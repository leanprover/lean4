// Lean compiler output
// Module: Lean.Elab.Tactic.Simpa
// Imports: public import Lean.Meta.Tactic.TryThis public import Lean.Elab.Tactic.Simp public import Lean.Elab.App
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_string_object l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unnecessarySimpa"};
static const lean_object* l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(182, 23, 154, 96, 189, 166, 9, 1)}};
static const lean_object* l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_string_object l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "enable the 'unnecessary simpa' linter"};
static const lean_object* l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value)}};
static const lean_object* l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_linter_unnecessarySimpa;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Type mismatch: After simplification, term"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0;
static lean_once_cell_t l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Try `simp at "};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` instead of `simpa using "};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Occurs check failed: Expression"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\ncontains the goal "};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__12_value),LEAN_SCALAR_PTR_LITERAL(38, 116, 214, 236, 212, 160, 188, 150)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "try 'simp' instead of 'simpa'"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "using"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticSimpa!_"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simpa!"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.Tactic.Simpa"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Elab.Tactic.Simpa.evalSimpa"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17;
static const lean_closure_object l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simpa"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 186, 141, 63, 66, 208, 56, 113)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8_value),LEAN_SCALAR_PTR_LITERAL(158, 198, 190, 154, 66, 126, 242, 208)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpaArgsRest"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6_value),LEAN_SCALAR_PTR_LITERAL(137, 133, 181, 17, 86, 74, 251, 208)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Simpa"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalSimpa"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 230, 37, 137, 25, 71, 189, 138)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 111, 162, 89, 60, 103, 42, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(90) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((lean_object*)(l_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_52_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v___x_50_, v___x_51_, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
return v_res_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object* v_o_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = l_linter_unnecessarySimpa;
v___x_57_ = l_Lean_Linter_getLinterValue(v___x_56_, v_o_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object* v_o_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_o_58_);
lean_dec_ref(v_o_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_box(0);
v___x_62_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___boxed(lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object* v_00_u03b1_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___boxed(lean_object* v_00_u03b1_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(v_00_u03b1_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0(lean_object* v_x_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; 
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
v___x_101_ = lean_apply_9(v_x_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, lean_box(0));
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0___boxed(lean_object* v_x_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0(v_x_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(lean_object* v_mvarId_113_, lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___f_124_; lean_object* v___x_125_; 
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
v___f_124_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_124_, 0, v_x_114_);
lean_closure_set(v___f_124_, 1, v___y_115_);
lean_closure_set(v___f_124_, 2, v___y_116_);
lean_closure_set(v___f_124_, 3, v___y_117_);
lean_closure_set(v___f_124_, 4, v___y_118_);
v___x_125_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_113_, v___f_124_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
if (lean_obj_tag(v___x_125_) == 0)
{
return v___x_125_;
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___boxed(lean_object* v_mvarId_134_, lean_object* v_x_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_mvarId_134_, v_x_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(lean_object* v_00_u03b1_146_, lean_object* v_mvarId_147_, lean_object* v_x_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_mvarId_147_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___boxed(lean_object* v_00_u03b1_159_, lean_object* v_mvarId_160_, lean_object* v_x_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(v_00_u03b1_159_, v_mvarId_160_, v_x_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_171_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(32u);
v___x_173_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_175_ = ((size_t)5ULL);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_unsigned_to_nat(32u);
v___x_178_ = lean_mk_empty_array_with_capacity(v___x_177_);
v___x_179_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0);
v___x_180_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_176_);
lean_ctor_set(v___x_180_, 3, v___x_176_);
lean_ctor_set_usize(v___x_180_, 4, v___x_175_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; lean_object* v_infoState_184_; lean_object* v_trees_185_; lean_object* v___x_186_; lean_object* v_infoState_187_; lean_object* v_env_188_; lean_object* v_nextMacroScope_189_; lean_object* v_ngen_190_; lean_object* v_auxDeclNGen_191_; lean_object* v_traceState_192_; lean_object* v_cache_193_; lean_object* v_messages_194_; lean_object* v_snapshotTasks_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_216_; 
v___x_183_ = lean_st_ref_get(v___y_181_);
v_infoState_184_ = lean_ctor_get(v___x_183_, 7);
lean_inc_ref(v_infoState_184_);
lean_dec(v___x_183_);
v_trees_185_ = lean_ctor_get(v_infoState_184_, 2);
lean_inc_ref(v_trees_185_);
lean_dec_ref(v_infoState_184_);
v___x_186_ = lean_st_ref_take(v___y_181_);
v_infoState_187_ = lean_ctor_get(v___x_186_, 7);
v_env_188_ = lean_ctor_get(v___x_186_, 0);
v_nextMacroScope_189_ = lean_ctor_get(v___x_186_, 1);
v_ngen_190_ = lean_ctor_get(v___x_186_, 2);
v_auxDeclNGen_191_ = lean_ctor_get(v___x_186_, 3);
v_traceState_192_ = lean_ctor_get(v___x_186_, 4);
v_cache_193_ = lean_ctor_get(v___x_186_, 5);
v_messages_194_ = lean_ctor_get(v___x_186_, 6);
v_snapshotTasks_195_ = lean_ctor_get(v___x_186_, 8);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_216_ == 0)
{
v___x_197_ = v___x_186_;
v_isShared_198_ = v_isSharedCheck_216_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_snapshotTasks_195_);
lean_inc(v_infoState_187_);
lean_inc(v_messages_194_);
lean_inc(v_cache_193_);
lean_inc(v_traceState_192_);
lean_inc(v_auxDeclNGen_191_);
lean_inc(v_ngen_190_);
lean_inc(v_nextMacroScope_189_);
lean_inc(v_env_188_);
lean_dec(v___x_186_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_216_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
uint8_t v_enabled_199_; lean_object* v_assignment_200_; lean_object* v_lazyAssignment_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_214_; 
v_enabled_199_ = lean_ctor_get_uint8(v_infoState_187_, sizeof(void*)*3);
v_assignment_200_ = lean_ctor_get(v_infoState_187_, 0);
v_lazyAssignment_201_ = lean_ctor_get(v_infoState_187_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_infoState_187_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_infoState_187_, 2);
lean_dec(v_unused_215_);
v___x_203_ = v_infoState_187_;
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_lazyAssignment_201_);
lean_inc(v_assignment_200_);
lean_dec(v_infoState_187_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 2, v___x_205_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_assignment_200_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_lazyAssignment_201_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v___x_205_);
lean_ctor_set_uint8(v_reuseFailAlloc_213_, sizeof(void*)*3, v_enabled_199_);
v___x_207_ = v_reuseFailAlloc_213_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_209_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 7, v___x_207_);
v___x_209_ = v___x_197_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_env_188_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_nextMacroScope_189_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_ngen_190_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_auxDeclNGen_191_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_traceState_192_);
lean_ctor_set(v_reuseFailAlloc_212_, 5, v_cache_193_);
lean_ctor_set(v_reuseFailAlloc_212_, 6, v_messages_194_);
lean_ctor_set(v_reuseFailAlloc_212_, 7, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_212_, 8, v_snapshotTasks_195_);
v___x_209_ = v_reuseFailAlloc_212_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_st_ref_set(v___y_181_, v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v_trees_185_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___boxed(lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_217_);
lean_dec(v___y_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7(lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___boxed(lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7(v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___f_251_; lean_object* v___x_66427__overap_252_; lean_object* v___x_253_; 
v___f_251_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___closed__0));
v___x_66427__overap_252_ = lean_panic_fn_borrowed(v___f_251_, v_msg_241_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
v___x_253_ = lean_apply_9(v___x_66427__overap_252_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___boxed(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_264_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(lean_object* v_opts_265_, lean_object* v_opt_266_){
_start:
{
lean_object* v_name_267_; lean_object* v_defValue_268_; lean_object* v_map_269_; lean_object* v___x_270_; 
v_name_267_ = lean_ctor_get(v_opt_266_, 0);
v_defValue_268_ = lean_ctor_get(v_opt_266_, 1);
v_map_269_ = lean_ctor_get(v_opts_265_, 0);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_269_, v_name_267_);
if (lean_obj_tag(v___x_270_) == 0)
{
uint8_t v___x_271_; 
v___x_271_ = lean_unbox(v_defValue_268_);
return v___x_271_;
}
else
{
lean_object* v_val_272_; 
v_val_272_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_val_272_);
lean_dec_ref(v___x_270_);
if (lean_obj_tag(v_val_272_) == 1)
{
uint8_t v_v_273_; 
v_v_273_ = lean_ctor_get_uint8(v_val_272_, 0);
lean_dec_ref(v_val_272_);
return v_v_273_;
}
else
{
uint8_t v___x_274_; 
lean_dec(v_val_272_);
v___x_274_ = lean_unbox(v_defValue_268_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10___boxed(lean_object* v_opts_275_, lean_object* v_opt_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_opts_275_, v_opt_276_);
lean_dec_ref(v_opt_276_);
lean_dec_ref(v_opts_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_ref_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_ref_288_ = lean_ctor_get(v___y_285_, 5);
v___x_289_ = 0;
v___x_290_ = l_Lean_SourceInfo_fromRef(v_ref_288_, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object* v_a_302_, lean_object* v_trees_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
v___x_313_ = lean_apply_9(v_a_302_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, lean_box(0));
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_318_, 0, v_a_314_);
lean_ctor_set(v___x_318_, 1, v_trees_303_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_318_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec_ref(v_trees_303_);
v_a_323_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_313_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_313_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object* v_a_331_, lean_object* v_trees_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(v_a_331_, v_trees_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object* v_a_349_, lean_object* v_a_350_, uint8_t v___x_351_, uint8_t v___x_352_, uint8_t v___x_353_, lean_object* v_a_354_, lean_object* v_mvarCounter_355_, lean_object* v___x_356_, lean_object* v___x_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
lean_inc(v_a_349_);
v___x_367_ = l_Lean_MVarId_getType(v_a_349_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_n(v_a_368_, 2);
lean_dec_ref(v___x_367_);
v___x_369_ = lean_mk_syntax_ident(v_a_350_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_a_368_);
v___x_371_ = l_Lean_Elab_Term_elabTerm(v___x_369_, v___x_370_, v___x_351_, v___x_351_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_406_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
v___x_406_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_352_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_483_; 
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v___x_406_, 0);
lean_dec(v_unused_484_);
v___x_408_ = v___x_406_;
v_isShared_409_ = v_isSharedCheck_483_;
goto v_resetjp_407_;
}
else
{
lean_dec(v___x_406_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_483_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; 
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
lean_inc(v_a_372_);
v___x_410_ = lean_infer_type(v_a_372_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; uint8_t v_a_413_; lean_object* v___x_423_; uint8_t v_foApprox_424_; uint8_t v_ctxApprox_425_; uint8_t v_quasiPatternApprox_426_; uint8_t v_constApprox_427_; uint8_t v_isDefEqStuckEx_428_; uint8_t v_unificationHints_429_; uint8_t v_proofIrrelevance_430_; uint8_t v_offsetCnstrs_431_; uint8_t v_transparency_432_; uint8_t v_etaStruct_433_; uint8_t v_univApprox_434_; uint8_t v_iota_435_; uint8_t v_beta_436_; uint8_t v_proj_437_; uint8_t v_zeta_438_; uint8_t v_zetaDelta_439_; uint8_t v_zetaUnused_440_; uint8_t v_zetaHave_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_474_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref(v___x_410_);
v___x_423_ = l_Lean_Meta_Context_config(v___y_362_);
v_foApprox_424_ = lean_ctor_get_uint8(v___x_423_, 0);
v_ctxApprox_425_ = lean_ctor_get_uint8(v___x_423_, 1);
v_quasiPatternApprox_426_ = lean_ctor_get_uint8(v___x_423_, 2);
v_constApprox_427_ = lean_ctor_get_uint8(v___x_423_, 3);
v_isDefEqStuckEx_428_ = lean_ctor_get_uint8(v___x_423_, 4);
v_unificationHints_429_ = lean_ctor_get_uint8(v___x_423_, 5);
v_proofIrrelevance_430_ = lean_ctor_get_uint8(v___x_423_, 6);
v_offsetCnstrs_431_ = lean_ctor_get_uint8(v___x_423_, 8);
v_transparency_432_ = lean_ctor_get_uint8(v___x_423_, 9);
v_etaStruct_433_ = lean_ctor_get_uint8(v___x_423_, 10);
v_univApprox_434_ = lean_ctor_get_uint8(v___x_423_, 11);
v_iota_435_ = lean_ctor_get_uint8(v___x_423_, 12);
v_beta_436_ = lean_ctor_get_uint8(v___x_423_, 13);
v_proj_437_ = lean_ctor_get_uint8(v___x_423_, 14);
v_zeta_438_ = lean_ctor_get_uint8(v___x_423_, 15);
v_zetaDelta_439_ = lean_ctor_get_uint8(v___x_423_, 16);
v_zetaUnused_440_ = lean_ctor_get_uint8(v___x_423_, 17);
v_zetaHave_441_ = lean_ctor_get_uint8(v___x_423_, 18);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_474_ == 0)
{
v___x_443_ = v___x_423_;
v_isShared_444_ = v_isSharedCheck_474_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_423_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_474_;
goto v_resetjp_442_;
}
v___jp_412_:
{
if (v_a_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_414_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1);
lean_inc_ref(v_a_354_);
v___x_415_ = l_Lean_indentExpr(v_a_354_);
v___x_416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v___x_417_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
if (v_isShared_409_ == 0)
{
lean_ctor_set_tag(v___x_408_, 1);
lean_ctor_set(v___x_408_, 0, v___x_418_);
v___x_420_ = v___x_408_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_422_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; 
lean_inc(v_a_372_);
v___x_421_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_420_, v_a_368_, v_a_411_, v_a_372_, v___x_357_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec_ref(v___x_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_dec_ref(v___x_421_);
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
v___y_378_ = v___y_362_;
v___y_379_ = v___y_363_;
v___y_380_ = v___y_364_;
v___y_381_ = v___y_365_;
goto v___jp_373_;
}
else
{
lean_dec(v_a_372_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_349_);
return v___x_421_;
}
}
}
else
{
lean_dec(v_a_411_);
lean_del_object(v___x_408_);
lean_dec(v_a_368_);
lean_dec(v___x_357_);
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
v___y_378_ = v___y_362_;
v___y_379_ = v___y_363_;
v___y_380_ = v___y_364_;
v___y_381_ = v___y_365_;
goto v___jp_373_;
}
}
v_resetjp_442_:
{
uint8_t v_trackZetaDelta_445_; lean_object* v_zetaDeltaSet_446_; lean_object* v_lctx_447_; lean_object* v_localInstances_448_; lean_object* v_defEqCtx_x3f_449_; lean_object* v_synthPendingDepth_450_; lean_object* v_canUnfold_x3f_451_; uint8_t v_univApprox_452_; uint8_t v_inTypeClassResolution_453_; uint8_t v_cacheInferType_454_; lean_object* v___x_456_; 
v_trackZetaDelta_445_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*7);
v_zetaDeltaSet_446_ = lean_ctor_get(v___y_362_, 1);
v_lctx_447_ = lean_ctor_get(v___y_362_, 2);
v_localInstances_448_ = lean_ctor_get(v___y_362_, 3);
v_defEqCtx_x3f_449_ = lean_ctor_get(v___y_362_, 4);
v_synthPendingDepth_450_ = lean_ctor_get(v___y_362_, 5);
v_canUnfold_x3f_451_ = lean_ctor_get(v___y_362_, 6);
v_univApprox_452_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_453_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*7 + 2);
v_cacheInferType_454_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*7 + 3);
if (v_isShared_444_ == 0)
{
v___x_456_ = v___x_443_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 0, v_foApprox_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 1, v_ctxApprox_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 2, v_quasiPatternApprox_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 3, v_constApprox_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 4, v_isDefEqStuckEx_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 5, v_unificationHints_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 6, v_proofIrrelevance_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 8, v_offsetCnstrs_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 9, v_transparency_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 10, v_etaStruct_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 11, v_univApprox_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 12, v_iota_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 13, v_beta_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 14, v_proj_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 15, v_zeta_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 16, v_zetaDelta_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 17, v_zetaUnused_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, 18, v_zetaHave_441_);
v___x_456_ = v_reuseFailAlloc_473_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
uint64_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_ctor_set_uint8(v___x_456_, 7, v___x_353_);
v___x_457_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set_uint64(v___x_458_, sizeof(void*)*1, v___x_457_);
lean_inc(v_canUnfold_x3f_451_);
lean_inc(v_synthPendingDepth_450_);
lean_inc(v_defEqCtx_x3f_449_);
lean_inc_ref(v_localInstances_448_);
lean_inc_ref(v_lctx_447_);
lean_inc(v_zetaDeltaSet_446_);
v___x_459_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v_zetaDeltaSet_446_);
lean_ctor_set(v___x_459_, 2, v_lctx_447_);
lean_ctor_set(v___x_459_, 3, v_localInstances_448_);
lean_ctor_set(v___x_459_, 4, v_defEqCtx_x3f_449_);
lean_ctor_set(v___x_459_, 5, v_synthPendingDepth_450_);
lean_ctor_set(v___x_459_, 6, v_canUnfold_x3f_451_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7, v_trackZetaDelta_445_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7 + 1, v_univApprox_452_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7 + 2, v_inTypeClassResolution_453_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7 + 3, v_cacheInferType_454_);
lean_inc(v_a_411_);
lean_inc(v_a_368_);
v___x_460_ = l_Lean_Meta_isExprDefEq(v_a_368_, v_a_411_, v___x_459_, v___y_363_, v___y_364_, v___y_365_);
lean_dec_ref(v___x_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; uint8_t v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref(v___x_460_);
v___x_462_ = lean_unbox(v_a_461_);
lean_dec(v_a_461_);
v_a_413_ = v___x_462_;
goto v___jp_412_;
}
else
{
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_463_; uint8_t v___x_464_; 
v_a_463_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_460_);
v___x_464_ = lean_unbox(v_a_463_);
lean_dec(v_a_463_);
v_a_413_ = v___x_464_;
goto v___jp_412_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_a_411_);
lean_del_object(v___x_408_);
lean_dec(v_a_372_);
lean_dec(v_a_368_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___x_357_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_349_);
v_a_465_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_460_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_460_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
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
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_del_object(v___x_408_);
lean_dec(v_a_372_);
lean_dec(v_a_368_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___x_357_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_349_);
v_a_475_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_410_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_410_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
else
{
lean_dec(v_a_372_);
lean_dec(v_a_368_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___x_357_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_349_);
return v___x_406_;
}
v___jp_373_:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_getMVars(v_a_354_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v___x_382_);
v___x_384_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_383_, v_mvarCounter_355_, v___y_379_);
lean_dec(v_a_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_384_);
v___x_386_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_385_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v_a_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_387_; 
lean_dec_ref(v___x_386_);
v___x_387_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_349_, v___y_375_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref(v___x_387_);
v___x_388_ = l_Lean_Name_mkStr1(v___x_356_);
v___x_389_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_388_, v_a_372_, v___x_352_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v___x_389_;
}
else
{
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v_a_372_);
lean_dec_ref(v___x_356_);
return v___x_387_;
}
}
else
{
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v_a_372_);
lean_dec_ref(v___x_356_);
lean_dec(v_a_349_);
return v___x_386_;
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v_a_372_);
lean_dec_ref(v___x_356_);
lean_dec(v_a_349_);
v_a_390_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_384_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_384_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v_a_372_);
lean_dec_ref(v___x_356_);
lean_dec(v_a_349_);
v_a_398_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_382_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_382_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
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
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_a_368_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___x_357_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_349_);
v_a_485_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_371_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_371_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___x_357_);
lean_dec_ref(v___x_356_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_350_);
lean_dec(v_a_349_);
v_a_493_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_367_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_367_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object** _args){
lean_object* v_a_501_ = _args[0];
lean_object* v_a_502_ = _args[1];
lean_object* v___x_503_ = _args[2];
lean_object* v___x_504_ = _args[3];
lean_object* v___x_505_ = _args[4];
lean_object* v_a_506_ = _args[5];
lean_object* v_mvarCounter_507_ = _args[6];
lean_object* v___x_508_ = _args[7];
lean_object* v___x_509_ = _args[8];
lean_object* v___y_510_ = _args[9];
lean_object* v___y_511_ = _args[10];
lean_object* v___y_512_ = _args[11];
lean_object* v___y_513_ = _args[12];
lean_object* v___y_514_ = _args[13];
lean_object* v___y_515_ = _args[14];
lean_object* v___y_516_ = _args[15];
lean_object* v___y_517_ = _args[16];
lean_object* v___y_518_ = _args[17];
_start:
{
uint8_t v___x_78725__boxed_519_; uint8_t v___x_78726__boxed_520_; uint8_t v___x_78727__boxed_521_; lean_object* v_res_522_; 
v___x_78725__boxed_519_ = lean_unbox(v___x_503_);
v___x_78726__boxed_520_ = lean_unbox(v___x_504_);
v___x_78727__boxed_521_ = lean_unbox(v___x_505_);
v_res_522_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(v_a_501_, v_a_502_, v___x_78725__boxed_519_, v___x_78726__boxed_520_, v___x_78727__boxed_521_, v_a_506_, v_mvarCounter_507_, v___x_508_, v___x_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v_mvarCounter_507_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object* v_a_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v_infoState_534_; lean_object* v_env_535_; lean_object* v_nextMacroScope_536_; lean_object* v_ngen_537_; lean_object* v_auxDeclNGen_538_; lean_object* v_traceState_539_; lean_object* v_cache_540_; lean_object* v_messages_541_; lean_object* v_snapshotTasks_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_563_; 
v___x_533_ = lean_st_ref_take(v___y_531_);
v_infoState_534_ = lean_ctor_get(v___x_533_, 7);
v_env_535_ = lean_ctor_get(v___x_533_, 0);
v_nextMacroScope_536_ = lean_ctor_get(v___x_533_, 1);
v_ngen_537_ = lean_ctor_get(v___x_533_, 2);
v_auxDeclNGen_538_ = lean_ctor_get(v___x_533_, 3);
v_traceState_539_ = lean_ctor_get(v___x_533_, 4);
v_cache_540_ = lean_ctor_get(v___x_533_, 5);
v_messages_541_ = lean_ctor_get(v___x_533_, 6);
v_snapshotTasks_542_ = lean_ctor_get(v___x_533_, 8);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_563_ == 0)
{
v___x_544_ = v___x_533_;
v_isShared_545_ = v_isSharedCheck_563_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_snapshotTasks_542_);
lean_inc(v_infoState_534_);
lean_inc(v_messages_541_);
lean_inc(v_cache_540_);
lean_inc(v_traceState_539_);
lean_inc(v_auxDeclNGen_538_);
lean_inc(v_ngen_537_);
lean_inc(v_nextMacroScope_536_);
lean_inc(v_env_535_);
lean_dec(v___x_533_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_563_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
uint8_t v_enabled_546_; lean_object* v_assignment_547_; lean_object* v_lazyAssignment_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_561_; 
v_enabled_546_ = lean_ctor_get_uint8(v_infoState_534_, sizeof(void*)*3);
v_assignment_547_ = lean_ctor_get(v_infoState_534_, 0);
v_lazyAssignment_548_ = lean_ctor_get(v_infoState_534_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_infoState_534_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v_infoState_534_, 2);
lean_dec(v_unused_562_);
v___x_550_ = v_infoState_534_;
v_isShared_551_ = v_isSharedCheck_561_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_lazyAssignment_548_);
lean_inc(v_assignment_547_);
lean_dec(v_infoState_534_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_561_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 2, v_a_523_);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_assignment_547_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_lazyAssignment_548_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_a_523_);
lean_ctor_set_uint8(v_reuseFailAlloc_560_, sizeof(void*)*3, v_enabled_546_);
v___x_553_ = v_reuseFailAlloc_560_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 7, v___x_553_);
v___x_555_ = v___x_544_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_env_535_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_nextMacroScope_536_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_ngen_537_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_auxDeclNGen_538_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_traceState_539_);
lean_ctor_set(v_reuseFailAlloc_559_, 5, v_cache_540_);
lean_ctor_set(v_reuseFailAlloc_559_, 6, v_messages_541_);
lean_ctor_set(v_reuseFailAlloc_559_, 7, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_559_, 8, v_snapshotTasks_542_);
v___x_555_ = v_reuseFailAlloc_559_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_st_ref_set(v___y_531_, v___x_555_);
v___x_557_ = lean_box(0);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object* v_a_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(v_a_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(lean_object* v_msgData_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_env_582_; lean_object* v___x_583_; lean_object* v_mctx_584_; lean_object* v_lctx_585_; lean_object* v_options_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_581_ = lean_st_ref_get(v___y_579_);
v_env_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_env_582_);
lean_dec(v___x_581_);
v___x_583_ = lean_st_ref_get(v___y_577_);
v_mctx_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_mctx_584_);
lean_dec(v___x_583_);
v_lctx_585_ = lean_ctor_get(v___y_576_, 2);
v_options_586_ = lean_ctor_get(v___y_578_, 2);
lean_inc_ref(v_options_586_);
lean_inc_ref(v_lctx_585_);
v___x_587_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_587_, 0, v_env_582_);
lean_ctor_set(v___x_587_, 1, v_mctx_584_);
lean_ctor_set(v___x_587_, 2, v_lctx_585_);
lean_ctor_set(v___x_587_, 3, v_options_586_);
v___x_588_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_msgData_575_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10___boxed(lean_object* v_msgData_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v_msgData_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_ref_603_; lean_object* v___x_604_; lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v_ref_603_ = lean_ctor_get(v___y_600_, 5);
v___x_604_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_inc(v_ref_603_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_ref_603_);
lean_ctor_set(v___x_609_, 1, v_a_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 1);
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg___boxed(lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(lean_object* v_mvarId_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; lean_object* v_mctx_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_625_ = lean_st_ref_get(v___y_623_);
v_mctx_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc_ref(v_mctx_626_);
lean_dec(v___x_625_);
v___x_627_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_626_, v_mvarId_621_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___y_622_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object* v_mvarId_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec(v_mvarId_631_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_mvarId_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; lean_object* v_mctx_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_640_ = lean_st_ref_get(v___y_638_);
v_mctx_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc_ref(v_mctx_641_);
lean_dec(v___x_640_);
v___x_642_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_641_, v_mvarId_636_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___y_637_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_mvarId_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec(v_mvarId_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
return v_x_651_;
}
else
{
lean_object* v_key_653_; lean_object* v_value_654_; lean_object* v_tail_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_678_; 
v_key_653_ = lean_ctor_get(v_x_652_, 0);
v_value_654_ = lean_ctor_get(v_x_652_, 1);
v_tail_655_ = lean_ctor_get(v_x_652_, 2);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_678_ == 0)
{
v___x_657_ = v_x_652_;
v_isShared_658_ = v_isSharedCheck_678_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_tail_655_);
lean_inc(v_value_654_);
lean_inc(v_key_653_);
lean_dec(v_x_652_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_678_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; uint64_t v_fold_663_; uint64_t v___x_664_; uint64_t v___x_665_; uint64_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_659_ = lean_array_get_size(v_x_651_);
v___x_660_ = l_Lean_Expr_hash(v_key_653_);
v___x_661_ = 32ULL;
v___x_662_ = lean_uint64_shift_right(v___x_660_, v___x_661_);
v_fold_663_ = lean_uint64_xor(v___x_660_, v___x_662_);
v___x_664_ = 16ULL;
v___x_665_ = lean_uint64_shift_right(v_fold_663_, v___x_664_);
v___x_666_ = lean_uint64_xor(v_fold_663_, v___x_665_);
v___x_667_ = lean_uint64_to_usize(v___x_666_);
v___x_668_ = lean_usize_of_nat(v___x_659_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_sub(v___x_668_, v___x_669_);
v___x_671_ = lean_usize_land(v___x_667_, v___x_670_);
v___x_672_ = lean_array_uget_borrowed(v_x_651_, v___x_671_);
lean_inc(v___x_672_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 2, v___x_672_);
v___x_674_ = v___x_657_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_key_653_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_value_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v___x_672_);
v___x_674_ = v_reuseFailAlloc_677_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_array_uset(v_x_651_, v___x_671_, v___x_674_);
v_x_651_ = v___x_675_;
v_x_652_ = v_tail_655_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object* v_i_679_, lean_object* v_source_680_, lean_object* v_target_681_){
_start:
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_array_get_size(v_source_680_);
v___x_683_ = lean_nat_dec_lt(v_i_679_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec_ref(v_source_680_);
lean_dec(v_i_679_);
return v_target_681_;
}
else
{
lean_object* v_es_684_; lean_object* v___x_685_; lean_object* v_source_686_; lean_object* v_target_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_es_684_ = lean_array_fget(v_source_680_, v_i_679_);
v___x_685_ = lean_box(0);
v_source_686_ = lean_array_fset(v_source_680_, v_i_679_, v___x_685_);
v_target_687_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_681_, v_es_684_);
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_add(v_i_679_, v___x_688_);
lean_dec(v_i_679_);
v_i_679_ = v___x_689_;
v_source_680_ = v_source_686_;
v_target_681_ = v_target_687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_data_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_nbuckets_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_692_ = lean_array_get_size(v_data_691_);
v___x_693_ = lean_unsigned_to_nat(2u);
v_nbuckets_694_ = lean_nat_mul(v___x_692_, v___x_693_);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_box(0);
v___x_697_ = lean_mk_array(v_nbuckets_694_, v___x_696_);
v___x_698_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_695_, v_data_691_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
else
{
lean_object* v_key_702_; lean_object* v_tail_703_; uint8_t v___x_704_; 
v_key_702_ = lean_ctor_get(v_x_700_, 0);
v_tail_703_ = lean_ctor_get(v_x_700_, 2);
v___x_704_ = lean_expr_eqv(v_key_702_, v_a_699_);
if (v___x_704_ == 0)
{
v_x_700_ = v_tail_703_;
goto _start;
}
else
{
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_a_706_, lean_object* v_x_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_706_, v_x_707_);
lean_dec(v_x_707_);
lean_dec_ref(v_a_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(lean_object* v_m_710_, lean_object* v_a_711_, lean_object* v_b_712_){
_start:
{
lean_object* v_size_713_; lean_object* v_buckets_714_; lean_object* v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; uint64_t v___x_718_; uint64_t v_fold_719_; uint64_t v___x_720_; uint64_t v___x_721_; uint64_t v___x_722_; size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v_bkt_728_; uint8_t v___x_729_; 
v_size_713_ = lean_ctor_get(v_m_710_, 0);
v_buckets_714_ = lean_ctor_get(v_m_710_, 1);
v___x_715_ = lean_array_get_size(v_buckets_714_);
v___x_716_ = l_Lean_Expr_hash(v_a_711_);
v___x_717_ = 32ULL;
v___x_718_ = lean_uint64_shift_right(v___x_716_, v___x_717_);
v_fold_719_ = lean_uint64_xor(v___x_716_, v___x_718_);
v___x_720_ = 16ULL;
v___x_721_ = lean_uint64_shift_right(v_fold_719_, v___x_720_);
v___x_722_ = lean_uint64_xor(v_fold_719_, v___x_721_);
v___x_723_ = lean_uint64_to_usize(v___x_722_);
v___x_724_ = lean_usize_of_nat(v___x_715_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_sub(v___x_724_, v___x_725_);
v___x_727_ = lean_usize_land(v___x_723_, v___x_726_);
v_bkt_728_ = lean_array_uget_borrowed(v_buckets_714_, v___x_727_);
v___x_729_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_711_, v_bkt_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_750_; 
lean_inc_ref(v_buckets_714_);
lean_inc(v_size_713_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_m_710_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; 
v_unused_751_ = lean_ctor_get(v_m_710_, 1);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_m_710_, 0);
lean_dec(v_unused_752_);
v___x_731_ = v_m_710_;
v_isShared_732_ = v_isSharedCheck_750_;
goto v_resetjp_730_;
}
else
{
lean_dec(v_m_710_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_750_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v_size_x27_734_; lean_object* v___x_735_; lean_object* v_buckets_x27_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_733_ = lean_unsigned_to_nat(1u);
v_size_x27_734_ = lean_nat_add(v_size_713_, v___x_733_);
lean_dec(v_size_713_);
lean_inc(v_bkt_728_);
v___x_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_735_, 0, v_a_711_);
lean_ctor_set(v___x_735_, 1, v_b_712_);
lean_ctor_set(v___x_735_, 2, v_bkt_728_);
v_buckets_x27_736_ = lean_array_uset(v_buckets_714_, v___x_727_, v___x_735_);
v___x_737_ = lean_unsigned_to_nat(4u);
v___x_738_ = lean_nat_mul(v_size_x27_734_, v___x_737_);
v___x_739_ = lean_unsigned_to_nat(3u);
v___x_740_ = lean_nat_div(v___x_738_, v___x_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_array_get_size(v_buckets_x27_736_);
v___x_742_ = lean_nat_dec_le(v___x_740_, v___x_741_);
lean_dec(v___x_740_);
if (v___x_742_ == 0)
{
lean_object* v_val_743_; lean_object* v___x_745_; 
v_val_743_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_736_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_val_743_);
lean_ctor_set(v___x_731_, 0, v_size_x27_734_);
v___x_745_ = v___x_731_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_size_x27_734_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_val_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
else
{
lean_object* v___x_748_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_buckets_x27_736_);
lean_ctor_set(v___x_731_, 0, v_size_x27_734_);
v___x_748_ = v___x_731_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_size_x27_734_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_buckets_x27_736_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_dec(v_b_712_);
lean_dec_ref(v_a_711_);
return v_m_710_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(lean_object* v_m_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_buckets_755_; lean_object* v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; uint64_t v___x_759_; uint64_t v_fold_760_; uint64_t v___x_761_; uint64_t v___x_762_; uint64_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_buckets_755_ = lean_ctor_get(v_m_753_, 1);
v___x_756_ = lean_array_get_size(v_buckets_755_);
v___x_757_ = l_Lean_Expr_hash(v_a_754_);
v___x_758_ = 32ULL;
v___x_759_ = lean_uint64_shift_right(v___x_757_, v___x_758_);
v_fold_760_ = lean_uint64_xor(v___x_757_, v___x_759_);
v___x_761_ = 16ULL;
v___x_762_ = lean_uint64_shift_right(v_fold_760_, v___x_761_);
v___x_763_ = lean_uint64_xor(v_fold_760_, v___x_762_);
v___x_764_ = lean_uint64_to_usize(v___x_763_);
v___x_765_ = lean_usize_of_nat(v___x_756_);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_sub(v___x_765_, v___x_766_);
v___x_768_ = lean_usize_land(v___x_764_, v___x_767_);
v___x_769_ = lean_array_uget_borrowed(v_buckets_755_, v___x_768_);
v___x_770_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_754_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_771_, lean_object* v_a_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_m_771_, v_a_772_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v_m_771_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object* v_mvarId_779_, lean_object* v_e_780_, lean_object* v_a_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_d_792_; lean_object* v_b_793_; lean_object* v___y_794_; uint8_t v___x_800_; 
v___x_800_ = l_Lean_Expr_hasExprMVar(v_e_780_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v_e_780_);
v___x_801_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v_a_781_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_a_781_, v_e_780_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_box(0);
lean_inc_ref(v_e_780_);
v___x_806_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(v_a_781_, v_e_780_, v___x_805_);
switch(lean_obj_tag(v_e_780_))
{
case 11:
{
lean_object* v_struct_807_; 
v_struct_807_ = lean_ctor_get(v_e_780_, 2);
lean_inc_ref(v_struct_807_);
lean_dec_ref(v_e_780_);
v_e_780_ = v_struct_807_;
v_a_781_ = v___x_806_;
goto _start;
}
case 7:
{
lean_object* v_binderType_809_; lean_object* v_body_810_; 
v_binderType_809_ = lean_ctor_get(v_e_780_, 1);
lean_inc_ref(v_binderType_809_);
v_body_810_ = lean_ctor_get(v_e_780_, 2);
lean_inc_ref(v_body_810_);
lean_dec_ref(v_e_780_);
v_d_792_ = v_binderType_809_;
v_b_793_ = v_body_810_;
v___y_794_ = v___x_806_;
goto v___jp_791_;
}
case 6:
{
lean_object* v_binderType_811_; lean_object* v_body_812_; 
v_binderType_811_ = lean_ctor_get(v_e_780_, 1);
lean_inc_ref(v_binderType_811_);
v_body_812_ = lean_ctor_get(v_e_780_, 2);
lean_inc_ref(v_body_812_);
lean_dec_ref(v_e_780_);
v_d_792_ = v_binderType_811_;
v_b_793_ = v_body_812_;
v___y_794_ = v___x_806_;
goto v___jp_791_;
}
case 8:
{
lean_object* v_type_813_; lean_object* v_value_814_; lean_object* v_body_815_; lean_object* v___x_816_; 
v_type_813_ = lean_ctor_get(v_e_780_, 1);
lean_inc_ref(v_type_813_);
v_value_814_ = lean_ctor_get(v_e_780_, 2);
lean_inc_ref(v_value_814_);
v_body_815_ = lean_ctor_get(v_e_780_, 3);
lean_inc_ref(v_body_815_);
lean_dec_ref(v_e_780_);
v___x_816_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_779_, v_type_813_, v___x_806_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v_fst_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
v_fst_818_ = lean_ctor_get(v_a_817_, 0);
if (lean_obj_tag(v_fst_818_) == 0)
{
lean_dec(v_a_817_);
lean_dec_ref(v_body_815_);
lean_dec_ref(v_value_814_);
return v___x_816_;
}
else
{
lean_object* v_snd_819_; lean_object* v___x_820_; 
lean_dec_ref(v___x_816_);
v_snd_819_ = lean_ctor_get(v_a_817_, 1);
lean_inc(v_snd_819_);
lean_dec(v_a_817_);
v___x_820_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_779_, v_value_814_, v_snd_819_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v_fst_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
v_fst_822_ = lean_ctor_get(v_a_821_, 0);
if (lean_obj_tag(v_fst_822_) == 0)
{
lean_dec(v_a_821_);
lean_dec_ref(v_body_815_);
return v___x_820_;
}
else
{
lean_object* v_snd_823_; 
lean_dec_ref(v___x_820_);
v_snd_823_ = lean_ctor_get(v_a_821_, 1);
lean_inc(v_snd_823_);
lean_dec(v_a_821_);
v_e_780_ = v_body_815_;
v_a_781_ = v_snd_823_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_815_);
return v___x_820_;
}
}
}
else
{
lean_dec_ref(v_body_815_);
lean_dec_ref(v_value_814_);
return v___x_816_;
}
}
case 10:
{
lean_object* v_expr_825_; 
v_expr_825_ = lean_ctor_get(v_e_780_, 1);
lean_inc_ref(v_expr_825_);
lean_dec_ref(v_e_780_);
v_e_780_ = v_expr_825_;
v_a_781_ = v___x_806_;
goto _start;
}
case 5:
{
lean_object* v_fn_827_; lean_object* v_arg_828_; lean_object* v___x_829_; 
v_fn_827_ = lean_ctor_get(v_e_780_, 0);
lean_inc_ref(v_fn_827_);
v_arg_828_ = lean_ctor_get(v_e_780_, 1);
lean_inc_ref(v_arg_828_);
lean_dec_ref(v_e_780_);
v___x_829_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_779_, v_fn_827_, v___x_806_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v_fst_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
v_fst_831_ = lean_ctor_get(v_a_830_, 0);
if (lean_obj_tag(v_fst_831_) == 0)
{
lean_dec(v_a_830_);
lean_dec_ref(v_arg_828_);
return v___x_829_;
}
else
{
lean_object* v_snd_832_; 
lean_dec_ref(v___x_829_);
v_snd_832_ = lean_ctor_get(v_a_830_, 1);
lean_inc(v_snd_832_);
lean_dec(v_a_830_);
v_e_780_ = v_arg_828_;
v_a_781_ = v_snd_832_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_828_);
return v___x_829_;
}
}
case 2:
{
lean_object* v_mvarId_834_; lean_object* v___x_835_; 
v_mvarId_834_ = lean_ctor_get(v_e_780_, 0);
lean_inc(v_mvarId_834_);
lean_dec_ref(v_e_780_);
v___x_835_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(v_mvarId_779_, v_mvarId_834_, v___x_806_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
return v___x_835_;
}
default: 
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_e_780_);
v___x_836_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_806_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v_e_780_);
v___x_839_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v_a_781_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
v___jp_791_:
{
lean_object* v___x_795_; 
v___x_795_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_779_, v_d_792_, v___y_794_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v_fst_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
v_fst_797_ = lean_ctor_get(v_a_796_, 0);
if (lean_obj_tag(v_fst_797_) == 0)
{
lean_dec(v_a_796_);
lean_dec_ref(v_b_793_);
return v___x_795_;
}
else
{
lean_object* v_snd_798_; 
lean_dec_ref(v___x_795_);
v_snd_798_ = lean_ctor_get(v_a_796_, 1);
lean_inc(v_snd_798_);
lean_dec(v_a_796_);
v_e_780_ = v_b_793_;
v_a_781_ = v_snd_798_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_793_);
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(lean_object* v_mvarId_842_, lean_object* v_mvarId_x27_843_, lean_object* v_a_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_instBEqMVarId_beq(v_mvarId_842_, v_mvarId_x27_843_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_843_, v_a_844_, v___y_850_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_939_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_939_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_939_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_939_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_fst_860_; 
v_fst_860_ = lean_ctor_get(v_a_856_, 0);
lean_inc(v_fst_860_);
if (lean_obj_tag(v_fst_860_) == 0)
{
lean_object* v_snd_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_mvarId_x27_843_);
v_snd_861_ = lean_ctor_get(v_a_856_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_a_856_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v_a_856_, 0);
lean_dec(v_unused_880_);
v___x_863_ = v_a_856_;
v_isShared_864_ = v_isSharedCheck_879_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snd_861_);
lean_dec(v_a_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_879_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_878_; 
v_a_865_ = lean_ctor_get(v_fst_860_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v_fst_860_);
if (v_isSharedCheck_878_ == 0)
{
v___x_867_ = v_fst_860_;
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v_fst_860_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_877_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_870_);
v___x_872_ = v___x_863_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_snd_861_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_872_);
v___x_874_ = v___x_858_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
else
{
lean_object* v_a_881_; 
lean_del_object(v___x_858_);
v_a_881_ = lean_ctor_get(v_fst_860_, 0);
lean_inc(v_a_881_);
lean_dec_ref(v_fst_860_);
if (lean_obj_tag(v_a_881_) == 0)
{
lean_object* v_snd_882_; lean_object* v___x_883_; 
v_snd_882_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_882_);
lean_dec(v_a_856_);
v___x_883_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_843_, v_snd_882_, v___y_850_);
lean_dec(v_mvarId_x27_843_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_927_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_927_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_927_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_927_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_fst_888_; 
v_fst_888_ = lean_ctor_get(v_a_884_, 0);
lean_inc(v_fst_888_);
if (lean_obj_tag(v_fst_888_) == 0)
{
lean_object* v_snd_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_907_; 
v_snd_889_ = lean_ctor_get(v_a_884_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_884_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_a_884_, 0);
lean_dec(v_unused_908_);
v___x_891_ = v_a_884_;
v_isShared_892_ = v_isSharedCheck_907_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_snd_889_);
lean_dec(v_a_884_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_907_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_906_; 
v_a_893_ = lean_ctor_get(v_fst_888_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_fst_888_);
if (v_isSharedCheck_906_ == 0)
{
v___x_895_ = v_fst_888_;
v_isShared_896_ = v_isSharedCheck_906_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v_fst_888_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_906_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_905_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_898_);
v___x_900_ = v___x_891_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_snd_889_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_900_);
v___x_902_ = v___x_886_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
else
{
lean_object* v_a_909_; 
v_a_909_ = lean_ctor_get(v_fst_888_, 0);
lean_inc(v_a_909_);
lean_dec_ref(v_fst_888_);
if (lean_obj_tag(v_a_909_) == 0)
{
lean_object* v_snd_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_921_; 
v_snd_910_ = lean_ctor_get(v_a_884_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_884_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_a_884_, 0);
lean_dec(v_unused_922_);
v___x_912_ = v_a_884_;
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snd_910_);
lean_dec(v_a_884_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_910_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_916_);
v___x_918_ = v___x_886_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_val_923_; lean_object* v_snd_924_; lean_object* v_mvarIdPending_925_; 
lean_del_object(v___x_886_);
v_val_923_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_val_923_);
lean_dec_ref(v_a_909_);
v_snd_924_ = lean_ctor_get(v_a_884_, 1);
lean_inc(v_snd_924_);
lean_dec(v_a_884_);
v_mvarIdPending_925_ = lean_ctor_get(v_val_923_, 1);
lean_inc(v_mvarIdPending_925_);
lean_dec(v_val_923_);
v_mvarId_x27_843_ = v_mvarIdPending_925_;
v_a_844_ = v_snd_924_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_883_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_883_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_snd_936_; lean_object* v_val_937_; lean_object* v___x_938_; 
lean_dec(v_mvarId_x27_843_);
v_snd_936_ = lean_ctor_get(v_a_856_, 1);
lean_inc(v_snd_936_);
lean_dec(v_a_856_);
v_val_937_ = lean_ctor_get(v_a_881_, 0);
lean_inc(v_val_937_);
lean_dec_ref(v_a_881_);
v___x_938_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_842_, v_val_937_, v_snd_936_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_mvarId_x27_843_);
v_a_940_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_855_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_855_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_mvarId_x27_843_);
v___x_948_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__1));
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_a_844_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_951_, lean_object* v_mvarId_x27_952_, lean_object* v_a_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(v_mvarId_951_, v_mvarId_x27_952_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v_mvarId_951_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object* v_mvarId_964_, lean_object* v_e_965_, lean_object* v_a_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_964_, v_e_965_, v_a_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v_mvarId_964_);
return v_res_976_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_box(0);
v___x_978_ = lean_unsigned_to_nat(16u);
v___x_979_ = lean_mk_array(v___x_978_, v___x_977_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object* v_mvarId_983_, lean_object* v_e_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_Expr_hasExprMVar(v_e_984_);
if (v___x_994_ == 0)
{
uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec_ref(v_e_984_);
v___x_995_ = 1;
v___x_996_ = lean_box(v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1);
v___x_999_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_983_, v_e_984_, v___x_998_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1014_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1014_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1014_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_fst_1004_; 
v_fst_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_fst_1004_);
lean_dec(v_a_1000_);
if (lean_obj_tag(v_fst_1004_) == 0)
{
uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_dec_ref(v_fst_1004_);
v___x_1005_ = 0;
v___x_1006_ = lean_box(v___x_1005_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1006_);
v___x_1008_ = v___x_1002_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
lean_dec_ref(v_fst_1004_);
v___x_1010_ = lean_box(v___x_994_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1010_);
v___x_1012_ = v___x_1002_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
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
v_a_1015_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_999_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_999_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object* v_mvarId_1023_, lean_object* v_e_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(v_mvarId_1023_, v_e_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v_mvarId_1023_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v_ks_1039_; lean_object* v_vs_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1064_; 
v_ks_1039_ = lean_ctor_get(v_x_1035_, 0);
v_vs_1040_ = lean_ctor_get(v_x_1035_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1035_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1042_ = v_x_1035_;
v_isShared_1043_ = v_isSharedCheck_1064_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_vs_1040_);
lean_inc(v_ks_1039_);
lean_dec(v_x_1035_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1064_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_array_get_size(v_ks_1039_);
v___x_1045_ = lean_nat_dec_lt(v_x_1036_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_dec(v_x_1036_);
v___x_1046_ = lean_array_push(v_ks_1039_, v_x_1037_);
v___x_1047_ = lean_array_push(v_vs_1040_, v_x_1038_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1047_);
lean_ctor_set(v___x_1042_, 0, v___x_1046_);
v___x_1049_ = v___x_1042_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
else
{
lean_object* v_k_x27_1051_; uint8_t v___x_1052_; 
v_k_x27_1051_ = lean_array_fget_borrowed(v_ks_1039_, v_x_1036_);
v___x_1052_ = l_Lean_instBEqMVarId_beq(v_x_1037_, v_k_x27_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1054_; 
if (v_isShared_1043_ == 0)
{
v___x_1054_ = v___x_1042_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_ks_1039_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_vs_1040_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_x_1036_, v___x_1055_);
lean_dec(v_x_1036_);
v_x_1035_ = v___x_1054_;
v_x_1036_ = v___x_1056_;
goto _start;
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1059_ = lean_array_fset(v_ks_1039_, v_x_1036_, v_x_1037_);
v___x_1060_ = lean_array_fset(v_vs_1040_, v_x_1036_, v_x_1038_);
lean_dec(v_x_1036_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1060_);
lean_ctor_set(v___x_1042_, 0, v___x_1059_);
v___x_1062_ = v___x_1042_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1065_, lean_object* v_k_1066_, lean_object* v_v_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1065_, v___x_1068_, v_k_1066_, v_v_1067_);
return v___x_1069_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; 
v___x_1070_ = ((size_t)5ULL);
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_shift_left(v___x_1071_, v___x_1070_);
return v___x_1072_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; 
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1075_ = lean_usize_sub(v___x_1074_, v___x_1073_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(lean_object* v_x_1077_, size_t v_x_1078_, size_t v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 0)
{
lean_object* v_es_1082_; size_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; lean_object* v_j_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_es_1082_ = lean_ctor_get(v_x_1077_, 0);
v___x_1083_ = ((size_t)5ULL);
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1);
v___x_1086_ = lean_usize_land(v_x_1078_, v___x_1085_);
v_j_1087_ = lean_usize_to_nat(v___x_1086_);
v___x_1088_ = lean_array_get_size(v_es_1082_);
v___x_1089_ = lean_nat_dec_lt(v_j_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_dec(v_j_1087_);
lean_dec(v_x_1081_);
lean_dec(v_x_1080_);
return v_x_1077_;
}
else
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1126_; 
lean_inc_ref(v_es_1082_);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_x_1077_, 0);
lean_dec(v_unused_1127_);
v___x_1091_ = v_x_1077_;
v_isShared_1092_ = v_isSharedCheck_1126_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v_x_1077_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1126_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_v_1093_; lean_object* v___x_1094_; lean_object* v_xs_x27_1095_; lean_object* v___y_1097_; 
v_v_1093_ = lean_array_fget(v_es_1082_, v_j_1087_);
v___x_1094_ = lean_box(0);
v_xs_x27_1095_ = lean_array_fset(v_es_1082_, v_j_1087_, v___x_1094_);
switch(lean_obj_tag(v_v_1093_))
{
case 0:
{
lean_object* v_key_1102_; lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
v_key_1102_ = lean_ctor_get(v_v_1093_, 0);
v_val_1103_ = lean_ctor_get(v_v_1093_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_v_1093_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1105_ = v_v_1093_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_inc(v_key_1102_);
lean_dec(v_v_1093_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Lean_instBEqMVarId_beq(v_x_1080_, v_key_1102_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_del_object(v___x_1105_);
v___x_1108_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1102_, v_val_1103_, v_x_1080_, v_x_1081_);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
v___y_1097_ = v___x_1109_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1111_; 
lean_dec(v_val_1103_);
lean_dec(v_key_1102_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v_x_1081_);
lean_ctor_set(v___x_1105_, 0, v_x_1080_);
v___x_1111_ = v___x_1105_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_x_1080_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_x_1081_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
v___y_1097_ = v___x_1111_;
goto v___jp_1096_;
}
}
}
}
case 1:
{
lean_object* v_node_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1124_; 
v_node_1114_ = lean_ctor_get(v_v_1093_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_v_1093_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1116_ = v_v_1093_;
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_node_1114_);
lean_dec(v_v_1093_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1124_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1118_ = lean_usize_shift_right(v_x_1078_, v___x_1083_);
v___x_1119_ = lean_usize_add(v_x_1079_, v___x_1084_);
v___x_1120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_node_1114_, v___x_1118_, v___x_1119_, v_x_1080_, v_x_1081_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1120_);
v___x_1122_ = v___x_1116_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
v___y_1097_ = v___x_1122_;
goto v___jp_1096_;
}
}
}
default: 
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_x_1080_);
lean_ctor_set(v___x_1125_, 1, v_x_1081_);
v___y_1097_ = v___x_1125_;
goto v___jp_1096_;
}
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_array_fset(v_xs_x27_1095_, v_j_1087_, v___y_1097_);
lean_dec(v_j_1087_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1098_);
v___x_1100_ = v___x_1091_;
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
lean_object* v_ks_1128_; lean_object* v_vs_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1149_; 
v_ks_1128_ = lean_ctor_get(v_x_1077_, 0);
v_vs_1129_ = lean_ctor_get(v_x_1077_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1131_ = v_x_1077_;
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_vs_1129_);
lean_inc(v_ks_1128_);
lean_dec(v_x_1077_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_ks_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_vs_1129_);
v___x_1134_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v_newNode_1135_; uint8_t v___y_1137_; size_t v___x_1143_; uint8_t v___x_1144_; 
v_newNode_1135_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1134_, v_x_1080_, v_x_1081_);
v___x_1143_ = ((size_t)7ULL);
v___x_1144_ = lean_usize_dec_le(v___x_1143_, v_x_1079_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1135_);
v___x_1146_ = lean_unsigned_to_nat(4u);
v___x_1147_ = lean_nat_dec_lt(v___x_1145_, v___x_1146_);
lean_dec(v___x_1145_);
v___y_1137_ = v___x_1147_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v___x_1144_;
goto v___jp_1136_;
}
v___jp_1136_:
{
if (v___y_1137_ == 0)
{
lean_object* v_ks_1138_; lean_object* v_vs_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_ks_1138_ = lean_ctor_get(v_newNode_1135_, 0);
lean_inc_ref(v_ks_1138_);
v_vs_1139_ = lean_ctor_get(v_newNode_1135_, 1);
lean_inc_ref(v_vs_1139_);
lean_dec_ref(v_newNode_1135_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2);
v___x_1142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1079_, v_ks_1138_, v_vs_1139_, v___x_1140_, v___x_1141_);
lean_dec_ref(v_vs_1139_);
lean_dec_ref(v_ks_1138_);
return v___x_1142_;
}
else
{
return v_newNode_1135_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1150_, lean_object* v_keys_1151_, lean_object* v_vals_1152_, lean_object* v_i_1153_, lean_object* v_entries_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_array_get_size(v_keys_1151_);
v___x_1156_ = lean_nat_dec_lt(v_i_1153_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec(v_i_1153_);
return v_entries_1154_;
}
else
{
lean_object* v_k_1157_; lean_object* v_v_1158_; uint64_t v___x_1159_; size_t v_h_1160_; size_t v___x_1161_; lean_object* v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; size_t v_h_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_k_1157_ = lean_array_fget_borrowed(v_keys_1151_, v_i_1153_);
v_v_1158_ = lean_array_fget_borrowed(v_vals_1152_, v_i_1153_);
v___x_1159_ = l_Lean_instHashableMVarId_hash(v_k_1157_);
v_h_1160_ = lean_uint64_to_usize(v___x_1159_);
v___x_1161_ = ((size_t)5ULL);
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = ((size_t)1ULL);
v___x_1164_ = lean_usize_sub(v_depth_1150_, v___x_1163_);
v___x_1165_ = lean_usize_mul(v___x_1161_, v___x_1164_);
v_h_1166_ = lean_usize_shift_right(v_h_1160_, v___x_1165_);
v___x_1167_ = lean_nat_add(v_i_1153_, v___x_1162_);
lean_dec(v_i_1153_);
lean_inc(v_v_1158_);
lean_inc(v_k_1157_);
v___x_1168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_entries_1154_, v_h_1166_, v_depth_1150_, v_k_1157_, v_v_1158_);
v_i_1153_ = v___x_1167_;
v_entries_1154_ = v___x_1168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1170_, lean_object* v_keys_1171_, lean_object* v_vals_1172_, lean_object* v_i_1173_, lean_object* v_entries_1174_){
_start:
{
size_t v_depth_boxed_1175_; lean_object* v_res_1176_; 
v_depth_boxed_1175_ = lean_unbox_usize(v_depth_1170_);
lean_dec(v_depth_1170_);
v_res_1176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1175_, v_keys_1171_, v_vals_1172_, v_i_1173_, v_entries_1174_);
lean_dec_ref(v_vals_1172_);
lean_dec_ref(v_keys_1171_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
size_t v_x_79947__boxed_1182_; size_t v_x_79948__boxed_1183_; lean_object* v_res_1184_; 
v_x_79947__boxed_1182_ = lean_unbox_usize(v_x_1178_);
lean_dec(v_x_1178_);
v_x_79948__boxed_1183_ = lean_unbox_usize(v_x_1179_);
lean_dec(v_x_1179_);
v_res_1184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_1177_, v_x_79947__boxed_1182_, v_x_79948__boxed_1183_, v_x_1180_, v_x_1181_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(lean_object* v_x_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_){
_start:
{
uint64_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = l_Lean_instHashableMVarId_hash(v_x_1186_);
v___x_1189_ = lean_uint64_to_usize(v___x_1188_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_1185_, v___x_1189_, v___x_1190_, v_x_1186_, v_x_1187_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(lean_object* v_mvarId_1192_, lean_object* v_val_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v_mctx_1197_; lean_object* v_cache_1198_; lean_object* v_zetaDeltaFVarIds_1199_; lean_object* v_postponed_1200_; lean_object* v_diag_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1229_; 
v___x_1196_ = lean_st_ref_take(v___y_1194_);
v_mctx_1197_ = lean_ctor_get(v___x_1196_, 0);
v_cache_1198_ = lean_ctor_get(v___x_1196_, 1);
v_zetaDeltaFVarIds_1199_ = lean_ctor_get(v___x_1196_, 2);
v_postponed_1200_ = lean_ctor_get(v___x_1196_, 3);
v_diag_1201_ = lean_ctor_get(v___x_1196_, 4);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1203_ = v___x_1196_;
v_isShared_1204_ = v_isSharedCheck_1229_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_diag_1201_);
lean_inc(v_postponed_1200_);
lean_inc(v_zetaDeltaFVarIds_1199_);
lean_inc(v_cache_1198_);
lean_inc(v_mctx_1197_);
lean_dec(v___x_1196_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1229_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_depth_1205_; lean_object* v_levelAssignDepth_1206_; lean_object* v_lmvarCounter_1207_; lean_object* v_mvarCounter_1208_; lean_object* v_lDecls_1209_; lean_object* v_decls_1210_; lean_object* v_userNames_1211_; lean_object* v_lAssignment_1212_; lean_object* v_eAssignment_1213_; lean_object* v_dAssignment_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1228_; 
v_depth_1205_ = lean_ctor_get(v_mctx_1197_, 0);
v_levelAssignDepth_1206_ = lean_ctor_get(v_mctx_1197_, 1);
v_lmvarCounter_1207_ = lean_ctor_get(v_mctx_1197_, 2);
v_mvarCounter_1208_ = lean_ctor_get(v_mctx_1197_, 3);
v_lDecls_1209_ = lean_ctor_get(v_mctx_1197_, 4);
v_decls_1210_ = lean_ctor_get(v_mctx_1197_, 5);
v_userNames_1211_ = lean_ctor_get(v_mctx_1197_, 6);
v_lAssignment_1212_ = lean_ctor_get(v_mctx_1197_, 7);
v_eAssignment_1213_ = lean_ctor_get(v_mctx_1197_, 8);
v_dAssignment_1214_ = lean_ctor_get(v_mctx_1197_, 9);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_mctx_1197_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1216_ = v_mctx_1197_;
v_isShared_1217_ = v_isSharedCheck_1228_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_dAssignment_1214_);
lean_inc(v_eAssignment_1213_);
lean_inc(v_lAssignment_1212_);
lean_inc(v_userNames_1211_);
lean_inc(v_decls_1210_);
lean_inc(v_lDecls_1209_);
lean_inc(v_mvarCounter_1208_);
lean_inc(v_lmvarCounter_1207_);
lean_inc(v_levelAssignDepth_1206_);
lean_inc(v_depth_1205_);
lean_dec(v_mctx_1197_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1228_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_eAssignment_1213_, v_mvarId_1192_, v_val_1193_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 8, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_depth_1205_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_levelAssignDepth_1206_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_lmvarCounter_1207_);
lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_mvarCounter_1208_);
lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_lDecls_1209_);
lean_ctor_set(v_reuseFailAlloc_1227_, 5, v_decls_1210_);
lean_ctor_set(v_reuseFailAlloc_1227_, 6, v_userNames_1211_);
lean_ctor_set(v_reuseFailAlloc_1227_, 7, v_lAssignment_1212_);
lean_ctor_set(v_reuseFailAlloc_1227_, 8, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1227_, 9, v_dAssignment_1214_);
v___x_1220_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1220_);
v___x_1222_ = v___x_1203_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_cache_1198_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_zetaDeltaFVarIds_1199_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_postponed_1200_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_diag_1201_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_st_ref_set(v___y_1194_, v___x_1222_);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg___boxed(lean_object* v_mvarId_1230_, lean_object* v_val_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_1230_, v_val_1231_, v___y_1232_);
lean_dec(v___y_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1243_, uint8_t v_suppressElabErrors_1244_, lean_object* v_x_1245_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 1)
{
lean_object* v_pre_1246_; 
v_pre_1246_ = lean_ctor_get(v_x_1245_, 0);
switch(lean_obj_tag(v_pre_1246_))
{
case 1:
{
lean_object* v_pre_1247_; 
v_pre_1247_ = lean_ctor_get(v_pre_1246_, 0);
switch(lean_obj_tag(v_pre_1247_))
{
case 0:
{
lean_object* v_str_1248_; lean_object* v_str_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_str_1248_ = lean_ctor_get(v_x_1245_, 1);
v_str_1249_ = lean_ctor_get(v_pre_1246_, 1);
v___x_1250_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1251_ = lean_string_dec_eq(v_str_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1253_ = lean_string_dec_eq(v_str_1249_, v___x_1252_);
if (v___x_1253_ == 0)
{
return v___y_1243_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1255_ = lean_string_dec_eq(v_str_1248_, v___x_1254_);
if (v___x_1255_ == 0)
{
return v___y_1243_;
}
else
{
return v_suppressElabErrors_1244_;
}
}
}
else
{
lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1256_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1257_ = lean_string_dec_eq(v_str_1248_, v___x_1256_);
if (v___x_1257_ == 0)
{
return v___y_1243_;
}
else
{
return v_suppressElabErrors_1244_;
}
}
}
case 1:
{
lean_object* v_pre_1258_; 
v_pre_1258_ = lean_ctor_get(v_pre_1247_, 0);
if (lean_obj_tag(v_pre_1258_) == 0)
{
lean_object* v_str_1259_; lean_object* v_str_1260_; lean_object* v_str_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_str_1259_ = lean_ctor_get(v_x_1245_, 1);
v_str_1260_ = lean_ctor_get(v_pre_1246_, 1);
v_str_1261_ = lean_ctor_get(v_pre_1247_, 1);
v___x_1262_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1263_ = lean_string_dec_eq(v_str_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
return v___y_1243_;
}
else
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1265_ = lean_string_dec_eq(v_str_1260_, v___x_1264_);
if (v___x_1265_ == 0)
{
return v___y_1243_;
}
else
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1267_ = lean_string_dec_eq(v_str_1259_, v___x_1266_);
if (v___x_1267_ == 0)
{
return v___y_1243_;
}
else
{
return v_suppressElabErrors_1244_;
}
}
}
}
else
{
return v___y_1243_;
}
}
default: 
{
return v___y_1243_;
}
}
}
case 0:
{
lean_object* v_str_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_str_1268_ = lean_ctor_get(v_x_1245_, 1);
v___x_1269_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1270_ = lean_string_dec_eq(v_str_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
return v___y_1243_;
}
else
{
return v_suppressElabErrors_1244_;
}
}
default: 
{
return v___y_1243_;
}
}
}
else
{
return v___y_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1271_, lean_object* v_suppressElabErrors_1272_, lean_object* v_x_1273_){
_start:
{
uint8_t v___y_80182__boxed_1274_; uint8_t v_suppressElabErrors_boxed_1275_; uint8_t v_res_1276_; lean_object* v_r_1277_; 
v___y_80182__boxed_1274_ = lean_unbox(v___y_1271_);
v_suppressElabErrors_boxed_1275_ = lean_unbox(v_suppressElabErrors_1272_);
v_res_1276_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(v___y_80182__boxed_1274_, v_suppressElabErrors_boxed_1275_, v_x_1273_);
lean_dec(v_x_1273_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1279_, lean_object* v_msgData_1280_, uint8_t v_severity_1281_, uint8_t v_isSilent_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; uint8_t v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; uint8_t v___y_1328_; uint8_t v___y_1329_; uint8_t v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1350_; lean_object* v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; uint8_t v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; uint8_t v___y_1365_; lean_object* v___y_1366_; uint8_t v___y_1367_; uint8_t v___x_1372_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1379_; uint8_t v___y_1380_; uint8_t v___y_1382_; uint8_t v___x_1397_; 
v___x_1372_ = 2;
v___x_1397_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1281_, v___x_1372_);
if (v___x_1397_ == 0)
{
v___y_1382_ = v___x_1397_;
goto v___jp_1381_;
}
else
{
uint8_t v___x_1398_; 
lean_inc_ref(v_msgData_1280_);
v___x_1398_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1280_);
v___y_1382_ = v___x_1398_;
goto v___jp_1381_;
}
v___jp_1288_:
{
lean_object* v___x_1298_; lean_object* v_currNamespace_1299_; lean_object* v_openDecls_1300_; lean_object* v_env_1301_; lean_object* v_nextMacroScope_1302_; lean_object* v_ngen_1303_; lean_object* v_auxDeclNGen_1304_; lean_object* v_traceState_1305_; lean_object* v_cache_1306_; lean_object* v_messages_1307_; lean_object* v_infoState_1308_; lean_object* v_snapshotTasks_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1323_; 
v___x_1298_ = lean_st_ref_take(v___y_1297_);
v_currNamespace_1299_ = lean_ctor_get(v___y_1296_, 6);
v_openDecls_1300_ = lean_ctor_get(v___y_1296_, 7);
v_env_1301_ = lean_ctor_get(v___x_1298_, 0);
v_nextMacroScope_1302_ = lean_ctor_get(v___x_1298_, 1);
v_ngen_1303_ = lean_ctor_get(v___x_1298_, 2);
v_auxDeclNGen_1304_ = lean_ctor_get(v___x_1298_, 3);
v_traceState_1305_ = lean_ctor_get(v___x_1298_, 4);
v_cache_1306_ = lean_ctor_get(v___x_1298_, 5);
v_messages_1307_ = lean_ctor_get(v___x_1298_, 6);
v_infoState_1308_ = lean_ctor_get(v___x_1298_, 7);
v_snapshotTasks_1309_ = lean_ctor_get(v___x_1298_, 8);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1311_ = v___x_1298_;
v_isShared_1312_ = v_isSharedCheck_1323_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_snapshotTasks_1309_);
lean_inc(v_infoState_1308_);
lean_inc(v_messages_1307_);
lean_inc(v_cache_1306_);
lean_inc(v_traceState_1305_);
lean_inc(v_auxDeclNGen_1304_);
lean_inc(v_ngen_1303_);
lean_inc(v_nextMacroScope_1302_);
lean_inc(v_env_1301_);
lean_dec(v___x_1298_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1323_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_inc(v_openDecls_1300_);
lean_inc(v_currNamespace_1299_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_currNamespace_1299_);
lean_ctor_set(v___x_1313_, 1, v_openDecls_1300_);
v___x_1314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
lean_ctor_set(v___x_1314_, 1, v___y_1291_);
lean_inc_ref(v___y_1289_);
lean_inc_ref(v___y_1295_);
v___x_1315_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1315_, 0, v___y_1295_);
lean_ctor_set(v___x_1315_, 1, v___y_1293_);
lean_ctor_set(v___x_1315_, 2, v___y_1292_);
lean_ctor_set(v___x_1315_, 3, v___y_1289_);
lean_ctor_set(v___x_1315_, 4, v___x_1314_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*5, v___y_1290_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*5 + 1, v___y_1294_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*5 + 2, v_isSilent_1282_);
v___x_1316_ = l_Lean_MessageLog_add(v___x_1315_, v_messages_1307_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 6, v___x_1316_);
v___x_1318_ = v___x_1311_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_env_1301_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_nextMacroScope_1302_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_ngen_1303_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_auxDeclNGen_1304_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_traceState_1305_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v_cache_1306_);
lean_ctor_set(v_reuseFailAlloc_1322_, 6, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 7, v_infoState_1308_);
lean_ctor_set(v_reuseFailAlloc_1322_, 8, v_snapshotTasks_1309_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_st_ref_set(v___y_1297_, v___x_1318_);
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
}
v___jp_1324_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1348_; 
v___x_1333_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1280_);
v___x_1334_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v___x_1333_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1348_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1348_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_inc_ref_n(v___y_1327_, 2);
v___x_1339_ = l_Lean_FileMap_toPosition(v___y_1327_, v___y_1326_);
lean_dec(v___y_1326_);
v___x_1340_ = l_Lean_FileMap_toPosition(v___y_1327_, v___y_1332_);
lean_dec(v___y_1332_);
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1330_ == 0)
{
lean_del_object(v___x_1337_);
lean_dec_ref(v___y_1325_);
v___y_1289_ = v___x_1342_;
v___y_1290_ = v___y_1328_;
v___y_1291_ = v_a_1335_;
v___y_1292_ = v___x_1341_;
v___y_1293_ = v___x_1339_;
v___y_1294_ = v___y_1329_;
v___y_1295_ = v___y_1331_;
v___y_1296_ = v___y_1285_;
v___y_1297_ = v___y_1286_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1343_; 
lean_inc(v_a_1335_);
v___x_1343_ = l_Lean_MessageData_hasTag(v___y_1325_, v_a_1335_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_dec_ref(v___x_1341_);
lean_dec_ref(v___x_1339_);
lean_dec(v_a_1335_);
v___x_1344_ = lean_box(0);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1344_);
v___x_1346_ = v___x_1337_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
else
{
lean_del_object(v___x_1337_);
v___y_1289_ = v___x_1342_;
v___y_1290_ = v___y_1328_;
v___y_1291_ = v_a_1335_;
v___y_1292_ = v___x_1341_;
v___y_1293_ = v___x_1339_;
v___y_1294_ = v___y_1329_;
v___y_1295_ = v___y_1331_;
v___y_1296_ = v___y_1285_;
v___y_1297_ = v___y_1286_;
goto v___jp_1288_;
}
}
}
}
v___jp_1349_:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Lean_Syntax_getTailPos_x3f(v___y_1353_, v___y_1352_);
lean_dec(v___y_1353_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_inc(v___y_1357_);
v___y_1325_ = v___y_1350_;
v___y_1326_ = v___y_1357_;
v___y_1327_ = v___y_1351_;
v___y_1328_ = v___y_1352_;
v___y_1329_ = v___y_1354_;
v___y_1330_ = v___y_1355_;
v___y_1331_ = v___y_1356_;
v___y_1332_ = v___y_1357_;
goto v___jp_1324_;
}
else
{
lean_object* v_val_1359_; 
v_val_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_val_1359_);
lean_dec_ref(v___x_1358_);
v___y_1325_ = v___y_1350_;
v___y_1326_ = v___y_1357_;
v___y_1327_ = v___y_1351_;
v___y_1328_ = v___y_1352_;
v___y_1329_ = v___y_1354_;
v___y_1330_ = v___y_1355_;
v___y_1331_ = v___y_1356_;
v___y_1332_ = v_val_1359_;
goto v___jp_1324_;
}
}
v___jp_1360_:
{
lean_object* v_ref_1368_; lean_object* v___x_1369_; 
v_ref_1368_ = l_Lean_replaceRef(v_ref_1279_, v___y_1363_);
v___x_1369_ = l_Lean_Syntax_getPos_x3f(v_ref_1368_, v___y_1364_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
v___y_1350_ = v___y_1361_;
v___y_1351_ = v___y_1362_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v_ref_1368_;
v___y_1354_ = v___y_1367_;
v___y_1355_ = v___y_1365_;
v___y_1356_ = v___y_1366_;
v___y_1357_ = v___x_1370_;
goto v___jp_1349_;
}
else
{
lean_object* v_val_1371_; 
v_val_1371_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v___x_1369_);
v___y_1350_ = v___y_1361_;
v___y_1351_ = v___y_1362_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v_ref_1368_;
v___y_1354_ = v___y_1367_;
v___y_1355_ = v___y_1365_;
v___y_1356_ = v___y_1366_;
v___y_1357_ = v_val_1371_;
goto v___jp_1349_;
}
}
v___jp_1373_:
{
if (v___y_1380_ == 0)
{
v___y_1361_ = v___y_1377_;
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1379_;
v___y_1365_ = v___y_1376_;
v___y_1366_ = v___y_1378_;
v___y_1367_ = v_severity_1281_;
goto v___jp_1360_;
}
else
{
v___y_1361_ = v___y_1377_;
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1379_;
v___y_1365_ = v___y_1376_;
v___y_1366_ = v___y_1378_;
v___y_1367_ = v___x_1372_;
goto v___jp_1360_;
}
}
v___jp_1381_:
{
if (v___y_1382_ == 0)
{
lean_object* v_fileName_1383_; lean_object* v_fileMap_1384_; lean_object* v_options_1385_; lean_object* v_ref_1386_; uint8_t v_suppressElabErrors_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; uint8_t v___x_1391_; uint8_t v___x_1392_; 
v_fileName_1383_ = lean_ctor_get(v___y_1285_, 0);
v_fileMap_1384_ = lean_ctor_get(v___y_1285_, 1);
v_options_1385_ = lean_ctor_get(v___y_1285_, 2);
v_ref_1386_ = lean_ctor_get(v___y_1285_, 5);
v_suppressElabErrors_1387_ = lean_ctor_get_uint8(v___y_1285_, sizeof(void*)*14 + 1);
v___x_1388_ = lean_box(v___y_1382_);
v___x_1389_ = lean_box(v_suppressElabErrors_1387_);
v___f_1390_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1390_, 0, v___x_1388_);
lean_closure_set(v___f_1390_, 1, v___x_1389_);
v___x_1391_ = 1;
v___x_1392_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1281_, v___x_1391_);
if (v___x_1392_ == 0)
{
v___y_1374_ = v_fileMap_1384_;
v___y_1375_ = v_ref_1386_;
v___y_1376_ = v_suppressElabErrors_1387_;
v___y_1377_ = v___f_1390_;
v___y_1378_ = v_fileName_1383_;
v___y_1379_ = v___y_1382_;
v___y_1380_ = v___x_1392_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = l_Lean_warningAsError;
v___x_1394_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_1385_, v___x_1393_);
v___y_1374_ = v_fileMap_1384_;
v___y_1375_ = v_ref_1386_;
v___y_1376_ = v_suppressElabErrors_1387_;
v___y_1377_ = v___f_1390_;
v___y_1378_ = v_fileName_1383_;
v___y_1379_ = v___y_1382_;
v___y_1380_ = v___x_1394_;
goto v___jp_1373_;
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v_msgData_1280_);
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1399_, lean_object* v_msgData_1400_, lean_object* v_severity_1401_, lean_object* v_isSilent_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v_severity_boxed_1408_; uint8_t v_isSilent_boxed_1409_; lean_object* v_res_1410_; 
v_severity_boxed_1408_ = lean_unbox(v_severity_1401_);
v_isSilent_boxed_1409_ = lean_unbox(v_isSilent_1402_);
v_res_1410_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_1399_, v_msgData_1400_, v_severity_boxed_1408_, v_isSilent_boxed_1409_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v_ref_1399_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(lean_object* v_ref_1411_, lean_object* v_msgData_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v___x_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = 1;
v___x_1423_ = 0;
v___x_1424_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_1411_, v_msgData_1412_, v___x_1422_, v___x_1423_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7___boxed(lean_object* v_ref_1425_, lean_object* v_msgData_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(v_ref_1425_, v_msgData_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v_ref_1425_);
return v_res_1436_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__0));
v___x_1439_ = l_Lean_stringToMessageData(v___x_1438_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__2));
v___x_1442_ = l_Lean_stringToMessageData(v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(lean_object* v_linterOption_1443_, lean_object* v_stx_1444_, lean_object* v_msg_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_name_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1470_; 
v_name_1455_ = lean_ctor_get(v_linterOption_1443_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_linterOption_1443_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_linterOption_1443_, 1);
lean_dec(v_unused_1471_);
v___x_1457_ = v_linterOption_1443_;
v_isShared_1458_ = v_isSharedCheck_1470_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_name_1455_);
lean_dec(v_linterOption_1443_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1470_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1459_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1);
lean_inc(v_name_1455_);
v___x_1460_ = l_Lean_MessageData_ofName(v_name_1455_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set_tag(v___x_1457_, 7);
lean_ctor_set(v___x_1457_, 1, v___x_1460_);
lean_ctor_set(v___x_1457_, 0, v___x_1459_);
v___x_1462_ = v___x_1457_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v_disable_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1463_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v_disable_1465_ = l_Lean_MessageData_note(v___x_1464_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_msg_1445_);
lean_ctor_set(v___x_1466_, 1, v_disable_1465_);
v___x_1467_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_name_1455_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(v_stx_1444_, v___x_1467_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___boxed(lean_object* v_linterOption_1472_, lean_object* v_stx_1473_, lean_object* v_msg_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v_linterOption_1472_, v_stx_1473_, v_msg_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v_stx_1473_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(lean_object* v_o_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v_env_1489_; lean_object* v___x_1490_; lean_object* v_toEnvExtension_1491_; lean_object* v_asyncMode_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_linterSets_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1488_ = lean_st_ref_get(v___y_1486_);
v_env_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc_ref(v_env_1489_);
lean_dec(v___x_1488_);
v___x_1490_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1491_ = lean_ctor_get(v___x_1490_, 0);
v_asyncMode_1492_ = lean_ctor_get(v_toEnvExtension_1491_, 2);
v___x_1493_ = lean_box(1);
v___x_1494_ = lean_box(0);
v_linterSets_1495_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1493_, v___x_1490_, v_env_1489_, v_asyncMode_1492_, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_o_1485_);
lean_ctor_set(v___x_1496_, 1, v_linterSets_1495_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg___boxed(lean_object* v_o_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_o_1498_, v___y_1499_);
lean_dec(v___y_1499_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_options_1511_; lean_object* v___x_1512_; 
v_options_1511_ = lean_ctor_get(v___y_1508_, 2);
lean_inc_ref(v_options_1511_);
v___x_1512_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_options_1511_, v___y_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(lean_object* v___y_1523_, lean_object* v_mkInfoTree_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v_a_1532_, lean_object* v_a_x3f_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_infoState_1536_; lean_object* v_trees_1537_; lean_object* v___x_1538_; 
v___x_1535_ = lean_st_ref_get(v___y_1523_);
v_infoState_1536_ = lean_ctor_get(v___x_1535_, 7);
lean_inc_ref(v_infoState_1536_);
lean_dec(v___x_1535_);
v_trees_1537_ = lean_ctor_get(v_infoState_1536_, 2);
lean_inc_ref(v_trees_1537_);
lean_dec_ref(v_infoState_1536_);
lean_inc(v___y_1523_);
lean_inc_ref(v___y_1531_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
lean_inc(v___y_1528_);
lean_inc_ref(v___y_1527_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
v___x_1538_ = lean_apply_10(v_mkInfoTree_1524_, v_trees_1537_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1523_, lean_box(0));
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1577_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1577_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1577_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v_infoState_1544_; lean_object* v_env_1545_; lean_object* v_nextMacroScope_1546_; lean_object* v_ngen_1547_; lean_object* v_auxDeclNGen_1548_; lean_object* v_traceState_1549_; lean_object* v_cache_1550_; lean_object* v_messages_1551_; lean_object* v_snapshotTasks_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1576_; 
v___x_1543_ = lean_st_ref_take(v___y_1523_);
v_infoState_1544_ = lean_ctor_get(v___x_1543_, 7);
v_env_1545_ = lean_ctor_get(v___x_1543_, 0);
v_nextMacroScope_1546_ = lean_ctor_get(v___x_1543_, 1);
v_ngen_1547_ = lean_ctor_get(v___x_1543_, 2);
v_auxDeclNGen_1548_ = lean_ctor_get(v___x_1543_, 3);
v_traceState_1549_ = lean_ctor_get(v___x_1543_, 4);
v_cache_1550_ = lean_ctor_get(v___x_1543_, 5);
v_messages_1551_ = lean_ctor_get(v___x_1543_, 6);
v_snapshotTasks_1552_ = lean_ctor_get(v___x_1543_, 8);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1554_ = v___x_1543_;
v_isShared_1555_ = v_isSharedCheck_1576_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_snapshotTasks_1552_);
lean_inc(v_infoState_1544_);
lean_inc(v_messages_1551_);
lean_inc(v_cache_1550_);
lean_inc(v_traceState_1549_);
lean_inc(v_auxDeclNGen_1548_);
lean_inc(v_ngen_1547_);
lean_inc(v_nextMacroScope_1546_);
lean_inc(v_env_1545_);
lean_dec(v___x_1543_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1576_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
uint8_t v_enabled_1556_; lean_object* v_assignment_1557_; lean_object* v_lazyAssignment_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1574_; 
v_enabled_1556_ = lean_ctor_get_uint8(v_infoState_1544_, sizeof(void*)*3);
v_assignment_1557_ = lean_ctor_get(v_infoState_1544_, 0);
v_lazyAssignment_1558_ = lean_ctor_get(v_infoState_1544_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_infoState_1544_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v_infoState_1544_, 2);
lean_dec(v_unused_1575_);
v___x_1560_ = v_infoState_1544_;
v_isShared_1561_ = v_isSharedCheck_1574_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_lazyAssignment_1558_);
lean_inc(v_assignment_1557_);
lean_dec(v_infoState_1544_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1574_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = l_Lean_PersistentArray_push___redArg(v_a_1532_, v_a_1539_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 2, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_assignment_1557_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_lazyAssignment_1558_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v___x_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1573_, sizeof(void*)*3, v_enabled_1556_);
v___x_1564_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1566_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 7, v___x_1564_);
v___x_1566_ = v___x_1554_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_env_1545_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_nextMacroScope_1546_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_ngen_1547_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_auxDeclNGen_1548_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_traceState_1549_);
lean_ctor_set(v_reuseFailAlloc_1572_, 5, v_cache_1550_);
lean_ctor_set(v_reuseFailAlloc_1572_, 6, v_messages_1551_);
lean_ctor_set(v_reuseFailAlloc_1572_, 7, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1572_, 8, v_snapshotTasks_1552_);
v___x_1566_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = lean_st_ref_set(v___y_1523_, v___x_1566_);
v___x_1568_ = lean_box(0);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1568_);
v___x_1570_ = v___x_1541_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v_a_1532_);
v_a_1578_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1538_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1538_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0___boxed(lean_object* v___y_1586_, lean_object* v_mkInfoTree_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v_a_1595_, lean_object* v_a_x3f_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1586_, v_mkInfoTree_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v_a_1595_, v_a_x3f_1596_);
lean_dec(v_a_x3f_1596_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1586_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(lean_object* v_x_1599_, lean_object* v_mkInfoTree_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v_infoState_1611_; uint8_t v_enabled_1612_; 
v___x_1610_ = lean_st_ref_get(v___y_1608_);
v_infoState_1611_ = lean_ctor_get(v___x_1610_, 7);
lean_inc_ref(v_infoState_1611_);
lean_dec(v___x_1610_);
v_enabled_1612_ = lean_ctor_get_uint8(v_infoState_1611_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1611_);
if (v_enabled_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref(v_mkInfoTree_1600_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
v___x_1613_ = lean_apply_9(v_x_1599_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, lean_box(0));
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; lean_object* v_a_1615_; lean_object* v_r_1616_; 
v___x_1614_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_1608_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
v_r_1616_ = lean_apply_9(v_x_1599_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, lean_box(0));
if (lean_obj_tag(v_r_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1641_; 
v_a_1617_ = lean_ctor_get(v_r_1616_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_r_1616_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1619_ = v_r_1616_;
v_isShared_1620_ = v_isSharedCheck_1641_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v_r_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1641_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
lean_inc(v_a_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 1);
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1608_, v_mkInfoTree_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v_a_1615_, v___x_1622_);
lean_dec_ref(v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v___x_1623_, 0);
lean_dec(v_unused_1631_);
v___x_1625_ = v___x_1623_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v___x_1623_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_a_1617_);
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1617_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_a_1617_);
v_a_1632_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1623_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1623_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_a_1642_ = lean_ctor_get(v_r_1616_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v_r_1616_);
v___x_1643_ = lean_box(0);
v___x_1644_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1608_, v_mkInfoTree_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v_a_1615_, v___x_1643_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v___x_1644_, 0);
lean_dec(v_unused_1652_);
v___x_1646_ = v___x_1644_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_dec(v___x_1644_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 1);
lean_ctor_set(v___x_1646_, 0, v_a_1642_);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1642_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1642_);
v_a_1653_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1644_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1644_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___boxed(lean_object* v_x_1661_, lean_object* v_mkInfoTree_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v_x_1661_, v_mkInfoTree_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
return v_res_1672_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6));
v___x_1684_ = l_Lean_stringToMessageData(v___x_1683_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8));
v___x_1687_ = l_Lean_stringToMessageData(v___x_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object* v_usingArg_1694_, lean_object* v_snd_1695_, uint8_t v___x_1696_, uint8_t v___x_1697_, uint8_t v___x_1698_, lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v___x_1701_, lean_object* v_simprocs_1702_, lean_object* v_discharge_x3f_1703_, lean_object* v_snd_1704_, lean_object* v___x_1705_, lean_object* v___f_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; 
if (lean_obj_tag(v_usingArg_1694_) == 1)
{
lean_object* v_val_1896_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___x_1948_; lean_object* v_infoState_1949_; uint8_t v_enabled_1950_; 
v_val_1896_ = lean_ctor_get(v_usingArg_1694_, 0);
lean_inc(v_val_1896_);
lean_dec_ref(v_usingArg_1694_);
v___x_1948_ = lean_st_ref_get(v___y_1714_);
v_infoState_1949_ = lean_ctor_get(v___x_1948_, 7);
lean_inc_ref(v_infoState_1949_);
lean_dec(v___x_1948_);
v_enabled_1950_ = lean_ctor_get_uint8(v_infoState_1949_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1949_);
if (v_enabled_1950_ == 0)
{
lean_dec_ref(v___f_1706_);
v___y_1898_ = v___y_1707_;
v___y_1899_ = v___y_1708_;
v___y_1900_ = v___y_1709_;
v___y_1901_ = v___y_1710_;
v___y_1902_ = v___y_1711_;
v___y_1903_ = v___y_1712_;
v___y_1904_ = v___y_1713_;
v___y_1905_ = v___y_1714_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1951_; lean_object* v_a_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; 
v___x_1951_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_1714_);
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref(v___x_1951_);
v___f_1953_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1953_, 0, v_a_1952_);
v___x_1954_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v___f_1953_, v___f_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_dec_ref(v___x_1954_);
v___y_1898_ = v___y_1707_;
v___y_1899_ = v___y_1708_;
v___y_1900_ = v___y_1709_;
v___y_1901_ = v___y_1710_;
v___y_1902_ = v___y_1711_;
v___y_1903_ = v___y_1712_;
v___y_1904_ = v___y_1713_;
v___y_1905_ = v___y_1714_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_val_1896_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
v___jp_1897_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_st_ref_get(v___y_1903_);
v___x_1907_ = lean_box(0);
v___x_1908_ = l_Lean_Elab_Tactic_elabTerm(v_val_1896_, v___x_1907_, v___x_1696_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_n(v_a_1909_, 2);
lean_dec_ref(v___x_1908_);
v___x_1910_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(v_snd_1695_, v_a_1909_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_mctx_1911_; lean_object* v_a_1912_; uint8_t v___x_1913_; 
v_mctx_1911_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_ref(v_mctx_1911_);
lean_dec(v___x_1906_);
v_a_1912_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1910_);
v___x_1913_ = lean_unbox(v_a_1912_);
lean_dec(v_a_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_mctx_1911_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
v___x_1914_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9);
v___x_1915_ = l_Lean_indentExpr(v_a_1909_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_Expr_mvar___override(v_snd_1695_);
v___x_1920_ = l_Lean_MessageData_ofExpr(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1918_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v___x_1921_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_mvarCounter_1931_; 
v_mvarCounter_1931_ = lean_ctor_get(v_mctx_1911_, 3);
lean_inc(v_mvarCounter_1931_);
lean_dec_ref(v_mctx_1911_);
lean_inc(v_a_1909_);
v___y_1780_ = v_a_1909_;
v___y_1781_ = v_mvarCounter_1931_;
v___y_1782_ = v___x_1907_;
v___y_1783_ = v___x_1907_;
v___y_1784_ = v_a_1909_;
v___y_1785_ = v___y_1898_;
v___y_1786_ = v___y_1899_;
v___y_1787_ = v___y_1900_;
v___y_1788_ = v___y_1901_;
v___y_1789_ = v___y_1902_;
v___y_1790_ = v___y_1903_;
v___y_1791_ = v___y_1904_;
v___y_1792_ = v___y_1905_;
goto v___jp_1779_;
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec(v_a_1909_);
lean_dec(v___x_1906_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1932_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1910_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1910_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v___x_1906_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1940_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1908_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1908_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
else
{
lean_object* v_lctx_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v___f_1706_);
lean_dec_ref(v___x_1699_);
lean_dec(v_usingArg_1694_);
v_lctx_1963_ = lean_ctor_get(v___y_1711_, 2);
v___x_1964_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13));
v___x_1965_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_1963_, v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 1)
{
lean_object* v_val_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_val_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_val_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l_Lean_LocalDecl_fvarId(v_val_1966_);
lean_dec(v_val_1966_);
v___x_1968_ = lean_mk_empty_array_with_capacity(v___x_1700_);
v___x_1969_ = lean_array_push(v___x_1968_, v___x_1967_);
lean_inc_ref(v_snd_1704_);
v___x_1970_ = l_Lean_Meta_simpGoal(v_snd_1695_, v___x_1701_, v_simprocs_1702_, v_discharge_x3f_1703_, v___x_1697_, v___x_1969_, v_snd_1704_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1999_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1999_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1999_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_fst_1975_; 
v_fst_1975_ = lean_ctor_get(v_a_1971_, 0);
if (lean_obj_tag(v_fst_1975_) == 1)
{
lean_object* v_val_1976_; lean_object* v_snd_1977_; lean_object* v_snd_1978_; lean_object* v___x_1979_; 
lean_del_object(v___x_1973_);
lean_dec_ref(v_snd_1704_);
v_val_1976_ = lean_ctor_get(v_fst_1975_, 0);
lean_inc(v_val_1976_);
v_snd_1977_ = lean_ctor_get(v_a_1971_, 1);
lean_inc(v_snd_1977_);
lean_dec(v_a_1971_);
v_snd_1978_ = lean_ctor_get(v_val_1976_, 1);
lean_inc(v_snd_1978_);
lean_dec(v_val_1976_);
v___x_1979_ = l_Lean_MVarId_assumption(v_snd_1978_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v___x_1979_, 0);
lean_dec(v_unused_1987_);
v___x_1981_ = v___x_1979_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_dec(v___x_1979_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v_snd_1977_);
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_snd_1977_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_snd_1977_);
v_a_1988_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1979_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1979_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v___x_1997_; 
lean_dec(v_a_1971_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_snd_1704_);
v___x_1997_ = v___x_1973_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_snd_1704_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_snd_1704_);
v_a_2000_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1970_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1970_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v___x_1965_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
v___x_2008_ = l_Lean_MVarId_assumption(v_snd_1695_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v___x_2008_, 0);
lean_dec(v_unused_2016_);
v___x_2010_ = v___x_2008_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_dec(v___x_2008_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_snd_1704_);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_snd_1704_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_snd_1704_);
v_a_2017_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2008_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2008_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
v___jp_1716_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v___x_1720_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_snd_1695_, v___y_1718_, v___y_1719_);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___x_1720_, 0);
lean_dec(v_unused_1728_);
v___x_1722_ = v___x_1720_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_dec(v___x_1720_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___y_1717_);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___y_1717_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
v___jp_1729_:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Core_mkFreshUserName(v___y_1741_, v___y_1743_, v___y_1735_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_n(v_a_1747_, 2);
lean_dec_ref(v___x_1746_);
v___x_1748_ = l_Lean_MVarId_rename(v___y_1739_, v___y_1745_, v_a_1747_, v___y_1733_, v___y_1738_, v___y_1743_, v___y_1735_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc_n(v_a_1749_, 2);
lean_dec_ref(v___x_1748_);
v___x_1750_ = lean_box(v___x_1696_);
v___x_1751_ = lean_box(v___x_1697_);
v___x_1752_ = lean_box(v___x_1698_);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1753_, 0, v_a_1749_);
lean_closure_set(v___f_1753_, 1, v_a_1747_);
lean_closure_set(v___f_1753_, 2, v___x_1750_);
lean_closure_set(v___f_1753_, 3, v___x_1751_);
lean_closure_set(v___f_1753_, 4, v___x_1752_);
lean_closure_set(v___f_1753_, 5, v___y_1730_);
lean_closure_set(v___f_1753_, 6, v___y_1731_);
lean_closure_set(v___f_1753_, 7, v___x_1699_);
lean_closure_set(v___f_1753_, 8, v___y_1732_);
v___x_1754_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_a_1749_, v___f_1753_, v___y_1744_, v___y_1737_, v___y_1742_, v___y_1734_, v___y_1733_, v___y_1738_, v___y_1743_, v___y_1735_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_dec_ref(v___x_1754_);
v___y_1717_ = v___y_1740_;
v___y_1718_ = v___y_1736_;
v___y_1719_ = v___y_1738_;
goto v___jp_1716_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1736_);
lean_dec(v_snd_1695_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1747_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1763_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1748_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1748_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1771_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1746_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1746_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
v___jp_1779_:
{
lean_object* v___x_1793_; 
lean_inc(v_snd_1695_);
v___x_1793_ = l_Lean_MVarId_getType(v_snd_1695_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1793_);
lean_inc(v_snd_1695_);
v___x_1795_ = l_Lean_MVarId_getTag(v_snd_1695_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1794_, v_a_1796_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = l_Lean_Expr_mvarId_x21(v_a_1798_);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1));
lean_inc_ref(v___y_1784_);
v___x_1801_ = l_Lean_MVarId_note(v___x_1799_, v___x_1800_, v___y_1784_, v___y_1783_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1863_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
v_fst_1803_ = lean_ctor_get(v_a_1802_, 0);
v_snd_1804_ = lean_ctor_get(v_a_1802_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_a_1802_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1806_ = v_a_1802_;
v_isShared_1807_ = v_isSharedCheck_1863_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snd_1804_);
lean_inc(v_fst_1803_);
lean_dec(v_a_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1863_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1700_);
lean_inc(v_fst_1803_);
v___x_1809_ = lean_array_push(v___x_1808_, v_fst_1803_);
v___x_1810_ = l_Lean_Meta_simpGoal(v_snd_1804_, v___x_1701_, v_simprocs_1702_, v_discharge_x3f_1703_, v___x_1697_, v___x_1809_, v_snd_1704_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v_fst_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref(v___x_1810_);
v_fst_1812_ = lean_ctor_get(v_a_1811_, 0);
if (lean_obj_tag(v_fst_1812_) == 0)
{
lean_object* v_snd_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_fst_1803_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___x_1699_);
v_snd_1813_ = lean_ctor_get(v_a_1811_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_a_1811_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v_a_1811_, 0);
lean_dec(v_unused_1847_);
v___x_1815_ = v_a_1811_;
v_isShared_1816_ = v_isSharedCheck_1846_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_snd_1813_);
lean_dec(v_a_1811_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1846_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v_a_1818_; uint8_t v___x_1819_; 
v___x_1817_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1818_);
lean_dec(v_a_1818_);
if (v___x_1819_ == 0)
{
lean_del_object(v___x_1815_);
lean_del_object(v___x_1806_);
lean_dec_ref(v___y_1784_);
v___y_1717_ = v_snd_1813_;
v___y_1718_ = v_a_1798_;
v___y_1719_ = v___y_1790_;
goto v___jp_1716_;
}
else
{
if (lean_obj_tag(v___y_1784_) == 1)
{
lean_object* v_fvarId_1820_; lean_object* v_lctx_1821_; lean_object* v___x_1822_; 
v_fvarId_1820_ = lean_ctor_get(v___y_1784_, 0);
v_lctx_1821_ = lean_ctor_get(v___y_1789_, 2);
lean_inc(v_fvarId_1820_);
lean_inc_ref(v_lctx_1821_);
v___x_1822_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1821_, v_fvarId_1820_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_dec_ref(v___y_1784_);
lean_del_object(v___x_1815_);
lean_del_object(v___x_1806_);
v___y_1717_ = v_snd_1813_;
v___y_1718_ = v_a_1798_;
v___y_1719_ = v___y_1790_;
goto v___jp_1716_;
}
else
{
lean_dec_ref(v___x_1822_);
if (v___x_1698_ == 0)
{
lean_dec_ref(v___y_1784_);
lean_del_object(v___x_1815_);
lean_del_object(v___x_1806_);
v___y_1717_ = v_snd_1813_;
v___y_1718_ = v_a_1798_;
v___y_1719_ = v___y_1790_;
goto v___jp_1716_;
}
else
{
lean_object* v_ref_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v_ref_1823_ = lean_ctor_get(v___y_1791_, 5);
v___x_1824_ = l_linter_unnecessarySimpa;
v___x_1825_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3);
v___x_1826_ = l_Lean_MessageData_ofExpr(v___y_1784_);
lean_inc_ref(v___x_1826_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 7);
lean_ctor_set(v___x_1815_, 1, v___x_1826_);
lean_ctor_set(v___x_1815_, 0, v___x_1825_);
v___x_1828_ = v___x_1815_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1829_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5);
if (v_isShared_1807_ == 0)
{
lean_ctor_set_tag(v___x_1806_, 7);
lean_ctor_set(v___x_1806_, 1, v___x_1829_);
lean_ctor_set(v___x_1806_, 0, v___x_1828_);
v___x_1831_ = v___x_1806_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___x_1826_);
v___x_1833_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v___x_1824_, v_ref_1823_, v___x_1834_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_dec_ref(v___x_1835_);
v___y_1717_ = v_snd_1813_;
v___y_1718_ = v_a_1798_;
v___y_1719_ = v___y_1790_;
goto v___jp_1716_;
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_snd_1813_);
lean_dec(v_a_1798_);
lean_dec(v_snd_1695_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
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
lean_del_object(v___x_1815_);
lean_del_object(v___x_1806_);
lean_dec_ref(v___y_1784_);
v___y_1717_ = v_snd_1813_;
v___y_1718_ = v_a_1798_;
v___y_1719_ = v___y_1790_;
goto v___jp_1716_;
}
}
}
}
else
{
lean_object* v_val_1848_; lean_object* v_snd_1849_; lean_object* v_fst_1850_; lean_object* v_snd_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
lean_del_object(v___x_1806_);
lean_dec_ref(v___y_1784_);
v_val_1848_ = lean_ctor_get(v_fst_1812_, 0);
lean_inc(v_val_1848_);
v_snd_1849_ = lean_ctor_get(v_a_1811_, 1);
lean_inc(v_snd_1849_);
lean_dec(v_a_1811_);
v_fst_1850_ = lean_ctor_get(v_val_1848_, 0);
lean_inc(v_fst_1850_);
v_snd_1851_ = lean_ctor_get(v_val_1848_, 1);
lean_inc(v_snd_1851_);
lean_dec(v_val_1848_);
v___x_1852_ = lean_array_get_size(v_fst_1850_);
v___x_1853_ = lean_nat_dec_lt(v___x_1705_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec(v_fst_1850_);
v___y_1730_ = v___y_1780_;
v___y_1731_ = v___y_1781_;
v___y_1732_ = v___y_1782_;
v___y_1733_ = v___y_1789_;
v___y_1734_ = v___y_1788_;
v___y_1735_ = v___y_1792_;
v___y_1736_ = v_a_1798_;
v___y_1737_ = v___y_1786_;
v___y_1738_ = v___y_1790_;
v___y_1739_ = v_snd_1851_;
v___y_1740_ = v_snd_1849_;
v___y_1741_ = v___x_1800_;
v___y_1742_ = v___y_1787_;
v___y_1743_ = v___y_1791_;
v___y_1744_ = v___y_1785_;
v___y_1745_ = v_fst_1803_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1854_; 
lean_dec(v_fst_1803_);
v___x_1854_ = lean_array_fget(v_fst_1850_, v___x_1705_);
lean_dec(v_fst_1850_);
v___y_1730_ = v___y_1780_;
v___y_1731_ = v___y_1781_;
v___y_1732_ = v___y_1782_;
v___y_1733_ = v___y_1789_;
v___y_1734_ = v___y_1788_;
v___y_1735_ = v___y_1792_;
v___y_1736_ = v_a_1798_;
v___y_1737_ = v___y_1786_;
v___y_1738_ = v___y_1790_;
v___y_1739_ = v_snd_1851_;
v___y_1740_ = v_snd_1849_;
v___y_1741_ = v___x_1800_;
v___y_1742_ = v___y_1787_;
v___y_1743_ = v___y_1791_;
v___y_1744_ = v___y_1785_;
v___y_1745_ = v___x_1854_;
goto v___jp_1729_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_del_object(v___x_1806_);
lean_dec(v_fst_1803_);
lean_dec(v_a_1798_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1855_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1810_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1810_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_a_1798_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1864_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1801_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1801_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1872_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1797_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1797_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_a_1794_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1880_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1795_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1795_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v_snd_1704_);
lean_dec(v_discharge_x3f_1703_);
lean_dec_ref(v_simprocs_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v___x_1699_);
lean_dec(v_snd_1695_);
v_a_1888_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1793_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1793_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2025_ = _args[0];
lean_object* v_snd_2026_ = _args[1];
lean_object* v___x_2027_ = _args[2];
lean_object* v___x_2028_ = _args[3];
lean_object* v___x_2029_ = _args[4];
lean_object* v___x_2030_ = _args[5];
lean_object* v___x_2031_ = _args[6];
lean_object* v___x_2032_ = _args[7];
lean_object* v_simprocs_2033_ = _args[8];
lean_object* v_discharge_x3f_2034_ = _args[9];
lean_object* v_snd_2035_ = _args[10];
lean_object* v___x_2036_ = _args[11];
lean_object* v___f_2037_ = _args[12];
lean_object* v___y_2038_ = _args[13];
lean_object* v___y_2039_ = _args[14];
lean_object* v___y_2040_ = _args[15];
lean_object* v___y_2041_ = _args[16];
lean_object* v___y_2042_ = _args[17];
lean_object* v___y_2043_ = _args[18];
lean_object* v___y_2044_ = _args[19];
lean_object* v___y_2045_ = _args[20];
lean_object* v___y_2046_ = _args[21];
_start:
{
uint8_t v___x_80895__boxed_2047_; uint8_t v___x_80896__boxed_2048_; uint8_t v___x_80897__boxed_2049_; lean_object* v_res_2050_; 
v___x_80895__boxed_2047_ = lean_unbox(v___x_2027_);
v___x_80896__boxed_2048_ = lean_unbox(v___x_2028_);
v___x_80897__boxed_2049_ = lean_unbox(v___x_2029_);
v_res_2050_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(v_usingArg_2025_, v_snd_2026_, v___x_80895__boxed_2047_, v___x_80896__boxed_2048_, v___x_80897__boxed_2049_, v___x_2030_, v___x_2031_, v___x_2032_, v_simprocs_2033_, v_discharge_x3f_2034_, v_snd_2035_, v___x_2036_, v___f_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___x_2036_);
lean_dec(v___x_2031_);
return v_res_2050_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_unsigned_to_nat(32u);
v___x_2055_ = lean_mk_empty_array_with_capacity(v___x_2054_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4));
v___x_2061_ = l_Lean_MessageData_ofFormat(v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object* v___x_2062_, lean_object* v_tk_2063_, lean_object* v___x_2064_, lean_object* v___x_2065_, lean_object* v___x_2066_, lean_object* v_simprocs_2067_, uint8_t v___x_2068_, lean_object* v_usingArg_2069_, uint8_t v___x_2070_, uint8_t v___x_2071_, lean_object* v___x_2072_, lean_object* v___x_2073_, lean_object* v_usingTk_x3f_2074_, lean_object* v_discharge_x3f_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___y_2086_; 
if (lean_obj_tag(v_usingTk_x3f_2074_) == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_box(0);
v___y_2086_ = v___x_2190_;
goto v___jp_2085_;
}
else
{
lean_object* v_val_2191_; 
v_val_2191_ = lean_ctor_get(v_usingTk_x3f_2074_, 0);
lean_inc(v_val_2191_);
lean_dec_ref(v_usingTk_x3f_2074_);
v___y_2086_ = v_val_2191_;
goto v___jp_2085_;
}
v___jp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2087_ = lean_mk_empty_array_with_capacity(v___x_2062_);
v___x_2088_ = lean_array_push(v___x_2087_, v_tk_2063_);
v___x_2089_ = lean_array_push(v___x_2088_, v___y_2086_);
v___x_2090_ = lean_box(2);
v___x_2091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2064_);
lean_ctor_set(v___x_2091_, 2, v___x_2089_);
v___x_2092_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2091_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
v___x_2094_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2077_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; size_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
v___x_2096_ = lean_mk_empty_array_with_capacity(v___x_2065_);
v___x_2097_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1);
lean_inc_n(v___x_2065_, 3);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___x_2065_);
v___x_2099_ = lean_unsigned_to_nat(32u);
v___x_2100_ = lean_mk_empty_array_with_capacity(v___x_2099_);
v___x_2101_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2);
v___x_2102_ = ((size_t)5ULL);
v___x_2103_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2100_);
lean_ctor_set(v___x_2103_, 2, v___x_2065_);
lean_ctor_set(v___x_2103_, 3, v___x_2065_);
lean_ctor_set_usize(v___x_2103_, 4, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2097_);
lean_ctor_set(v___x_2104_, 1, v___x_2097_);
lean_ctor_set(v___x_2104_, 2, v___x_2097_);
lean_ctor_set(v___x_2104_, 3, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2098_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
lean_inc_ref(v___x_2105_);
lean_inc(v_discharge_x3f_2075_);
lean_inc_ref(v_simprocs_2067_);
lean_inc_ref(v___x_2066_);
v___x_2106_ = l_Lean_Meta_simpGoal(v_a_2095_, v___x_2066_, v_simprocs_2067_, v_discharge_x3f_2075_, v___x_2068_, v___x_2096_, v___x_2105_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v_fst_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref(v___x_2106_);
v_fst_2108_ = lean_ctor_get(v_a_2107_, 0);
if (lean_obj_tag(v_fst_2108_) == 1)
{
lean_object* v_val_2109_; lean_object* v_snd_2110_; lean_object* v_snd_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v___x_2105_);
v_val_2109_ = lean_ctor_get(v_fst_2108_, 0);
lean_inc(v_val_2109_);
v_snd_2110_ = lean_ctor_get(v_a_2107_, 1);
lean_inc(v_snd_2110_);
lean_dec(v_a_2107_);
v_snd_2111_ = lean_ctor_get(v_val_2109_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_val_2109_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_val_2109_, 0);
lean_dec(v_unused_2135_);
v___x_2113_ = v_val_2109_;
v_isShared_2114_ = v_isSharedCheck_2134_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_snd_2111_);
lean_dec(v_val_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2134_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_box(0);
lean_inc(v_snd_2111_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 1);
lean_ctor_set(v___x_2113_, 1, v___x_2115_);
lean_ctor_set(v___x_2113_, 0, v_snd_2111_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_snd_2111_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2117_, v___y_2077_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___f_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___y_2123_; lean_object* v___x_2124_; 
lean_dec_ref(v___x_2118_);
v___f_2119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2119_, 0, v_a_2093_);
v___x_2120_ = lean_box(v___x_2068_);
v___x_2121_ = lean_box(v___x_2070_);
v___x_2122_ = lean_box(v___x_2071_);
lean_inc(v_snd_2111_);
v___y_2123_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 22, 13);
lean_closure_set(v___y_2123_, 0, v_usingArg_2069_);
lean_closure_set(v___y_2123_, 1, v_snd_2111_);
lean_closure_set(v___y_2123_, 2, v___x_2120_);
lean_closure_set(v___y_2123_, 3, v___x_2121_);
lean_closure_set(v___y_2123_, 4, v___x_2122_);
lean_closure_set(v___y_2123_, 5, v___x_2072_);
lean_closure_set(v___y_2123_, 6, v___x_2073_);
lean_closure_set(v___y_2123_, 7, v___x_2066_);
lean_closure_set(v___y_2123_, 8, v_simprocs_2067_);
lean_closure_set(v___y_2123_, 9, v_discharge_x3f_2075_);
lean_closure_set(v___y_2123_, 10, v_snd_2110_);
lean_closure_set(v___y_2123_, 11, v___x_2065_);
lean_closure_set(v___y_2123_, 12, v___f_2119_);
v___x_2124_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_snd_2111_, v___y_2123_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
return v___x_2124_;
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_snd_2111_);
lean_dec(v_snd_2110_);
lean_dec(v_a_2093_);
lean_dec(v_discharge_x3f_2075_);
lean_dec(v___x_2073_);
lean_dec_ref(v___x_2072_);
lean_dec(v_usingArg_2069_);
lean_dec_ref(v_simprocs_2067_);
lean_dec_ref(v___x_2066_);
lean_dec(v___x_2065_);
v_a_2125_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2118_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2118_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
else
{
lean_object* v___x_2136_; lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2107_);
lean_dec(v_a_2093_);
lean_dec(v_discharge_x3f_2075_);
lean_dec(v___x_2073_);
lean_dec_ref(v___x_2072_);
lean_dec(v_usingArg_2069_);
lean_dec_ref(v_simprocs_2067_);
lean_dec_ref(v___x_2066_);
lean_dec(v___x_2065_);
v___x_2136_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2165_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2165_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
uint8_t v___x_2141_; 
v___x_2141_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2137_);
lean_dec(v_a_2137_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2143_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2105_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2105_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
else
{
lean_object* v_ref_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_del_object(v___x_2139_);
v_ref_2145_ = lean_ctor_get(v___y_2082_, 5);
v___x_2146_ = l_linter_unnecessarySimpa;
v___x_2147_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5);
v___x_2148_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v___x_2146_, v_ref_2145_, v___x_2147_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v___x_2148_, 0);
lean_dec(v_unused_2156_);
v___x_2150_ = v___x_2148_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v___x_2148_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2105_);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2105_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v___x_2105_);
v_a_2157_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2148_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2148_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v___x_2105_);
lean_dec(v_a_2093_);
lean_dec(v_discharge_x3f_2075_);
lean_dec(v___x_2073_);
lean_dec_ref(v___x_2072_);
lean_dec(v_usingArg_2069_);
lean_dec_ref(v_simprocs_2067_);
lean_dec_ref(v___x_2066_);
lean_dec(v___x_2065_);
v_a_2166_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2106_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2106_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2093_);
lean_dec(v_discharge_x3f_2075_);
lean_dec(v___x_2073_);
lean_dec_ref(v___x_2072_);
lean_dec(v_usingArg_2069_);
lean_dec_ref(v_simprocs_2067_);
lean_dec_ref(v___x_2066_);
lean_dec(v___x_2065_);
v_a_2174_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2094_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2094_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_discharge_x3f_2075_);
lean_dec(v___x_2073_);
lean_dec_ref(v___x_2072_);
lean_dec(v_usingArg_2069_);
lean_dec_ref(v_simprocs_2067_);
lean_dec_ref(v___x_2066_);
lean_dec(v___x_2065_);
v_a_2182_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2092_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2092_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object** _args){
lean_object* v___x_2192_ = _args[0];
lean_object* v_tk_2193_ = _args[1];
lean_object* v___x_2194_ = _args[2];
lean_object* v___x_2195_ = _args[3];
lean_object* v___x_2196_ = _args[4];
lean_object* v_simprocs_2197_ = _args[5];
lean_object* v___x_2198_ = _args[6];
lean_object* v_usingArg_2199_ = _args[7];
lean_object* v___x_2200_ = _args[8];
lean_object* v___x_2201_ = _args[9];
lean_object* v___x_2202_ = _args[10];
lean_object* v___x_2203_ = _args[11];
lean_object* v_usingTk_x3f_2204_ = _args[12];
lean_object* v_discharge_x3f_2205_ = _args[13];
lean_object* v___y_2206_ = _args[14];
lean_object* v___y_2207_ = _args[15];
lean_object* v___y_2208_ = _args[16];
lean_object* v___y_2209_ = _args[17];
lean_object* v___y_2210_ = _args[18];
lean_object* v___y_2211_ = _args[19];
lean_object* v___y_2212_ = _args[20];
lean_object* v___y_2213_ = _args[21];
lean_object* v___y_2214_ = _args[22];
_start:
{
uint8_t v___x_81617__boxed_2215_; uint8_t v___x_81618__boxed_2216_; uint8_t v___x_81619__boxed_2217_; lean_object* v_res_2218_; 
v___x_81617__boxed_2215_ = lean_unbox(v___x_2198_);
v___x_81618__boxed_2216_ = lean_unbox(v___x_2200_);
v___x_81619__boxed_2217_ = lean_unbox(v___x_2201_);
v_res_2218_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(v___x_2192_, v_tk_2193_, v___x_2194_, v___x_2195_, v___x_2196_, v_simprocs_2197_, v___x_81617__boxed_2215_, v_usingArg_2199_, v___x_81618__boxed_2216_, v___x_81619__boxed_2217_, v___x_2202_, v___x_2203_, v_usingTk_x3f_2204_, v_discharge_x3f_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___x_2192_);
return v_res_2218_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Array_mkArray0(lean_box(0));
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2238_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16));
v___x_2239_ = lean_unsigned_to_nat(15u);
v___x_2240_ = lean_unsigned_to_nat(116u);
v___x_2241_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15));
v___x_2242_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14));
v___x_2243_ = l_mkPanicMessageWithDecl(v___x_2242_, v___x_2241_, v___x_2240_, v___x_2239_, v___x_2238_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object* v_tk_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v___x_2248_, lean_object* v___x_2249_, lean_object* v___x_2250_, uint8_t v___x_2251_, lean_object* v___x_2252_, lean_object* v___f_2253_, lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v___x_2259_, lean_object* v_usingArg_2260_, lean_object* v___x_2261_, uint8_t v___x_2262_, lean_object* v_usingTk_x3f_2263_, lean_object* v_squeeze_2264_, lean_object* v_unfold_2265_, lean_object* v_args_2266_, lean_object* v_only_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___y_2279_; lean_object* v___y_2283_; lean_object* v_stx_2284_; lean_object* v___y_2285_; lean_object* v_ref_2286_; lean_object* v___y_2287_; lean_object* v___y_2305_; lean_object* v_stx_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v_options_2310_; lean_object* v_ref_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; uint8_t v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_args_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; uint8_t v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_only_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; uint8_t v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; uint8_t v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; uint8_t v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; uint8_t v___y_2683_; lean_object* v___y_2685_; uint8_t v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2761_; 
v_options_2310_ = lean_ctor_get(v___y_2275_, 2);
v_ref_2311_ = lean_ctor_get(v___y_2275_, 5);
v___x_2312_ = 0;
v___x_2313_ = l_Lean_SourceInfo_fromRef(v_ref_2311_, v___x_2312_);
v___x_2314_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3));
lean_inc_ref(v___x_2248_);
lean_inc_ref(v___x_2247_);
lean_inc_ref(v___x_2246_);
v___x_2315_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2314_);
lean_inc(v___x_2313_);
v___x_2316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2313_);
lean_ctor_set(v___x_2316_, 1, v___x_2314_);
v___x_2317_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5));
v___x_2318_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6);
if (lean_obj_tag(v___y_2268_) == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2761_ = v___x_2770_;
goto v___jp_2760_;
}
else
{
lean_object* v_val_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_val_2771_ = lean_ctor_get(v___y_2268_, 0);
lean_inc(v_val_2771_);
lean_dec_ref(v___y_2268_);
v___x_2772_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2773_ = lean_array_push(v___x_2772_, v_val_2771_);
v___y_2761_ = v___x_2773_;
goto v___jp_2760_;
}
v___jp_2278_:
{
lean_object* v_diag_2280_; lean_object* v___x_2281_; 
v_diag_2280_ = lean_ctor_get(v___y_2279_, 1);
lean_inc_ref(v_diag_2280_);
lean_dec_ref(v___y_2279_);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v_diag_2280_);
return v___x_2281_;
}
v___jp_2282_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2288_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1));
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v_stx_2284_);
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
lean_ctor_set(v___x_2291_, 2, v___x_2290_);
lean_ctor_set(v___x_2291_, 3, v___x_2290_);
lean_ctor_set(v___x_2291_, 4, v___x_2290_);
lean_ctor_set(v___x_2291_, 5, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_ref_2286_);
v___x_2293_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2));
v___x_2294_ = 4;
v___x_2295_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2245_, v___x_2291_, v___x_2292_, v___x_2293_, v___x_2290_, v___x_2294_, v___y_2285_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2285_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_dec_ref(v___x_2295_);
v___y_2279_ = v___y_2283_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v___y_2283_);
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
v___jp_2304_:
{
lean_object* v_ref_2309_; 
v_ref_2309_ = lean_ctor_get(v___y_2307_, 5);
lean_inc(v_ref_2309_);
v___y_2283_ = v___y_2305_;
v_stx_2284_ = v_stx_2306_;
v___y_2285_ = v___y_2307_;
v_ref_2286_ = v_ref_2309_;
v___y_2287_ = v___y_2308_;
goto v___jp_2282_;
}
v___jp_2319_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2331_ = l_Array_append___redArg(v___x_2318_, v___y_2330_);
lean_dec_ref(v___y_2330_);
lean_inc_n(v___y_2326_, 2);
v___x_2332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___y_2326_);
lean_ctor_set(v___x_2332_, 1, v___x_2317_);
lean_ctor_set(v___x_2332_, 2, v___x_2331_);
v___x_2333_ = l_Lean_Syntax_node5(v___y_2326_, v___x_2249_, v___y_2329_, v___y_2325_, v___y_2323_, v___y_2328_, v___x_2332_);
lean_inc(v___y_2322_);
v___x_2334_ = l_Lean_Syntax_node4(v___y_2326_, v___x_2252_, v___y_2321_, v___y_2322_, v___y_2322_, v___x_2333_);
v___y_2305_ = v___y_2324_;
v_stx_2306_ = v___x_2334_;
v___y_2307_ = v___y_2327_;
v___y_2308_ = v___y_2320_;
goto v___jp_2304_;
}
v___jp_2335_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = l_Array_append___redArg(v___x_2318_, v___y_2346_);
lean_dec_ref(v___y_2346_);
lean_inc(v___y_2343_);
v___x_2348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2348_, 0, v___y_2343_);
lean_ctor_set(v___x_2348_, 1, v___x_2317_);
lean_ctor_set(v___x_2348_, 2, v___x_2347_);
if (lean_obj_tag(v___y_2341_) == 1)
{
lean_object* v_val_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_dec(v___x_2250_);
v_val_2349_ = lean_ctor_get(v___y_2341_, 0);
lean_inc(v_val_2349_);
lean_dec_ref(v___y_2341_);
v___x_2350_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2343_);
v___x_2351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___y_2343_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = l_Array_mkArray2___redArg(v___x_2351_, v_val_2349_);
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2337_;
v___y_2322_ = v___y_2339_;
v___y_2323_ = v___y_2338_;
v___y_2324_ = v___y_2340_;
v___y_2325_ = v___y_2342_;
v___y_2326_ = v___y_2343_;
v___y_2327_ = v___y_2345_;
v___y_2328_ = v___x_2348_;
v___y_2329_ = v___y_2344_;
v___y_2330_ = v___x_2352_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2353_; 
lean_dec(v___y_2341_);
v___x_2353_ = lean_mk_empty_array_with_capacity(v___x_2250_);
lean_dec(v___x_2250_);
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2337_;
v___y_2322_ = v___y_2339_;
v___y_2323_ = v___y_2338_;
v___y_2324_ = v___y_2340_;
v___y_2325_ = v___y_2342_;
v___y_2326_ = v___y_2343_;
v___y_2327_ = v___y_2345_;
v___y_2328_ = v___x_2348_;
v___y_2329_ = v___y_2344_;
v___y_2330_ = v___x_2353_;
goto v___jp_2319_;
}
}
v___jp_2354_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = l_Array_append___redArg(v___x_2318_, v___y_2365_);
lean_dec_ref(v___y_2365_);
lean_inc(v___y_2362_);
v___x_2367_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2367_, 0, v___y_2362_);
lean_ctor_set(v___x_2367_, 1, v___x_2317_);
lean_ctor_set(v___x_2367_, 2, v___x_2366_);
if (lean_obj_tag(v___y_2358_) == 1)
{
lean_object* v_val_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_val_2368_ = lean_ctor_get(v___y_2358_, 0);
lean_inc(v_val_2368_);
lean_dec_ref(v___y_2358_);
v___x_2369_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2370_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___y_2362_, 4);
v___x_2372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___y_2362_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Array_append___redArg(v___x_2318_, v_val_2368_);
lean_dec(v_val_2368_);
v___x_2374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2374_, 0, v___y_2362_);
lean_ctor_set(v___x_2374_, 1, v___x_2317_);
lean_ctor_set(v___x_2374_, 2, v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___y_2362_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = l_Lean_Syntax_node3(v___y_2362_, v___x_2370_, v___x_2372_, v___x_2374_, v___x_2376_);
v___x_2378_ = l_Array_mkArray1___redArg(v___x_2377_);
v___y_2336_ = v___y_2355_;
v___y_2337_ = v___y_2356_;
v___y_2338_ = v___x_2367_;
v___y_2339_ = v___y_2357_;
v___y_2340_ = v___y_2359_;
v___y_2341_ = v___y_2360_;
v___y_2342_ = v___y_2361_;
v___y_2343_ = v___y_2362_;
v___y_2344_ = v___y_2364_;
v___y_2345_ = v___y_2363_;
v___y_2346_ = v___x_2378_;
goto v___jp_2335_;
}
else
{
lean_object* v___x_2379_; 
lean_dec(v___y_2358_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2379_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2336_ = v___y_2355_;
v___y_2337_ = v___y_2356_;
v___y_2338_ = v___x_2367_;
v___y_2339_ = v___y_2357_;
v___y_2340_ = v___y_2359_;
v___y_2341_ = v___y_2360_;
v___y_2342_ = v___y_2361_;
v___y_2343_ = v___y_2362_;
v___y_2344_ = v___y_2364_;
v___y_2345_ = v___y_2363_;
v___y_2346_ = v___x_2379_;
goto v___jp_2335_;
}
}
v___jp_2380_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = l_Array_append___redArg(v___x_2318_, v___y_2391_);
lean_dec_ref(v___y_2391_);
lean_inc(v___y_2388_);
v___x_2393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___y_2388_);
lean_ctor_set(v___x_2393_, 1, v___x_2317_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
if (lean_obj_tag(v___y_2386_) == 1)
{
lean_object* v_val_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v_val_2394_ = lean_ctor_get(v___y_2386_, 0);
lean_inc(v_val_2394_);
lean_dec_ref(v___y_2386_);
v___x_2395_ = l_Lean_SourceInfo_fromRef(v_val_2394_, v___x_2251_);
lean_dec(v_val_2394_);
v___x_2396_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = l_Array_mkArray1___redArg(v___x_2397_);
v___y_2355_ = v___y_2381_;
v___y_2356_ = v___y_2382_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2384_;
v___y_2359_ = v___y_2385_;
v___y_2360_ = v___y_2387_;
v___y_2361_ = v___x_2393_;
v___y_2362_ = v___y_2388_;
v___y_2363_ = v___y_2390_;
v___y_2364_ = v___y_2389_;
v___y_2365_ = v___x_2398_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2399_; 
lean_dec(v___y_2386_);
v___x_2399_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2355_ = v___y_2381_;
v___y_2356_ = v___y_2382_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2384_;
v___y_2359_ = v___y_2385_;
v___y_2360_ = v___y_2387_;
v___y_2361_ = v___x_2393_;
v___y_2362_ = v___y_2388_;
v___y_2363_ = v___y_2390_;
v___y_2364_ = v___y_2389_;
v___y_2365_ = v___x_2399_;
goto v___jp_2354_;
}
}
v___jp_2400_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2412_ = l_Array_append___redArg(v___x_2318_, v___y_2411_);
lean_dec_ref(v___y_2411_);
lean_inc_n(v___y_2403_, 2);
v___x_2413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2413_, 0, v___y_2403_);
lean_ctor_set(v___x_2413_, 1, v___x_2317_);
lean_ctor_set(v___x_2413_, 2, v___x_2412_);
v___x_2414_ = l_Lean_Syntax_node5(v___y_2403_, v___x_2249_, v___y_2410_, v___y_2405_, v___y_2409_, v___y_2404_, v___x_2413_);
v___x_2415_ = l_Lean_Syntax_node2(v___y_2403_, v___y_2408_, v___y_2407_, v___x_2414_);
v___y_2305_ = v___y_2402_;
v_stx_2306_ = v___x_2415_;
v___y_2307_ = v___y_2406_;
v___y_2308_ = v___y_2401_;
goto v___jp_2304_;
}
v___jp_2416_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = l_Array_append___redArg(v___x_2318_, v___y_2427_);
lean_dec_ref(v___y_2427_);
lean_inc(v___y_2420_);
v___x_2429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2429_, 0, v___y_2420_);
lean_ctor_set(v___x_2429_, 1, v___x_2317_);
lean_ctor_set(v___x_2429_, 2, v___x_2428_);
if (lean_obj_tag(v___y_2419_) == 1)
{
lean_object* v_val_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_dec(v___x_2250_);
v_val_2430_ = lean_ctor_get(v___y_2419_, 0);
lean_inc(v_val_2430_);
lean_dec_ref(v___y_2419_);
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2420_);
v___x_2432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___y_2420_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = l_Array_mkArray2___redArg(v___x_2432_, v_val_2430_);
v___y_2401_ = v___y_2417_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2420_;
v___y_2404_ = v___x_2429_;
v___y_2405_ = v___y_2421_;
v___y_2406_ = v___y_2426_;
v___y_2407_ = v___y_2425_;
v___y_2408_ = v___y_2424_;
v___y_2409_ = v___y_2423_;
v___y_2410_ = v___y_2422_;
v___y_2411_ = v___x_2433_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2434_; 
lean_dec(v___y_2419_);
v___x_2434_ = lean_mk_empty_array_with_capacity(v___x_2250_);
lean_dec(v___x_2250_);
v___y_2401_ = v___y_2417_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2420_;
v___y_2404_ = v___x_2429_;
v___y_2405_ = v___y_2421_;
v___y_2406_ = v___y_2426_;
v___y_2407_ = v___y_2425_;
v___y_2408_ = v___y_2424_;
v___y_2409_ = v___y_2423_;
v___y_2410_ = v___y_2422_;
v___y_2411_ = v___x_2434_;
goto v___jp_2400_;
}
}
v___jp_2435_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = l_Array_append___redArg(v___x_2318_, v___y_2446_);
lean_dec_ref(v___y_2446_);
lean_inc(v___y_2440_);
v___x_2448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2448_, 0, v___y_2440_);
lean_ctor_set(v___x_2448_, 1, v___x_2317_);
lean_ctor_set(v___x_2448_, 2, v___x_2447_);
if (lean_obj_tag(v___y_2437_) == 1)
{
lean_object* v_val_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_val_2449_ = lean_ctor_get(v___y_2437_, 0);
lean_inc(v_val_2449_);
lean_dec_ref(v___y_2437_);
v___x_2450_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2451_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___y_2440_, 4);
v___x_2453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___y_2440_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = l_Array_append___redArg(v___x_2318_, v_val_2449_);
lean_dec(v_val_2449_);
v___x_2455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2455_, 0, v___y_2440_);
lean_ctor_set(v___x_2455_, 1, v___x_2317_);
lean_ctor_set(v___x_2455_, 2, v___x_2454_);
v___x_2456_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___y_2440_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = l_Lean_Syntax_node3(v___y_2440_, v___x_2451_, v___x_2453_, v___x_2455_, v___x_2457_);
v___x_2459_ = l_Array_mkArray1___redArg(v___x_2458_);
v___y_2417_ = v___y_2436_;
v___y_2418_ = v___y_2438_;
v___y_2419_ = v___y_2439_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2441_;
v___y_2422_ = v___y_2445_;
v___y_2423_ = v___x_2448_;
v___y_2424_ = v___y_2444_;
v___y_2425_ = v___y_2443_;
v___y_2426_ = v___y_2442_;
v___y_2427_ = v___x_2459_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2460_; 
lean_dec(v___y_2437_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2460_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2417_ = v___y_2436_;
v___y_2418_ = v___y_2438_;
v___y_2419_ = v___y_2439_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2441_;
v___y_2422_ = v___y_2445_;
v___y_2423_ = v___x_2448_;
v___y_2424_ = v___y_2444_;
v___y_2425_ = v___y_2443_;
v___y_2426_ = v___y_2442_;
v___y_2427_ = v___x_2460_;
goto v___jp_2416_;
}
}
v___jp_2461_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = l_Array_append___redArg(v___x_2318_, v___y_2472_);
lean_dec_ref(v___y_2472_);
lean_inc(v___y_2467_);
v___x_2474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2474_, 0, v___y_2467_);
lean_ctor_set(v___x_2474_, 1, v___x_2317_);
lean_ctor_set(v___x_2474_, 2, v___x_2473_);
if (lean_obj_tag(v___y_2465_) == 1)
{
lean_object* v_val_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_val_2475_ = lean_ctor_get(v___y_2465_, 0);
lean_inc(v_val_2475_);
lean_dec_ref(v___y_2465_);
v___x_2476_ = l_Lean_SourceInfo_fromRef(v_val_2475_, v___x_2251_);
lean_dec(v_val_2475_);
v___x_2477_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Array_mkArray1___redArg(v___x_2478_);
v___y_2436_ = v___y_2462_;
v___y_2437_ = v___y_2463_;
v___y_2438_ = v___y_2464_;
v___y_2439_ = v___y_2466_;
v___y_2440_ = v___y_2467_;
v___y_2441_ = v___x_2474_;
v___y_2442_ = v___y_2471_;
v___y_2443_ = v___y_2470_;
v___y_2444_ = v___y_2469_;
v___y_2445_ = v___y_2468_;
v___y_2446_ = v___x_2479_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2480_; 
lean_dec(v___y_2465_);
v___x_2480_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2436_ = v___y_2462_;
v___y_2437_ = v___y_2463_;
v___y_2438_ = v___y_2464_;
v___y_2439_ = v___y_2466_;
v___y_2440_ = v___y_2467_;
v___y_2441_ = v___x_2474_;
v___y_2442_ = v___y_2471_;
v___y_2443_ = v___y_2470_;
v___y_2444_ = v___y_2469_;
v___y_2445_ = v___y_2468_;
v___y_2446_ = v___x_2480_;
goto v___jp_2435_;
}
}
v___jp_2481_:
{
if (v___y_2492_ == 0)
{
lean_object* v___x_2497_; 
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2497_ = lean_apply_9(v___f_2253_, v___y_2483_, v___y_2482_, v___y_2488_, v___y_2485_, v___y_2484_, v___y_2493_, v___y_2490_, v___y_2491_, lean_box(0));
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc_n(v_a_2498_, 3);
lean_dec_ref(v___x_2497_);
v___x_2499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2254_);
v___x_2500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2317_);
lean_ctor_set(v___x_2500_, 2, v___x_2318_);
if (lean_obj_tag(v___y_2496_) == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2381_ = v___y_2491_;
v___y_2382_ = v___x_2499_;
v___y_2383_ = v___x_2500_;
v___y_2384_ = v___y_2486_;
v___y_2385_ = v___y_2494_;
v___y_2386_ = v___y_2487_;
v___y_2387_ = v___y_2495_;
v___y_2388_ = v_a_2498_;
v___y_2389_ = v___y_2489_;
v___y_2390_ = v___y_2490_;
v___y_2391_ = v___x_2501_;
goto v___jp_2380_;
}
else
{
lean_object* v_val_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_val_2502_ = lean_ctor_get(v___y_2496_, 0);
lean_inc(v_val_2502_);
lean_dec_ref(v___y_2496_);
v___x_2503_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2504_ = lean_array_push(v___x_2503_, v_val_2502_);
v___y_2381_ = v___y_2491_;
v___y_2382_ = v___x_2499_;
v___y_2383_ = v___x_2500_;
v___y_2384_ = v___y_2486_;
v___y_2385_ = v___y_2494_;
v___y_2386_ = v___y_2487_;
v___y_2387_ = v___y_2495_;
v___y_2388_ = v_a_2498_;
v___y_2389_ = v___y_2489_;
v___y_2390_ = v___y_2490_;
v___y_2391_ = v___x_2504_;
goto v___jp_2380_;
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v_a_2505_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2497_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2497_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v___x_2513_; 
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2252_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2513_ = lean_apply_9(v___f_2253_, v___y_2483_, v___y_2482_, v___y_2488_, v___y_2485_, v___y_2484_, v___y_2493_, v___y_2490_, v___y_2491_, lean_box(0));
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc_n(v_a_2514_, 2);
lean_dec_ref(v___x_2513_);
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12));
lean_inc_ref(v___x_2248_);
lean_inc_ref(v___x_2247_);
lean_inc_ref(v___x_2246_);
v___x_2516_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2515_);
v___x_2517_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13));
v___x_2518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2518_, 0, v_a_2514_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
if (lean_obj_tag(v___y_2496_) == 0)
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2462_ = v___y_2491_;
v___y_2463_ = v___y_2486_;
v___y_2464_ = v___y_2494_;
v___y_2465_ = v___y_2487_;
v___y_2466_ = v___y_2495_;
v___y_2467_ = v_a_2514_;
v___y_2468_ = v___y_2489_;
v___y_2469_ = v___x_2516_;
v___y_2470_ = v___x_2518_;
v___y_2471_ = v___y_2490_;
v___y_2472_ = v___x_2519_;
goto v___jp_2461_;
}
else
{
lean_object* v_val_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_val_2520_ = lean_ctor_get(v___y_2496_, 0);
lean_inc(v_val_2520_);
lean_dec_ref(v___y_2496_);
v___x_2521_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2522_ = lean_array_push(v___x_2521_, v_val_2520_);
v___y_2462_ = v___y_2491_;
v___y_2463_ = v___y_2486_;
v___y_2464_ = v___y_2494_;
v___y_2465_ = v___y_2487_;
v___y_2466_ = v___y_2495_;
v___y_2467_ = v_a_2514_;
v___y_2468_ = v___y_2489_;
v___y_2469_ = v___x_2516_;
v___y_2470_ = v___x_2518_;
v___y_2471_ = v___y_2490_;
v___y_2472_ = v___x_2522_;
goto v___jp_2461_;
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v_a_2523_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2513_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2513_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
v___jp_2531_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2548_ = lean_unsigned_to_nat(5u);
v___x_2549_ = l_Lean_Syntax_getArg(v___y_2533_, v___x_2548_);
lean_dec(v___y_2533_);
v___x_2550_ = l_Lean_Syntax_matchesNull(v___x_2549_, v___x_2250_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec(v_args_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2551_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2552_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2551_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
v___y_2305_ = v___y_2534_;
v_stx_2306_ = v_a_2553_;
v___y_2307_ = v___y_2546_;
v___y_2308_ = v___y_2547_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v___y_2534_);
lean_dec(v_tk_2245_);
v_a_2554_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2552_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2552_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Syntax_getOptional_x3f(v___y_2537_);
lean_dec(v___y_2537_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_box(0);
v___y_2482_ = v___y_2541_;
v___y_2483_ = v___y_2540_;
v___y_2484_ = v___y_2544_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v_args_2539_;
v___y_2487_ = v___y_2535_;
v___y_2488_ = v___y_2542_;
v___y_2489_ = v___y_2538_;
v___y_2490_ = v___y_2546_;
v___y_2491_ = v___y_2547_;
v___y_2492_ = v___y_2532_;
v___y_2493_ = v___y_2545_;
v___y_2494_ = v___y_2534_;
v___y_2495_ = v___y_2536_;
v___y_2496_ = v___x_2563_;
goto v___jp_2481_;
}
else
{
lean_object* v_val_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v_val_2564_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2562_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_val_2564_);
lean_dec(v___x_2562_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_val_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
v___y_2482_ = v___y_2541_;
v___y_2483_ = v___y_2540_;
v___y_2484_ = v___y_2544_;
v___y_2485_ = v___y_2543_;
v___y_2486_ = v_args_2539_;
v___y_2487_ = v___y_2535_;
v___y_2488_ = v___y_2542_;
v___y_2489_ = v___y_2538_;
v___y_2490_ = v___y_2546_;
v___y_2491_ = v___y_2547_;
v___y_2492_ = v___y_2532_;
v___y_2493_ = v___y_2545_;
v___y_2494_ = v___y_2534_;
v___y_2495_ = v___y_2536_;
v___y_2496_ = v___x_2569_;
goto v___jp_2481_;
}
}
}
}
}
v___jp_2572_:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = l_Lean_Syntax_getArg(v___y_2574_, v___x_2255_);
v___x_2589_ = l_Lean_Syntax_isNone(v___x_2588_);
if (v___x_2589_ == 0)
{
uint8_t v___x_2590_; 
lean_inc(v___x_2588_);
v___x_2590_ = l_Lean_Syntax_matchesNull(v___x_2588_, v___x_2256_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v___x_2588_);
lean_dec(v_only_2579_);
lean_dec(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2574_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2591_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2592_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2591_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v___x_2592_);
v___y_2305_ = v___y_2575_;
v_stx_2306_ = v_a_2593_;
v___y_2307_ = v___y_2586_;
v___y_2308_ = v___y_2587_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec_ref(v___y_2575_);
lean_dec(v_tk_2245_);
v_a_2594_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2592_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2592_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = l_Lean_Syntax_getArg(v___x_2588_, v___x_2257_);
lean_dec(v___x_2257_);
lean_dec(v___x_2588_);
v___x_2603_ = l_Lean_Syntax_getArgs(v___x_2602_);
lean_dec(v___x_2602_);
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
v___y_2532_ = v___y_2573_;
v___y_2533_ = v___y_2574_;
v___y_2534_ = v___y_2575_;
v___y_2535_ = v_only_2579_;
v___y_2536_ = v___y_2576_;
v___y_2537_ = v___y_2577_;
v___y_2538_ = v___y_2578_;
v_args_2539_ = v___x_2604_;
v___y_2540_ = v___y_2580_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2584_;
v___y_2545_ = v___y_2585_;
v___y_2546_ = v___y_2586_;
v___y_2547_ = v___y_2587_;
goto v___jp_2531_;
}
}
else
{
lean_object* v___x_2605_; 
lean_dec(v___x_2588_);
lean_dec(v___x_2257_);
v___x_2605_ = lean_box(0);
v___y_2532_ = v___y_2573_;
v___y_2533_ = v___y_2574_;
v___y_2534_ = v___y_2575_;
v___y_2535_ = v_only_2579_;
v___y_2536_ = v___y_2576_;
v___y_2537_ = v___y_2577_;
v___y_2538_ = v___y_2578_;
v_args_2539_ = v___x_2605_;
v___y_2540_ = v___y_2580_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2584_;
v___y_2545_ = v___y_2585_;
v___y_2546_ = v___y_2586_;
v___y_2547_ = v___y_2587_;
goto v___jp_2531_;
}
}
v___jp_2606_:
{
lean_object* v_usedTheorems_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_usedTheorems_2611_ = lean_ctor_get(v___y_2608_, 0);
v___x_2612_ = l_Lean_Syntax_unsetTrailing(v___y_2609_);
v___x_2613_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2612_, v_usedTheorems_2611_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; uint8_t v___x_2615_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc_n(v_a_2614_, 2);
lean_dec_ref(v___x_2613_);
v___x_2615_ = l_Lean_Syntax_isOfKind(v_a_2614_, v___x_2315_);
lean_dec(v___x_2315_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_inc(v_ref_2311_);
lean_dec(v_a_2614_);
lean_dec(v___y_2610_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2616_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2617_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2616_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v___y_2283_ = v___y_2608_;
v_stx_2284_ = v_a_2618_;
v___y_2285_ = v___y_2275_;
v_ref_2286_ = v_ref_2311_;
v___y_2287_ = v___y_2276_;
goto v___jp_2282_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v___y_2608_);
lean_dec(v_ref_2311_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_tk_2245_);
v_a_2619_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2617_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2617_);
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
else
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = l_Lean_Syntax_getArg(v_a_2614_, v___x_2257_);
lean_inc(v___x_2627_);
v___x_2628_ = l_Lean_Syntax_isOfKind(v___x_2627_, v___x_2258_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_inc(v_ref_2311_);
lean_dec(v___x_2627_);
lean_dec(v_a_2614_);
lean_dec(v___y_2610_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2629_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2630_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2629_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v___x_2630_);
v___y_2283_ = v___y_2608_;
v_stx_2284_ = v_a_2631_;
v___y_2285_ = v___y_2275_;
v_ref_2286_ = v_ref_2311_;
v___y_2287_ = v___y_2276_;
goto v___jp_2282_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v___y_2608_);
lean_dec(v_ref_2311_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_tk_2245_);
v_a_2632_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2630_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2630_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = l_Lean_Syntax_getArg(v_a_2614_, v___x_2259_);
lean_dec(v___x_2259_);
v___x_2641_ = l_Lean_Syntax_getArg(v_a_2614_, v___x_2256_);
v___x_2642_ = l_Lean_Syntax_isNone(v___x_2641_);
if (v___x_2642_ == 0)
{
uint8_t v___x_2643_; 
lean_inc(v___x_2641_);
v___x_2643_ = l_Lean_Syntax_matchesNull(v___x_2641_, v___x_2257_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_inc(v_ref_2311_);
lean_dec(v___x_2641_);
lean_dec(v___x_2640_);
lean_dec(v___x_2627_);
lean_dec(v_a_2614_);
lean_dec(v___y_2610_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2644_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2645_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2644_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___y_2283_ = v___y_2608_;
v_stx_2284_ = v_a_2646_;
v___y_2285_ = v___y_2275_;
v_ref_2286_ = v_ref_2311_;
v___y_2287_ = v___y_2276_;
goto v___jp_2282_;
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___y_2608_);
lean_dec(v_ref_2311_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_tk_2245_);
v_a_2647_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2645_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2645_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = l_Lean_Syntax_getArg(v___x_2641_, v___x_2250_);
lean_dec(v___x_2641_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
v___y_2573_ = v___y_2607_;
v___y_2574_ = v_a_2614_;
v___y_2575_ = v___y_2608_;
v___y_2576_ = v___y_2610_;
v___y_2577_ = v___x_2640_;
v___y_2578_ = v___x_2627_;
v_only_2579_ = v___x_2656_;
v___y_2580_ = v___y_2269_;
v___y_2581_ = v___y_2270_;
v___y_2582_ = v___y_2271_;
v___y_2583_ = v___y_2272_;
v___y_2584_ = v___y_2273_;
v___y_2585_ = v___y_2274_;
v___y_2586_ = v___y_2275_;
v___y_2587_ = v___y_2276_;
goto v___jp_2572_;
}
}
else
{
lean_object* v___x_2657_; 
lean_dec(v___x_2641_);
v___x_2657_ = lean_box(0);
v___y_2573_ = v___y_2607_;
v___y_2574_ = v_a_2614_;
v___y_2575_ = v___y_2608_;
v___y_2576_ = v___y_2610_;
v___y_2577_ = v___x_2640_;
v___y_2578_ = v___x_2627_;
v_only_2579_ = v___x_2657_;
v___y_2580_ = v___y_2269_;
v___y_2581_ = v___y_2270_;
v___y_2582_ = v___y_2271_;
v___y_2583_ = v___y_2272_;
v___y_2584_ = v___y_2273_;
v___y_2585_ = v___y_2274_;
v___y_2586_ = v___y_2275_;
v___y_2587_ = v___y_2276_;
goto v___jp_2572_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2608_);
lean_dec(v___x_2315_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v_a_2658_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2613_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2613_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
v___jp_2666_:
{
if (lean_obj_tag(v_usingArg_2260_) == 0)
{
v___y_2607_ = v___y_2667_;
v___y_2608_ = v___y_2668_;
v___y_2609_ = v___y_2669_;
v___y_2610_ = v_usingArg_2260_;
goto v___jp_2606_;
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2678_; 
v_val_2670_ = lean_ctor_get(v_usingArg_2260_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_usingArg_2260_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2672_ = v_usingArg_2260_;
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_val_2670_);
lean_dec(v_usingArg_2260_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2678_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2674_ = l_Lean_Syntax_unsetTrailing(v_val_2670_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2674_);
v___x_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
v___y_2607_ = v___y_2667_;
v___y_2608_ = v___y_2668_;
v___y_2609_ = v___y_2669_;
v___y_2610_ = v___x_2676_;
goto v___jp_2606_;
}
}
}
}
v___jp_2679_:
{
if (v___y_2683_ == 0)
{
lean_dec(v___y_2682_);
lean_dec(v___x_2315_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v_usingArg_2260_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v___y_2279_ = v___y_2681_;
goto v___jp_2278_;
}
else
{
v___y_2667_ = v___y_2680_;
v___y_2668_ = v___y_2681_;
v___y_2669_ = v___y_2682_;
goto v___jp_2666_;
}
}
v___jp_2684_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___f_2694_; lean_object* v___x_2695_; 
v___x_2690_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_2689_, v___x_2312_);
v___x_2691_ = lean_box(v___x_2251_);
v___x_2692_ = lean_box(v___x_2312_);
v___x_2693_ = lean_box(v___x_2262_);
lean_inc(v___x_2257_);
lean_inc_ref(v___x_2254_);
lean_inc(v_usingArg_2260_);
lean_inc(v___x_2250_);
lean_inc(v_tk_2245_);
lean_inc(v___x_2259_);
v___f_2694_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 23, 13);
lean_closure_set(v___f_2694_, 0, v___x_2259_);
lean_closure_set(v___f_2694_, 1, v_tk_2245_);
lean_closure_set(v___f_2694_, 2, v___x_2317_);
lean_closure_set(v___f_2694_, 3, v___x_2250_);
lean_closure_set(v___f_2694_, 4, v___x_2690_);
lean_closure_set(v___f_2694_, 5, v___y_2685_);
lean_closure_set(v___f_2694_, 6, v___x_2691_);
lean_closure_set(v___f_2694_, 7, v_usingArg_2260_);
lean_closure_set(v___f_2694_, 8, v___x_2692_);
lean_closure_set(v___f_2694_, 9, v___x_2693_);
lean_closure_set(v___f_2694_, 10, v___x_2254_);
lean_closure_set(v___f_2694_, 11, v___x_2257_);
lean_closure_set(v___f_2694_, 12, v_usingTk_x3f_2263_);
v___x_2695_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_2687_, v___f_2694_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2687_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_2698_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_2310_, v___x_2697_);
if (v___x_2698_ == 0)
{
if (lean_obj_tag(v_squeeze_2264_) == 0)
{
v___y_2680_ = v___y_2686_;
v___y_2681_ = v_a_2696_;
v___y_2682_ = v___y_2688_;
v___y_2683_ = v___x_2698_;
goto v___jp_2679_;
}
else
{
v___y_2680_ = v___y_2686_;
v___y_2681_ = v_a_2696_;
v___y_2682_ = v___y_2688_;
v___y_2683_ = v___x_2262_;
goto v___jp_2679_;
}
}
else
{
v___y_2667_ = v___y_2686_;
v___y_2668_ = v_a_2696_;
v___y_2669_ = v___y_2688_;
goto v___jp_2666_;
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v___y_2688_);
lean_dec(v___x_2315_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v_usingArg_2260_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v_a_2699_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2695_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2695_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
v___jp_2707_:
{
v___y_2685_ = v___y_2709_;
v___y_2686_ = v___x_2312_;
v___y_2687_ = v___y_2710_;
v___y_2688_ = v___y_2711_;
v___y_2689_ = v___y_2708_;
goto v___jp_2684_;
}
v___jp_2712_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2716_ = l_Array_append___redArg(v___x_2318_, v___y_2715_);
lean_dec_ref(v___y_2715_);
lean_inc_n(v___x_2313_, 2);
v___x_2717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2313_);
lean_ctor_set(v___x_2717_, 1, v___x_2317_);
lean_ctor_set(v___x_2717_, 2, v___x_2716_);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2313_);
lean_ctor_set(v___x_2718_, 1, v___x_2317_);
lean_ctor_set(v___x_2718_, 2, v___x_2318_);
lean_inc(v___x_2315_);
v___x_2719_ = l_Lean_Syntax_node6(v___x_2313_, v___x_2315_, v___x_2316_, v___x_2261_, v___y_2714_, v___y_2713_, v___x_2717_, v___x_2718_);
v___x_2720_ = 0;
v___x_2721_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18));
v___x_2722_ = lean_box(v___x_2312_);
v___x_2723_ = lean_box(v___x_2720_);
v___x_2724_ = lean_box(v___x_2312_);
lean_inc(v___x_2719_);
v___x_2725_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_2725_, 0, v___x_2719_);
lean_closure_set(v___x_2725_, 1, v___x_2722_);
lean_closure_set(v___x_2725_, 2, v___x_2723_);
lean_closure_set(v___x_2725_, 3, v___x_2724_);
lean_closure_set(v___x_2725_, 4, v___x_2721_);
v___x_2726_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2725_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref(v___x_2726_);
if (lean_obj_tag(v_unfold_2265_) == 0)
{
lean_object* v_ctx_2728_; lean_object* v_simprocs_2729_; lean_object* v_dischargeWrapper_2730_; 
v_ctx_2728_ = lean_ctor_get(v_a_2727_, 0);
lean_inc_ref(v_ctx_2728_);
v_simprocs_2729_ = lean_ctor_get(v_a_2727_, 1);
lean_inc_ref(v_simprocs_2729_);
v_dischargeWrapper_2730_ = lean_ctor_get(v_a_2727_, 2);
lean_inc(v_dischargeWrapper_2730_);
lean_dec(v_a_2727_);
v___y_2708_ = v_ctx_2728_;
v___y_2709_ = v_simprocs_2729_;
v___y_2710_ = v_dischargeWrapper_2730_;
v___y_2711_ = v___x_2719_;
goto v___jp_2707_;
}
else
{
if (v___x_2262_ == 0)
{
lean_object* v_ctx_2731_; lean_object* v_simprocs_2732_; lean_object* v_dischargeWrapper_2733_; 
v_ctx_2731_ = lean_ctor_get(v_a_2727_, 0);
lean_inc_ref(v_ctx_2731_);
v_simprocs_2732_ = lean_ctor_get(v_a_2727_, 1);
lean_inc_ref(v_simprocs_2732_);
v_dischargeWrapper_2733_ = lean_ctor_get(v_a_2727_, 2);
lean_inc(v_dischargeWrapper_2733_);
lean_dec(v_a_2727_);
v___y_2708_ = v_ctx_2731_;
v___y_2709_ = v_simprocs_2732_;
v___y_2710_ = v_dischargeWrapper_2733_;
v___y_2711_ = v___x_2719_;
goto v___jp_2707_;
}
else
{
lean_object* v_ctx_2734_; lean_object* v_simprocs_2735_; lean_object* v_dischargeWrapper_2736_; lean_object* v___x_2737_; 
v_ctx_2734_ = lean_ctor_get(v_a_2727_, 0);
lean_inc_ref(v_ctx_2734_);
v_simprocs_2735_ = lean_ctor_get(v_a_2727_, 1);
lean_inc_ref(v_simprocs_2735_);
v_dischargeWrapper_2736_ = lean_ctor_get(v_a_2727_, 2);
lean_inc(v_dischargeWrapper_2736_);
lean_dec(v_a_2727_);
v___x_2737_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2734_);
v___y_2685_ = v_simprocs_2735_;
v___y_2686_ = v___x_2262_;
v___y_2687_ = v_dischargeWrapper_2736_;
v___y_2688_ = v___x_2719_;
v___y_2689_ = v___x_2737_;
goto v___jp_2684_;
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v___x_2719_);
lean_dec(v___x_2315_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v_usingTk_x3f_2263_);
lean_dec(v_usingArg_2260_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v_a_2738_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2726_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2726_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
v___jp_2746_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = l_Array_append___redArg(v___x_2318_, v___y_2748_);
lean_dec_ref(v___y_2748_);
lean_inc(v___x_2313_);
v___x_2750_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2313_);
lean_ctor_set(v___x_2750_, 1, v___x_2317_);
lean_ctor_set(v___x_2750_, 2, v___x_2749_);
if (lean_obj_tag(v_args_2266_) == 1)
{
lean_object* v_val_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_val_2751_ = lean_ctor_get(v_args_2266_, 0);
v___x_2752_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___x_2313_, 3);
v___x_2753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2313_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Array_append___redArg(v___x_2318_, v_val_2751_);
v___x_2755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2313_);
lean_ctor_set(v___x_2755_, 1, v___x_2317_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
v___x_2756_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2313_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_Array_mkArray3___redArg(v___x_2753_, v___x_2755_, v___x_2757_);
v___y_2713_ = v___x_2750_;
v___y_2714_ = v___y_2747_;
v___y_2715_ = v___x_2758_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2713_ = v___x_2750_;
v___y_2714_ = v___y_2747_;
v___y_2715_ = v___x_2759_;
goto v___jp_2712_;
}
}
v___jp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = l_Array_append___redArg(v___x_2318_, v___y_2761_);
lean_dec_ref(v___y_2761_);
lean_inc(v___x_2313_);
v___x_2763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2313_);
lean_ctor_set(v___x_2763_, 1, v___x_2317_);
lean_ctor_set(v___x_2763_, 2, v___x_2762_);
if (lean_obj_tag(v_only_2267_) == 1)
{
lean_object* v_val_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_val_2764_ = lean_ctor_get(v_only_2267_, 0);
v___x_2765_ = l_Lean_SourceInfo_fromRef(v_val_2764_, v___x_2251_);
v___x_2766_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = l_Array_mkArray1___redArg(v___x_2767_);
v___y_2747_ = v___x_2763_;
v___y_2748_ = v___x_2768_;
goto v___jp_2746_;
}
else
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2747_ = v___x_2763_;
v___y_2748_ = v___x_2769_;
goto v___jp_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object** _args){
lean_object* v_tk_2774_ = _args[0];
lean_object* v___x_2775_ = _args[1];
lean_object* v___x_2776_ = _args[2];
lean_object* v___x_2777_ = _args[3];
lean_object* v___x_2778_ = _args[4];
lean_object* v___x_2779_ = _args[5];
lean_object* v___x_2780_ = _args[6];
lean_object* v___x_2781_ = _args[7];
lean_object* v___f_2782_ = _args[8];
lean_object* v___x_2783_ = _args[9];
lean_object* v___x_2784_ = _args[10];
lean_object* v___x_2785_ = _args[11];
lean_object* v___x_2786_ = _args[12];
lean_object* v___x_2787_ = _args[13];
lean_object* v___x_2788_ = _args[14];
lean_object* v_usingArg_2789_ = _args[15];
lean_object* v___x_2790_ = _args[16];
lean_object* v___x_2791_ = _args[17];
lean_object* v_usingTk_x3f_2792_ = _args[18];
lean_object* v_squeeze_2793_ = _args[19];
lean_object* v_unfold_2794_ = _args[20];
lean_object* v_args_2795_ = _args[21];
lean_object* v_only_2796_ = _args[22];
lean_object* v___y_2797_ = _args[23];
lean_object* v___y_2798_ = _args[24];
lean_object* v___y_2799_ = _args[25];
lean_object* v___y_2800_ = _args[26];
lean_object* v___y_2801_ = _args[27];
lean_object* v___y_2802_ = _args[28];
lean_object* v___y_2803_ = _args[29];
lean_object* v___y_2804_ = _args[30];
lean_object* v___y_2805_ = _args[31];
lean_object* v___y_2806_ = _args[32];
_start:
{
uint8_t v___x_82001__boxed_2807_; uint8_t v___x_82011__boxed_2808_; lean_object* v_res_2809_; 
v___x_82001__boxed_2807_ = lean_unbox(v___x_2780_);
v___x_82011__boxed_2808_ = lean_unbox(v___x_2791_);
v_res_2809_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(v_tk_2774_, v___x_2775_, v___x_2776_, v___x_2777_, v___x_2778_, v___x_2779_, v___x_82001__boxed_2807_, v___x_2781_, v___f_2782_, v___x_2783_, v___x_2784_, v___x_2785_, v___x_2786_, v___x_2787_, v___x_2788_, v_usingArg_2789_, v___x_2790_, v___x_82011__boxed_2808_, v_usingTk_x3f_2792_, v_squeeze_2793_, v_unfold_2794_, v_args_2795_, v_only_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v_only_2796_);
lean_dec(v_args_2795_);
lean_dec(v_unfold_2794_);
lean_dec(v_squeeze_2793_);
lean_dec(v___x_2787_);
lean_dec(v___x_2785_);
lean_dec(v___x_2784_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_stx_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2846_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0));
v___x_2847_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1));
v___x_2848_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_2849_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2));
v___x_2850_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
lean_inc(v_stx_2836_);
v___x_2851_ = l_Lean_Syntax_isOfKind(v_stx_2836_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; 
lean_dec(v_stx_2836_);
v___x_2852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2852_;
}
else
{
lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v_tk_2855_; lean_object* v___x_2856_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; uint8_t v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; uint8_t v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v_usingTk_x3f_2906_; lean_object* v_usingArg_2907_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v_args_2939_; uint8_t v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v_only_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v_unfold_2995_; lean_object* v_squeeze_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___f_2853_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4));
v___x_2854_ = lean_unsigned_to_nat(0u);
v_tk_2855_ = l_Lean_Syntax_getArg(v_stx_2836_, v___x_2854_);
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_3031_ = l_Lean_Syntax_getArg(v_stx_2836_, v___x_2856_);
v___x_3032_ = l_Lean_Syntax_isNone(v___x_3031_);
if (v___x_3032_ == 0)
{
uint8_t v___x_3033_; 
lean_inc(v___x_3031_);
v___x_3033_ = l_Lean_Syntax_matchesNull(v___x_3031_, v___x_2856_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; 
lean_dec(v___x_3031_);
lean_dec(v_tk_2855_);
lean_dec(v_stx_2836_);
v___x_3034_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3034_;
}
else
{
lean_object* v_squeeze_3035_; lean_object* v___x_3036_; 
v_squeeze_3035_ = l_Lean_Syntax_getArg(v___x_3031_, v___x_2854_);
lean_dec(v___x_3031_);
v___x_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3036_, 0, v_squeeze_3035_);
v_squeeze_3014_ = v___x_3036_;
v___y_3015_ = v_a_2837_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
v___y_3019_ = v_a_2841_;
v___y_3020_ = v_a_2842_;
v___y_3021_ = v_a_2843_;
v___y_3022_ = v_a_2844_;
goto v___jp_3013_;
}
}
else
{
lean_object* v___x_3037_; 
lean_dec(v___x_3031_);
v___x_3037_ = lean_box(0);
v_squeeze_3014_ = v___x_3037_;
v___y_3015_ = v_a_2837_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
v___y_3019_ = v_a_2841_;
v___y_3020_ = v_a_2842_;
v___y_3021_ = v_a_2843_;
v___y_3022_ = v_a_2844_;
goto v___jp_3013_;
}
v___jp_2857_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2880_ = lean_box(v___x_2851_);
v___x_2881_ = lean_box(v___y_2870_);
lean_inc(v___y_2877_);
lean_inc(v___y_2861_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 33, 24);
lean_closure_set(v___f_2882_, 0, v_tk_2855_);
lean_closure_set(v___f_2882_, 1, v___x_2846_);
lean_closure_set(v___f_2882_, 2, v___x_2847_);
lean_closure_set(v___f_2882_, 3, v___x_2848_);
lean_closure_set(v___f_2882_, 4, v___y_2861_);
lean_closure_set(v___f_2882_, 5, v___x_2854_);
lean_closure_set(v___f_2882_, 6, v___x_2880_);
lean_closure_set(v___f_2882_, 7, v___x_2850_);
lean_closure_set(v___f_2882_, 8, v___f_2853_);
lean_closure_set(v___f_2882_, 9, v___x_2849_);
lean_closure_set(v___f_2882_, 10, v___y_2875_);
lean_closure_set(v___f_2882_, 11, v___y_2862_);
lean_closure_set(v___f_2882_, 12, v___x_2856_);
lean_closure_set(v___f_2882_, 13, v___y_2877_);
lean_closure_set(v___f_2882_, 14, v___y_2867_);
lean_closure_set(v___f_2882_, 15, v___y_2872_);
lean_closure_set(v___f_2882_, 16, v___y_2874_);
lean_closure_set(v___f_2882_, 17, v___x_2881_);
lean_closure_set(v___f_2882_, 18, v___y_2864_);
lean_closure_set(v___f_2882_, 19, v___y_2866_);
lean_closure_set(v___f_2882_, 20, v___y_2868_);
lean_closure_set(v___f_2882_, 21, v___y_2863_);
lean_closure_set(v___f_2882_, 22, v___y_2876_);
lean_closure_set(v___f_2882_, 23, v___y_2879_);
v___x_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2883_, 0, v___f_2882_);
v___x_2884_ = l_Lean_Elab_Tactic_focus___redArg(v___x_2883_, v___y_2871_, v___y_2860_, v___y_2865_, v___y_2869_, v___y_2858_, v___y_2873_, v___y_2878_, v___y_2859_);
return v___x_2884_;
}
v___jp_2885_:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Syntax_getOptional_x3f(v___y_2894_);
lean_dec(v___y_2894_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_box(0);
v___y_2858_ = v___y_2886_;
v___y_2859_ = v___y_2887_;
v___y_2860_ = v___y_2888_;
v___y_2861_ = v___y_2889_;
v___y_2862_ = v___y_2890_;
v___y_2863_ = v___y_2891_;
v___y_2864_ = v_usingTk_x3f_2906_;
v___y_2865_ = v___y_2892_;
v___y_2866_ = v___y_2893_;
v___y_2867_ = v___y_2895_;
v___y_2868_ = v___y_2896_;
v___y_2869_ = v___y_2897_;
v___y_2870_ = v___y_2898_;
v___y_2871_ = v___y_2899_;
v___y_2872_ = v_usingArg_2907_;
v___y_2873_ = v___y_2900_;
v___y_2874_ = v___y_2901_;
v___y_2875_ = v___y_2903_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2904_;
v___y_2878_ = v___y_2905_;
v___y_2879_ = v___x_2909_;
goto v___jp_2857_;
}
else
{
lean_object* v_val_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v_val_2910_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2908_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_val_2910_);
lean_dec(v___x_2908_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_val_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
v___y_2858_ = v___y_2886_;
v___y_2859_ = v___y_2887_;
v___y_2860_ = v___y_2888_;
v___y_2861_ = v___y_2889_;
v___y_2862_ = v___y_2890_;
v___y_2863_ = v___y_2891_;
v___y_2864_ = v_usingTk_x3f_2906_;
v___y_2865_ = v___y_2892_;
v___y_2866_ = v___y_2893_;
v___y_2867_ = v___y_2895_;
v___y_2868_ = v___y_2896_;
v___y_2869_ = v___y_2897_;
v___y_2870_ = v___y_2898_;
v___y_2871_ = v___y_2899_;
v___y_2872_ = v_usingArg_2907_;
v___y_2873_ = v___y_2900_;
v___y_2874_ = v___y_2901_;
v___y_2875_ = v___y_2903_;
v___y_2876_ = v___y_2902_;
v___y_2877_ = v___y_2904_;
v___y_2878_ = v___y_2905_;
v___y_2879_ = v___x_2915_;
goto v___jp_2857_;
}
}
}
}
v___jp_2918_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2940_ = lean_unsigned_to_nat(4u);
v___x_2941_ = l_Lean_Syntax_getArg(v___y_2932_, v___x_2940_);
lean_dec(v___y_2932_);
v___x_2942_ = l_Lean_Syntax_isNone(v___x_2941_);
if (v___x_2942_ == 0)
{
uint8_t v___x_2943_; 
lean_inc(v___x_2941_);
v___x_2943_ = l_Lean_Syntax_matchesNull(v___x_2941_, v___y_2938_);
lean_dec(v___y_2938_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; 
lean_dec(v___x_2941_);
lean_dec(v_args_2939_);
lean_dec(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec(v___y_2923_);
lean_dec(v_tk_2855_);
v___x_2944_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2944_;
}
else
{
lean_object* v_usingTk_x3f_2945_; lean_object* v_usingArg_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_usingTk_x3f_2945_ = l_Lean_Syntax_getArg(v___x_2941_, v___x_2854_);
v_usingArg_2946_ = l_Lean_Syntax_getArg(v___x_2941_, v___x_2856_);
lean_dec(v___x_2941_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_usingTk_x3f_2945_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_usingArg_2946_);
v___y_2886_ = v___y_2919_;
v___y_2887_ = v___y_2920_;
v___y_2888_ = v___y_2921_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v_args_2939_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2927_;
v___y_2896_ = v___y_2928_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___y_2930_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2934_;
v___y_2902_ = v___y_2935_;
v___y_2903_ = v___x_2940_;
v___y_2904_ = v___y_2936_;
v___y_2905_ = v___y_2937_;
v_usingTk_x3f_2906_ = v___x_2947_;
v_usingArg_2907_ = v___x_2948_;
goto v___jp_2885_;
}
}
else
{
lean_object* v___x_2949_; 
lean_dec(v___x_2941_);
lean_dec(v___y_2938_);
v___x_2949_ = lean_box(0);
v___y_2886_ = v___y_2919_;
v___y_2887_ = v___y_2920_;
v___y_2888_ = v___y_2921_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v_args_2939_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2927_;
v___y_2896_ = v___y_2928_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___y_2930_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2934_;
v___y_2902_ = v___y_2935_;
v___y_2903_ = v___x_2940_;
v___y_2904_ = v___y_2936_;
v___y_2905_ = v___y_2937_;
v_usingTk_x3f_2906_ = v___x_2949_;
v_usingArg_2907_ = v___x_2949_;
goto v___jp_2885_;
}
}
v___jp_2950_:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = l_Lean_Syntax_getArg(v___y_2960_, v___y_2959_);
lean_dec(v___y_2959_);
v___x_2973_ = l_Lean_Syntax_isNone(v___x_2972_);
if (v___x_2973_ == 0)
{
uint8_t v___x_2974_; 
lean_inc(v___x_2972_);
v___x_2974_ = l_Lean_Syntax_matchesNull(v___x_2972_, v___x_2856_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
lean_dec(v___x_2972_);
lean_dec(v_only_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec(v_tk_2855_);
v___x_2975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = l_Lean_Syntax_getArg(v___x_2972_, v___x_2854_);
lean_dec(v___x_2972_);
v___x_2977_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5));
lean_inc(v___x_2976_);
v___x_2978_ = l_Lean_Syntax_isOfKind(v___x_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec(v___x_2976_);
lean_dec(v_only_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec(v_tk_2855_);
v___x_2979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; lean_object* v_args_2981_; lean_object* v___x_2982_; 
v___x_2980_ = l_Lean_Syntax_getArg(v___x_2976_, v___x_2856_);
lean_dec(v___x_2976_);
v_args_2981_ = l_Lean_Syntax_getArgs(v___x_2980_);
lean_dec(v___x_2980_);
v___x_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_args_2981_);
v___y_2919_ = v___y_2968_;
v___y_2920_ = v___y_2971_;
v___y_2921_ = v___y_2965_;
v___y_2922_ = v___y_2953_;
v___y_2923_ = v___y_2952_;
v___y_2924_ = v___y_2966_;
v___y_2925_ = v___y_2955_;
v___y_2926_ = v___y_2961_;
v___y_2927_ = v___y_2958_;
v___y_2928_ = v___y_2957_;
v___y_2929_ = v___y_2967_;
v___y_2930_ = v___y_2951_;
v___y_2931_ = v___y_2964_;
v___y_2932_ = v___y_2960_;
v___y_2933_ = v___y_2969_;
v___y_2934_ = v___y_2954_;
v___y_2935_ = v_only_2963_;
v___y_2936_ = v___y_2956_;
v___y_2937_ = v___y_2970_;
v___y_2938_ = v___y_2962_;
v_args_2939_ = v___x_2982_;
goto v___jp_2918_;
}
}
}
else
{
lean_object* v___x_2983_; 
lean_dec(v___x_2972_);
v___x_2983_ = lean_box(0);
v___y_2919_ = v___y_2968_;
v___y_2920_ = v___y_2971_;
v___y_2921_ = v___y_2965_;
v___y_2922_ = v___y_2953_;
v___y_2923_ = v___y_2952_;
v___y_2924_ = v___y_2966_;
v___y_2925_ = v___y_2955_;
v___y_2926_ = v___y_2961_;
v___y_2927_ = v___y_2958_;
v___y_2928_ = v___y_2957_;
v___y_2929_ = v___y_2967_;
v___y_2930_ = v___y_2951_;
v___y_2931_ = v___y_2964_;
v___y_2932_ = v___y_2960_;
v___y_2933_ = v___y_2969_;
v___y_2934_ = v___y_2954_;
v___y_2935_ = v_only_2963_;
v___y_2936_ = v___y_2956_;
v___y_2937_ = v___y_2970_;
v___y_2938_ = v___y_2962_;
v_args_2939_ = v___x_2983_;
goto v___jp_2918_;
}
}
v___jp_2984_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2996_ = lean_unsigned_to_nat(3u);
v___x_2997_ = l_Lean_Syntax_getArg(v_stx_2836_, v___x_2996_);
lean_dec(v_stx_2836_);
v___x_2998_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7));
lean_inc(v___x_2997_);
v___x_2999_ = l_Lean_Syntax_isOfKind(v___x_2997_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v___x_2997_);
lean_dec(v_unfold_2995_);
lean_dec(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec(v_tk_2855_);
v___x_3000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3001_ = l_Lean_Syntax_getArg(v___x_2997_, v___x_2854_);
v___x_3002_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9));
lean_inc(v___x_3001_);
v___x_3003_ = l_Lean_Syntax_isOfKind(v___x_3001_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; 
lean_dec(v___x_3001_);
lean_dec(v___x_2997_);
lean_dec(v_unfold_2995_);
lean_dec(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec(v_tk_2855_);
v___x_3004_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3005_ = l_Lean_Syntax_getArg(v___x_2997_, v___x_2856_);
v___x_3006_ = l_Lean_Syntax_getArg(v___x_2997_, v___y_2994_);
v___x_3007_ = l_Lean_Syntax_isNone(v___x_3006_);
if (v___x_3007_ == 0)
{
uint8_t v___x_3008_; 
lean_inc(v___x_3006_);
v___x_3008_ = l_Lean_Syntax_matchesNull(v___x_3006_, v___x_2856_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
lean_dec(v___x_3006_);
lean_dec(v___x_3005_);
lean_dec(v___x_3001_);
lean_dec(v___x_2997_);
lean_dec(v_unfold_2995_);
lean_dec(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec(v_tk_2855_);
v___x_3009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3009_;
}
else
{
lean_object* v_only_3010_; lean_object* v___x_3011_; 
v_only_3010_ = l_Lean_Syntax_getArg(v___x_3006_, v___x_2854_);
lean_dec(v___x_3006_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_only_3010_);
lean_inc(v___y_2994_);
v___y_2951_ = v___x_3003_;
v___y_2952_ = v___x_2996_;
v___y_2953_ = v___x_2998_;
v___y_2954_ = v___x_3001_;
v___y_2955_ = v___y_2993_;
v___y_2956_ = v___x_3002_;
v___y_2957_ = v_unfold_2995_;
v___y_2958_ = v___y_2994_;
v___y_2959_ = v___x_2996_;
v___y_2960_ = v___x_2997_;
v___y_2961_ = v___x_3005_;
v___y_2962_ = v___y_2994_;
v_only_2963_ = v___x_3011_;
v___y_2964_ = v___y_2992_;
v___y_2965_ = v___y_2988_;
v___y_2966_ = v___y_2990_;
v___y_2967_ = v___y_2989_;
v___y_2968_ = v___y_2985_;
v___y_2969_ = v___y_2987_;
v___y_2970_ = v___y_2986_;
v___y_2971_ = v___y_2991_;
goto v___jp_2950_;
}
}
else
{
lean_object* v___x_3012_; 
lean_dec(v___x_3006_);
v___x_3012_ = lean_box(0);
lean_inc(v___y_2994_);
v___y_2951_ = v___x_3003_;
v___y_2952_ = v___x_2996_;
v___y_2953_ = v___x_2998_;
v___y_2954_ = v___x_3001_;
v___y_2955_ = v___y_2993_;
v___y_2956_ = v___x_3002_;
v___y_2957_ = v_unfold_2995_;
v___y_2958_ = v___y_2994_;
v___y_2959_ = v___x_2996_;
v___y_2960_ = v___x_2997_;
v___y_2961_ = v___x_3005_;
v___y_2962_ = v___y_2994_;
v_only_2963_ = v___x_3012_;
v___y_2964_ = v___y_2992_;
v___y_2965_ = v___y_2988_;
v___y_2966_ = v___y_2990_;
v___y_2967_ = v___y_2989_;
v___y_2968_ = v___y_2985_;
v___y_2969_ = v___y_2987_;
v___y_2970_ = v___y_2986_;
v___y_2971_ = v___y_2991_;
goto v___jp_2950_;
}
}
}
}
v___jp_3013_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3023_ = lean_unsigned_to_nat(2u);
v___x_3024_ = l_Lean_Syntax_getArg(v_stx_2836_, v___x_3023_);
v___x_3025_ = l_Lean_Syntax_isNone(v___x_3024_);
if (v___x_3025_ == 0)
{
uint8_t v___x_3026_; 
lean_inc(v___x_3024_);
v___x_3026_ = l_Lean_Syntax_matchesNull(v___x_3024_, v___x_2856_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
lean_dec(v___x_3024_);
lean_dec(v_squeeze_3014_);
lean_dec(v_tk_2855_);
lean_dec(v_stx_2836_);
v___x_3027_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3027_;
}
else
{
lean_object* v_unfold_3028_; lean_object* v___x_3029_; 
v_unfold_3028_ = l_Lean_Syntax_getArg(v___x_3024_, v___x_2854_);
lean_dec(v___x_3024_);
v___x_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_unfold_3028_);
v___y_2985_ = v___y_3019_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3020_;
v___y_2988_ = v___y_3016_;
v___y_2989_ = v___y_3018_;
v___y_2990_ = v___y_3017_;
v___y_2991_ = v___y_3022_;
v___y_2992_ = v___y_3015_;
v___y_2993_ = v_squeeze_3014_;
v___y_2994_ = v___x_3023_;
v_unfold_2995_ = v___x_3029_;
goto v___jp_2984_;
}
}
else
{
lean_object* v___x_3030_; 
lean_dec(v___x_3024_);
v___x_3030_ = lean_box(0);
v___y_2985_ = v___y_3019_;
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3020_;
v___y_2988_ = v___y_3016_;
v___y_2989_ = v___y_3018_;
v___y_2990_ = v___y_3017_;
v___y_2991_ = v___y_3022_;
v___y_2992_ = v___y_3015_;
v___y_2993_ = v_squeeze_3014_;
v___y_2994_ = v___x_3023_;
v_unfold_2995_ = v___x_3030_;
goto v___jp_2984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_stx_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_stx_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(lean_object* v_mvarId_3049_, lean_object* v_val_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_3049_, v_val_3050_, v___y_3056_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___boxed(lean_object* v_mvarId_3061_, lean_object* v_val_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(v_mvarId_3061_, v_val_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(lean_object* v_o_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_o_3073_, v___y_3081_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___boxed(lean_object* v_o_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(v_o_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(lean_object* v_00_u03b1_3095_, lean_object* v_msg_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v_msg_3096_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___boxed(lean_object* v_00_u03b1_3107_, lean_object* v_msg_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(v_00_u03b1_3107_, v_msg_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(lean_object* v_00_u03b1_3119_, lean_object* v_x_3120_, lean_object* v_mkInfoTree_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v_x_3120_, v_mkInfoTree_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_x_3133_, lean_object* v_mkInfoTree_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(v_00_u03b1_3132_, v_x_3133_, v_mkInfoTree_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3(lean_object* v_00_u03b2_3145_, lean_object* v_x_3146_, lean_object* v_x_3147_, lean_object* v_x_3148_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_x_3146_, v_x_3147_, v_x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3150_, lean_object* v_m_3151_, lean_object* v_a_3152_){
_start:
{
uint8_t v___x_3153_; 
v___x_3153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_m_3151_, v_a_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3154_, lean_object* v_m_3155_, lean_object* v_a_3156_){
_start:
{
uint8_t v_res_3157_; lean_object* v_r_3158_; 
v_res_3157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(v_00_u03b2_3154_, v_m_3155_, v_a_3156_);
lean_dec_ref(v_a_3156_);
lean_dec_ref(v_m_3155_);
v_r_3158_ = lean_box(v_res_3157_);
return v_r_3158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3159_, lean_object* v_m_3160_, lean_object* v_a_3161_, lean_object* v_b_3162_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(v_m_3160_, v_a_3161_, v_b_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3164_, v___y_3165_, v___y_3171_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(v_mvarId_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v_mvarId_3176_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3188_, v___y_3189_, v___y_3195_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(v_mvarId_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v_mvarId_3200_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3212_, lean_object* v_x_3213_, size_t v_x_3214_, size_t v_x_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_3213_, v_x_3214_, v_x_3215_, v_x_3216_, v_x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_, lean_object* v_x_3224_){
_start:
{
size_t v_x_83791__boxed_3225_; size_t v_x_83792__boxed_3226_; lean_object* v_res_3227_; 
v_x_83791__boxed_3225_ = lean_unbox_usize(v_x_3221_);
lean_dec(v_x_3221_);
v_x_83792__boxed_3226_ = lean_unbox_usize(v_x_3222_);
lean_dec(v_x_3222_);
v_res_3227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(v_00_u03b2_3219_, v_x_3220_, v_x_83791__boxed_3225_, v_x_83792__boxed_3226_, v_x_3223_, v_x_3224_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(lean_object* v_ref_3228_, lean_object* v_msgData_3229_, uint8_t v_severity_3230_, uint8_t v_isSilent_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_3228_, v_msgData_3229_, v_severity_3230_, v_isSilent_3231_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3242_, lean_object* v_msgData_3243_, lean_object* v_severity_3244_, lean_object* v_isSilent_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
uint8_t v_severity_boxed_3255_; uint8_t v_isSilent_boxed_3256_; lean_object* v_res_3257_; 
v_severity_boxed_3255_ = lean_unbox(v_severity_3244_);
v_isSilent_boxed_3256_ = lean_unbox(v_isSilent_3245_);
v_res_3257_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(v_ref_3242_, v_msgData_3243_, v_severity_boxed_3255_, v_isSilent_boxed_3256_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v_ref_3242_);
return v_res_3257_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3258_, lean_object* v_a_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3259_, v_x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3262_, lean_object* v_a_3263_, lean_object* v_x_3264_){
_start:
{
uint8_t v_res_3265_; lean_object* v_r_3266_; 
v_res_3265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3262_, v_a_3263_, v_x_3264_);
lean_dec(v_x_3264_);
lean_dec_ref(v_a_3263_);
v_r_3266_ = lean_box(v_res_3265_);
return v_r_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3267_, lean_object* v_data_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3270_, lean_object* v_n_3271_, lean_object* v_k_3272_, lean_object* v_v_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3271_, v_k_3272_, v_v_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3275_, size_t v_depth_3276_, lean_object* v_keys_3277_, lean_object* v_vals_3278_, lean_object* v_heq_3279_, lean_object* v_i_3280_, lean_object* v_entries_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3276_, v_keys_3277_, v_vals_3278_, v_i_3280_, v_entries_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3283_, lean_object* v_depth_3284_, lean_object* v_keys_3285_, lean_object* v_vals_3286_, lean_object* v_heq_3287_, lean_object* v_i_3288_, lean_object* v_entries_3289_){
_start:
{
size_t v_depth_boxed_3290_; lean_object* v_res_3291_; 
v_depth_boxed_3290_ = lean_unbox_usize(v_depth_3284_);
lean_dec(v_depth_3284_);
v_res_3291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3283_, v_depth_boxed_3290_, v_keys_3285_, v_vals_3286_, v_heq_3287_, v_i_3288_, v_entries_3289_);
lean_dec_ref(v_vals_3286_);
lean_dec_ref(v_keys_3285_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3292_, lean_object* v_i_3293_, lean_object* v_source_3294_, lean_object* v_target_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3293_, v_source_3294_, v_target_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3298_, v_x_3299_, v_x_3300_, v_x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3304_, v_x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3316_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3317_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
v___x_3318_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3319_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3320_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3316_, v___x_3317_, v___x_3318_, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3350_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3351_ = l_Lean_addBuiltinDeclarationRanges(v___x_3349_, v___x_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3353_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_linter_unnecessarySimpa = lean_io_result_get_value(res);
lean_mark_persistent(l_linter_unnecessarySimpa);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Simpa(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Simpa(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Simpa(builtin);
}
#ifdef __cplusplus
}
#endif
