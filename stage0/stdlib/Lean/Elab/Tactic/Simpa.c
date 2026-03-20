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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
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
v___x_101_ = lean_apply_9(v_x_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, lean_box(0));
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0___boxed(lean_object* v_x_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0(v_x_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(lean_object* v_mvarId_113_, lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___f_124_; lean_object* v___x_125_; 
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
lean_object* v___f_251_; lean_object* v___x_67668__overap_252_; lean_object* v___x_253_; 
v___f_251_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___closed__0));
v___x_67668__overap_252_ = lean_panic_fn(v___f_251_, v_msg_241_);
v___x_253_ = lean_apply_9(v___x_67668__overap_252_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, lean_box(0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___boxed(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
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
lean_inc(v_a_368_);
lean_dec_ref(v___x_367_);
v___x_369_ = lean_mk_syntax_ident(v_a_350_);
lean_inc(v_a_368_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_a_368_);
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
v___x_371_ = l_Lean_Elab_Term_elabTerm(v___x_369_, v___x_370_, v___x_351_, v___x_351_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_406_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
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
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_362_);
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
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
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
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc(v_a_411_);
lean_inc(v_a_368_);
v___x_460_ = l_Lean_Meta_isExprDefEq(v_a_368_, v_a_411_, v___x_459_, v___y_363_, v___y_364_, v___y_365_);
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
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
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
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
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
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
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
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc_ref(v___y_378_);
lean_inc(v___y_377_);
lean_inc_ref(v___y_376_);
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
return v___x_389_;
}
else
{
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
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
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
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
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
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
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
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
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
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
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
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
uint8_t v___x_79966__boxed_519_; uint8_t v___x_79967__boxed_520_; uint8_t v___x_79968__boxed_521_; lean_object* v_res_522_; 
v___x_79966__boxed_519_ = lean_unbox(v___x_503_);
v___x_79967__boxed_520_ = lean_unbox(v___x_504_);
v___x_79968__boxed_521_ = lean_unbox(v___x_505_);
v_res_522_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(v_a_501_, v_a_502_, v___x_79966__boxed_519_, v___x_79967__boxed_520_, v___x_79968__boxed_521_, v_a_506_, v_mvarCounter_507_, v___x_508_, v___x_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
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
size_t v_x_81188__boxed_1182_; size_t v_x_81189__boxed_1183_; lean_object* v_res_1184_; 
v_x_81188__boxed_1182_ = lean_unbox_usize(v_x_1178_);
lean_dec(v_x_1178_);
v_x_81189__boxed_1183_ = lean_unbox_usize(v_x_1179_);
lean_dec(v_x_1179_);
v_res_1184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_1177_, v_x_81188__boxed_1182_, v_x_81189__boxed_1183_, v_x_1180_, v_x_1181_);
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
lean_object* v___x_1196_; lean_object* v_mctx_1197_; lean_object* v_cache_1198_; lean_object* v_zetaDeltaFVarIds_1199_; lean_object* v_postponed_1200_; lean_object* v_diag_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1228_; 
v___x_1196_ = lean_st_ref_take(v___y_1194_);
v_mctx_1197_ = lean_ctor_get(v___x_1196_, 0);
v_cache_1198_ = lean_ctor_get(v___x_1196_, 1);
v_zetaDeltaFVarIds_1199_ = lean_ctor_get(v___x_1196_, 2);
v_postponed_1200_ = lean_ctor_get(v___x_1196_, 3);
v_diag_1201_ = lean_ctor_get(v___x_1196_, 4);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1203_ = v___x_1196_;
v_isShared_1204_ = v_isSharedCheck_1228_;
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
v_isShared_1204_ = v_isSharedCheck_1228_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_depth_1205_; lean_object* v_levelAssignDepth_1206_; lean_object* v_mvarCounter_1207_; lean_object* v_lDepth_1208_; lean_object* v_decls_1209_; lean_object* v_userNames_1210_; lean_object* v_lAssignment_1211_; lean_object* v_eAssignment_1212_; lean_object* v_dAssignment_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1227_; 
v_depth_1205_ = lean_ctor_get(v_mctx_1197_, 0);
v_levelAssignDepth_1206_ = lean_ctor_get(v_mctx_1197_, 1);
v_mvarCounter_1207_ = lean_ctor_get(v_mctx_1197_, 2);
v_lDepth_1208_ = lean_ctor_get(v_mctx_1197_, 3);
v_decls_1209_ = lean_ctor_get(v_mctx_1197_, 4);
v_userNames_1210_ = lean_ctor_get(v_mctx_1197_, 5);
v_lAssignment_1211_ = lean_ctor_get(v_mctx_1197_, 6);
v_eAssignment_1212_ = lean_ctor_get(v_mctx_1197_, 7);
v_dAssignment_1213_ = lean_ctor_get(v_mctx_1197_, 8);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_mctx_1197_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1215_ = v_mctx_1197_;
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_dAssignment_1213_);
lean_inc(v_eAssignment_1212_);
lean_inc(v_lAssignment_1211_);
lean_inc(v_userNames_1210_);
lean_inc(v_decls_1209_);
lean_inc(v_lDepth_1208_);
lean_inc(v_mvarCounter_1207_);
lean_inc(v_levelAssignDepth_1206_);
lean_inc(v_depth_1205_);
lean_dec(v_mctx_1197_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1227_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_eAssignment_1212_, v_mvarId_1192_, v_val_1193_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 7, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_depth_1205_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_levelAssignDepth_1206_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_mvarCounter_1207_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_lDepth_1208_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v_decls_1209_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v_userNames_1210_);
lean_ctor_set(v_reuseFailAlloc_1226_, 6, v_lAssignment_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 7, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1226_, 8, v_dAssignment_1213_);
v___x_1219_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1219_);
v___x_1221_ = v___x_1203_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_cache_1198_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_zetaDeltaFVarIds_1199_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_postponed_1200_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_diag_1201_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_st_ref_set(v___y_1194_, v___x_1221_);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg___boxed(lean_object* v_mvarId_1229_, lean_object* v_val_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_1229_, v_val_1230_, v___y_1231_);
lean_dec(v___y_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1242_, uint8_t v_suppressElabErrors_1243_, lean_object* v_x_1244_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 1)
{
lean_object* v_pre_1245_; 
v_pre_1245_ = lean_ctor_get(v_x_1244_, 0);
switch(lean_obj_tag(v_pre_1245_))
{
case 1:
{
lean_object* v_pre_1246_; 
v_pre_1246_ = lean_ctor_get(v_pre_1245_, 0);
switch(lean_obj_tag(v_pre_1246_))
{
case 0:
{
lean_object* v_str_1247_; lean_object* v_str_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_str_1247_ = lean_ctor_get(v_x_1244_, 1);
v_str_1248_ = lean_ctor_get(v_pre_1245_, 1);
v___x_1249_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1250_ = lean_string_dec_eq(v_str_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1252_ = lean_string_dec_eq(v_str_1248_, v___x_1251_);
if (v___x_1252_ == 0)
{
return v___y_1242_;
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1254_ = lean_string_dec_eq(v_str_1247_, v___x_1253_);
if (v___x_1254_ == 0)
{
return v___y_1242_;
}
else
{
return v_suppressElabErrors_1243_;
}
}
}
else
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1256_ = lean_string_dec_eq(v_str_1247_, v___x_1255_);
if (v___x_1256_ == 0)
{
return v___y_1242_;
}
else
{
return v_suppressElabErrors_1243_;
}
}
}
case 1:
{
lean_object* v_pre_1257_; 
v_pre_1257_ = lean_ctor_get(v_pre_1246_, 0);
if (lean_obj_tag(v_pre_1257_) == 0)
{
lean_object* v_str_1258_; lean_object* v_str_1259_; lean_object* v_str_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_str_1258_ = lean_ctor_get(v_x_1244_, 1);
v_str_1259_ = lean_ctor_get(v_pre_1245_, 1);
v_str_1260_ = lean_ctor_get(v_pre_1246_, 1);
v___x_1261_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1262_ = lean_string_dec_eq(v_str_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
return v___y_1242_;
}
else
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1264_ = lean_string_dec_eq(v_str_1259_, v___x_1263_);
if (v___x_1264_ == 0)
{
return v___y_1242_;
}
else
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1266_ = lean_string_dec_eq(v_str_1258_, v___x_1265_);
if (v___x_1266_ == 0)
{
return v___y_1242_;
}
else
{
return v_suppressElabErrors_1243_;
}
}
}
}
else
{
return v___y_1242_;
}
}
default: 
{
return v___y_1242_;
}
}
}
case 0:
{
lean_object* v_str_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_str_1267_ = lean_ctor_get(v_x_1244_, 1);
v___x_1268_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1269_ = lean_string_dec_eq(v_str_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
return v___y_1242_;
}
else
{
return v_suppressElabErrors_1243_;
}
}
default: 
{
return v___y_1242_;
}
}
}
else
{
return v___y_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1270_, lean_object* v_suppressElabErrors_1271_, lean_object* v_x_1272_){
_start:
{
uint8_t v___y_81423__boxed_1273_; uint8_t v_suppressElabErrors_boxed_1274_; uint8_t v_res_1275_; lean_object* v_r_1276_; 
v___y_81423__boxed_1273_ = lean_unbox(v___y_1270_);
v_suppressElabErrors_boxed_1274_ = lean_unbox(v_suppressElabErrors_1271_);
v_res_1275_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(v___y_81423__boxed_1273_, v_suppressElabErrors_boxed_1274_, v_x_1272_);
lean_dec(v_x_1272_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1278_, lean_object* v_msgData_1279_, uint8_t v_severity_1280_, uint8_t v_isSilent_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; uint8_t v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1324_; lean_object* v___y_1325_; uint8_t v___y_1326_; uint8_t v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; uint8_t v___x_1371_; lean_object* v___y_1373_; lean_object* v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; uint8_t v___y_1379_; uint8_t v___y_1381_; uint8_t v___x_1396_; 
v___x_1371_ = 2;
v___x_1396_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1280_, v___x_1371_);
if (v___x_1396_ == 0)
{
v___y_1381_ = v___x_1396_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1397_; 
lean_inc_ref(v_msgData_1279_);
v___x_1397_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1279_);
v___y_1381_ = v___x_1397_;
goto v___jp_1380_;
}
v___jp_1287_:
{
lean_object* v___x_1297_; lean_object* v_currNamespace_1298_; lean_object* v_openDecls_1299_; lean_object* v_env_1300_; lean_object* v_nextMacroScope_1301_; lean_object* v_ngen_1302_; lean_object* v_auxDeclNGen_1303_; lean_object* v_traceState_1304_; lean_object* v_cache_1305_; lean_object* v_messages_1306_; lean_object* v_infoState_1307_; lean_object* v_snapshotTasks_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1322_; 
v___x_1297_ = lean_st_ref_take(v___y_1296_);
v_currNamespace_1298_ = lean_ctor_get(v___y_1295_, 6);
lean_inc(v_currNamespace_1298_);
v_openDecls_1299_ = lean_ctor_get(v___y_1295_, 7);
lean_inc(v_openDecls_1299_);
lean_dec_ref(v___y_1295_);
v_env_1300_ = lean_ctor_get(v___x_1297_, 0);
v_nextMacroScope_1301_ = lean_ctor_get(v___x_1297_, 1);
v_ngen_1302_ = lean_ctor_get(v___x_1297_, 2);
v_auxDeclNGen_1303_ = lean_ctor_get(v___x_1297_, 3);
v_traceState_1304_ = lean_ctor_get(v___x_1297_, 4);
v_cache_1305_ = lean_ctor_get(v___x_1297_, 5);
v_messages_1306_ = lean_ctor_get(v___x_1297_, 6);
v_infoState_1307_ = lean_ctor_get(v___x_1297_, 7);
v_snapshotTasks_1308_ = lean_ctor_get(v___x_1297_, 8);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1310_ = v___x_1297_;
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_snapshotTasks_1308_);
lean_inc(v_infoState_1307_);
lean_inc(v_messages_1306_);
lean_inc(v_cache_1305_);
lean_inc(v_traceState_1304_);
lean_inc(v_auxDeclNGen_1303_);
lean_inc(v_ngen_1302_);
lean_inc(v_nextMacroScope_1301_);
lean_inc(v_env_1300_);
lean_dec(v___x_1297_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v_currNamespace_1298_);
lean_ctor_set(v___x_1312_, 1, v_openDecls_1299_);
v___x_1313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___y_1291_);
v___x_1314_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1314_, 0, v___y_1288_);
lean_ctor_set(v___x_1314_, 1, v___y_1293_);
lean_ctor_set(v___x_1314_, 2, v___y_1289_);
lean_ctor_set(v___x_1314_, 3, v___y_1294_);
lean_ctor_set(v___x_1314_, 4, v___x_1313_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5, v___y_1292_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5 + 1, v___y_1290_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5 + 2, v_isSilent_1281_);
v___x_1315_ = l_Lean_MessageLog_add(v___x_1314_, v_messages_1306_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 6, v___x_1315_);
v___x_1317_ = v___x_1310_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_env_1300_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1301_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1302_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1303_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_traceState_1304_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_cache_1305_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_infoState_1307_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_snapshotTasks_1308_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_st_ref_set(v___y_1296_, v___x_1317_);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
v___jp_1323_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1347_; 
v___x_1332_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1279_);
v___x_1333_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v___x_1332_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1347_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1347_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_inc_ref(v___y_1329_);
v___x_1338_ = l_Lean_FileMap_toPosition(v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
v___x_1339_ = l_Lean_FileMap_toPosition(v___y_1329_, v___y_1331_);
lean_dec(v___y_1331_);
v___x_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
v___x_1341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1328_ == 0)
{
lean_del_object(v___x_1336_);
lean_dec_ref(v___y_1324_);
v___y_1288_ = v___y_1325_;
v___y_1289_ = v___x_1340_;
v___y_1290_ = v___y_1326_;
v___y_1291_ = v_a_1334_;
v___y_1292_ = v___y_1327_;
v___y_1293_ = v___x_1338_;
v___y_1294_ = v___x_1341_;
v___y_1295_ = v___y_1284_;
v___y_1296_ = v___y_1285_;
goto v___jp_1287_;
}
else
{
uint8_t v___x_1342_; 
lean_inc(v_a_1334_);
v___x_1342_ = l_Lean_MessageData_hasTag(v___y_1324_, v_a_1334_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1338_);
lean_dec(v_a_1334_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v___y_1284_);
v___x_1343_ = lean_box(0);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1343_);
v___x_1345_ = v___x_1336_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
else
{
lean_del_object(v___x_1336_);
v___y_1288_ = v___y_1325_;
v___y_1289_ = v___x_1340_;
v___y_1290_ = v___y_1326_;
v___y_1291_ = v_a_1334_;
v___y_1292_ = v___y_1327_;
v___y_1293_ = v___x_1338_;
v___y_1294_ = v___x_1341_;
v___y_1295_ = v___y_1284_;
v___y_1296_ = v___y_1285_;
goto v___jp_1287_;
}
}
}
}
v___jp_1348_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Syntax_getTailPos_x3f(v___y_1353_, v___y_1352_);
lean_dec(v___y_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_inc(v___y_1356_);
v___y_1324_ = v___y_1349_;
v___y_1325_ = v___y_1350_;
v___y_1326_ = v___y_1351_;
v___y_1327_ = v___y_1352_;
v___y_1328_ = v___y_1354_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v___y_1356_;
goto v___jp_1323_;
}
else
{
lean_object* v_val_1358_; 
v_val_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_val_1358_);
lean_dec_ref(v___x_1357_);
v___y_1324_ = v___y_1349_;
v___y_1325_ = v___y_1350_;
v___y_1326_ = v___y_1351_;
v___y_1327_ = v___y_1352_;
v___y_1328_ = v___y_1354_;
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1356_;
v___y_1331_ = v_val_1358_;
goto v___jp_1323_;
}
}
v___jp_1359_:
{
lean_object* v_ref_1367_; lean_object* v___x_1368_; 
v_ref_1367_ = l_Lean_replaceRef(v_ref_1278_, v___y_1362_);
lean_dec(v___y_1362_);
v___x_1368_ = l_Lean_Syntax_getPos_x3f(v_ref_1367_, v___y_1363_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___y_1349_ = v___y_1360_;
v___y_1350_ = v___y_1361_;
v___y_1351_ = v___y_1366_;
v___y_1352_ = v___y_1363_;
v___y_1353_ = v_ref_1367_;
v___y_1354_ = v___y_1364_;
v___y_1355_ = v___y_1365_;
v___y_1356_ = v___x_1369_;
goto v___jp_1348_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1370_);
lean_dec_ref(v___x_1368_);
v___y_1349_ = v___y_1360_;
v___y_1350_ = v___y_1361_;
v___y_1351_ = v___y_1366_;
v___y_1352_ = v___y_1363_;
v___y_1353_ = v_ref_1367_;
v___y_1354_ = v___y_1364_;
v___y_1355_ = v___y_1365_;
v___y_1356_ = v_val_1370_;
goto v___jp_1348_;
}
}
v___jp_1372_:
{
if (v___y_1379_ == 0)
{
v___y_1360_ = v___y_1376_;
v___y_1361_ = v___y_1373_;
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1378_;
v___y_1364_ = v___y_1375_;
v___y_1365_ = v___y_1377_;
v___y_1366_ = v_severity_1280_;
goto v___jp_1359_;
}
else
{
v___y_1360_ = v___y_1376_;
v___y_1361_ = v___y_1373_;
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1378_;
v___y_1364_ = v___y_1375_;
v___y_1365_ = v___y_1377_;
v___y_1366_ = v___x_1371_;
goto v___jp_1359_;
}
}
v___jp_1380_:
{
if (v___y_1381_ == 0)
{
lean_object* v_fileName_1382_; lean_object* v_fileMap_1383_; lean_object* v_options_1384_; lean_object* v_ref_1385_; uint8_t v_suppressElabErrors_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___f_1389_; uint8_t v___x_1390_; uint8_t v___x_1391_; 
v_fileName_1382_ = lean_ctor_get(v___y_1284_, 0);
v_fileMap_1383_ = lean_ctor_get(v___y_1284_, 1);
v_options_1384_ = lean_ctor_get(v___y_1284_, 2);
v_ref_1385_ = lean_ctor_get(v___y_1284_, 5);
v_suppressElabErrors_1386_ = lean_ctor_get_uint8(v___y_1284_, sizeof(void*)*14 + 1);
v___x_1387_ = lean_box(v___y_1381_);
v___x_1388_ = lean_box(v_suppressElabErrors_1386_);
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1389_, 0, v___x_1387_);
lean_closure_set(v___f_1389_, 1, v___x_1388_);
v___x_1390_ = 1;
v___x_1391_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1280_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_inc_ref(v_fileMap_1383_);
lean_inc(v_ref_1385_);
lean_inc_ref(v_fileName_1382_);
v___y_1373_ = v_fileName_1382_;
v___y_1374_ = v_ref_1385_;
v___y_1375_ = v_suppressElabErrors_1386_;
v___y_1376_ = v___f_1389_;
v___y_1377_ = v_fileMap_1383_;
v___y_1378_ = v___y_1381_;
v___y_1379_ = v___x_1391_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = l_Lean_warningAsError;
v___x_1393_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_1384_, v___x_1392_);
lean_inc_ref(v_fileMap_1383_);
lean_inc(v_ref_1385_);
lean_inc_ref(v_fileName_1382_);
v___y_1373_ = v_fileName_1382_;
v___y_1374_ = v_ref_1385_;
v___y_1375_ = v_suppressElabErrors_1386_;
v___y_1376_ = v___f_1389_;
v___y_1377_ = v_fileMap_1383_;
v___y_1378_ = v___y_1381_;
v___y_1379_ = v___x_1393_;
goto v___jp_1372_;
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v___y_1284_);
lean_dec_ref(v_msgData_1279_);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1398_, lean_object* v_msgData_1399_, lean_object* v_severity_1400_, lean_object* v_isSilent_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v_severity_boxed_1407_; uint8_t v_isSilent_boxed_1408_; lean_object* v_res_1409_; 
v_severity_boxed_1407_ = lean_unbox(v_severity_1400_);
v_isSilent_boxed_1408_ = lean_unbox(v_isSilent_1401_);
v_res_1409_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_1398_, v_msgData_1399_, v_severity_boxed_1407_, v_isSilent_boxed_1408_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v_ref_1398_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(lean_object* v_ref_1410_, lean_object* v_msgData_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = 1;
v___x_1422_ = 0;
v___x_1423_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_1410_, v_msgData_1411_, v___x_1421_, v___x_1422_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7___boxed(lean_object* v_ref_1424_, lean_object* v_msgData_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(v_ref_1424_, v_msgData_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v_ref_1424_);
return v_res_1435_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__0));
v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__2));
v___x_1441_ = l_Lean_stringToMessageData(v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(lean_object* v_linterOption_1442_, lean_object* v_stx_1443_, lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_name_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1469_; 
v_name_1454_ = lean_ctor_get(v_linterOption_1442_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_linterOption_1442_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v_linterOption_1442_, 1);
lean_dec(v_unused_1470_);
v___x_1456_ = v_linterOption_1442_;
v_isShared_1457_ = v_isSharedCheck_1469_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_name_1454_);
lean_dec(v_linterOption_1442_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1469_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1);
lean_inc(v_name_1454_);
v___x_1459_ = l_Lean_MessageData_ofName(v_name_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 7);
lean_ctor_set(v___x_1456_, 1, v___x_1459_);
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_disable_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1462_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v_disable_1464_ = l_Lean_MessageData_note(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_msg_1444_);
lean_ctor_set(v___x_1465_, 1, v_disable_1464_);
v___x_1466_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_name_1454_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(v_stx_1443_, v___x_1466_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___boxed(lean_object* v_linterOption_1471_, lean_object* v_stx_1472_, lean_object* v_msg_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v_linterOption_1471_, v_stx_1472_, v_msg_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v_stx_1472_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(lean_object* v_o_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; lean_object* v_env_1488_; lean_object* v___x_1489_; lean_object* v_toEnvExtension_1490_; lean_object* v_asyncMode_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v_linterSets_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1487_ = lean_st_ref_get(v___y_1485_);
v_env_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc_ref(v_env_1488_);
lean_dec(v___x_1487_);
v___x_1489_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc_ref(v_toEnvExtension_1490_);
v_asyncMode_1491_ = lean_ctor_get(v_toEnvExtension_1490_, 2);
lean_inc(v_asyncMode_1491_);
lean_dec_ref(v_toEnvExtension_1490_);
v___x_1492_ = lean_box(1);
v___x_1493_ = lean_box(0);
v_linterSets_1494_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1492_, v___x_1489_, v_env_1488_, v_asyncMode_1491_, v___x_1493_);
lean_dec(v_asyncMode_1491_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_o_1484_);
lean_ctor_set(v___x_1495_, 1, v_linterSets_1494_);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg___boxed(lean_object* v_o_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_o_1497_, v___y_1498_);
lean_dec(v___y_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_options_1510_; lean_object* v___x_1511_; 
v_options_1510_ = lean_ctor_get(v___y_1507_, 2);
lean_inc_ref(v_options_1510_);
lean_dec_ref(v___y_1507_);
v___x_1511_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_options_1510_, v___y_1508_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(lean_object* v___y_1522_, lean_object* v_mkInfoTree_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v_a_1531_, lean_object* v_a_x3f_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v_infoState_1535_; lean_object* v_trees_1536_; lean_object* v___x_1537_; 
v___x_1534_ = lean_st_ref_get(v___y_1522_);
v_infoState_1535_ = lean_ctor_get(v___x_1534_, 7);
lean_inc_ref(v_infoState_1535_);
lean_dec(v___x_1534_);
v_trees_1536_ = lean_ctor_get(v_infoState_1535_, 2);
lean_inc_ref(v_trees_1536_);
lean_dec_ref(v_infoState_1535_);
lean_inc(v___y_1522_);
v___x_1537_ = lean_apply_10(v_mkInfoTree_1523_, v_trees_1536_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1576_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1576_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1576_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v_infoState_1543_; lean_object* v_env_1544_; lean_object* v_nextMacroScope_1545_; lean_object* v_ngen_1546_; lean_object* v_auxDeclNGen_1547_; lean_object* v_traceState_1548_; lean_object* v_cache_1549_; lean_object* v_messages_1550_; lean_object* v_snapshotTasks_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1575_; 
v___x_1542_ = lean_st_ref_take(v___y_1522_);
v_infoState_1543_ = lean_ctor_get(v___x_1542_, 7);
v_env_1544_ = lean_ctor_get(v___x_1542_, 0);
v_nextMacroScope_1545_ = lean_ctor_get(v___x_1542_, 1);
v_ngen_1546_ = lean_ctor_get(v___x_1542_, 2);
v_auxDeclNGen_1547_ = lean_ctor_get(v___x_1542_, 3);
v_traceState_1548_ = lean_ctor_get(v___x_1542_, 4);
v_cache_1549_ = lean_ctor_get(v___x_1542_, 5);
v_messages_1550_ = lean_ctor_get(v___x_1542_, 6);
v_snapshotTasks_1551_ = lean_ctor_get(v___x_1542_, 8);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1553_ = v___x_1542_;
v_isShared_1554_ = v_isSharedCheck_1575_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_snapshotTasks_1551_);
lean_inc(v_infoState_1543_);
lean_inc(v_messages_1550_);
lean_inc(v_cache_1549_);
lean_inc(v_traceState_1548_);
lean_inc(v_auxDeclNGen_1547_);
lean_inc(v_ngen_1546_);
lean_inc(v_nextMacroScope_1545_);
lean_inc(v_env_1544_);
lean_dec(v___x_1542_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1575_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
uint8_t v_enabled_1555_; lean_object* v_assignment_1556_; lean_object* v_lazyAssignment_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1573_; 
v_enabled_1555_ = lean_ctor_get_uint8(v_infoState_1543_, sizeof(void*)*3);
v_assignment_1556_ = lean_ctor_get(v_infoState_1543_, 0);
v_lazyAssignment_1557_ = lean_ctor_get(v_infoState_1543_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_infoState_1543_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; 
v_unused_1574_ = lean_ctor_get(v_infoState_1543_, 2);
lean_dec(v_unused_1574_);
v___x_1559_ = v_infoState_1543_;
v_isShared_1560_ = v_isSharedCheck_1573_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_lazyAssignment_1557_);
lean_inc(v_assignment_1556_);
lean_dec(v_infoState_1543_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1573_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = l_Lean_PersistentArray_push___redArg(v_a_1531_, v_a_1538_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 2, v___x_1561_);
v___x_1563_ = v___x_1559_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_assignment_1556_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_lazyAssignment_1557_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v___x_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1572_, sizeof(void*)*3, v_enabled_1555_);
v___x_1563_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 7, v___x_1563_);
v___x_1565_ = v___x_1553_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_env_1544_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_nextMacroScope_1545_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_ngen_1546_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_auxDeclNGen_1547_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_traceState_1548_);
lean_ctor_set(v_reuseFailAlloc_1571_, 5, v_cache_1549_);
lean_ctor_set(v_reuseFailAlloc_1571_, 6, v_messages_1550_);
lean_ctor_set(v_reuseFailAlloc_1571_, 7, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1571_, 8, v_snapshotTasks_1551_);
v___x_1565_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1566_ = lean_st_ref_set(v___y_1522_, v___x_1565_);
lean_dec(v___y_1522_);
v___x_1567_ = lean_box(0);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1567_);
v___x_1569_ = v___x_1540_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_a_1531_);
lean_dec(v___y_1522_);
v_a_1577_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1537_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1537_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0___boxed(lean_object* v___y_1585_, lean_object* v_mkInfoTree_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v_a_1594_, lean_object* v_a_x3f_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1585_, v_mkInfoTree_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v_a_1594_, v_a_x3f_1595_);
lean_dec(v_a_x3f_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(lean_object* v_x_1598_, lean_object* v_mkInfoTree_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v_infoState_1610_; uint8_t v_enabled_1611_; 
v___x_1609_ = lean_st_ref_get(v___y_1607_);
v_infoState_1610_ = lean_ctor_get(v___x_1609_, 7);
lean_inc_ref(v_infoState_1610_);
lean_dec(v___x_1609_);
v_enabled_1611_ = lean_ctor_get_uint8(v_infoState_1610_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1610_);
if (v_enabled_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_dec_ref(v_mkInfoTree_1599_);
v___x_1612_ = lean_apply_9(v_x_1598_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, lean_box(0));
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; lean_object* v_a_1614_; lean_object* v_r_1615_; 
v___x_1613_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_1607_);
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
lean_inc(v___y_1607_);
lean_inc_ref(v___y_1606_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
v_r_1615_ = lean_apply_9(v_x_1598_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, lean_box(0));
if (lean_obj_tag(v_r_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1640_; 
v_a_1616_ = lean_ctor_get(v_r_1615_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_r_1615_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1618_ = v_r_1615_;
v_isShared_1619_ = v_isSharedCheck_1640_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v_r_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1640_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
lean_inc(v_a_1616_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 1);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1607_, v_mkInfoTree_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v_a_1614_, v___x_1621_);
lean_dec_ref(v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v___x_1622_, 0);
lean_dec(v_unused_1630_);
v___x_1624_ = v___x_1622_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_dec(v___x_1622_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_a_1616_);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1616_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_a_1616_);
v_a_1631_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1622_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1622_);
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
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1641_ = lean_ctor_get(v_r_1615_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v_r_1615_);
v___x_1642_ = lean_box(0);
v___x_1643_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1607_, v_mkInfoTree_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v_a_1614_, v___x_1642_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1643_, 0);
lean_dec(v_unused_1651_);
v___x_1645_ = v___x_1643_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_dec(v___x_1643_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 1);
lean_ctor_set(v___x_1645_, 0, v_a_1641_);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1641_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec(v_a_1641_);
v_a_1652_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1643_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1643_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___boxed(lean_object* v_x_1660_, lean_object* v_mkInfoTree_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v_x_1660_, v_mkInfoTree_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v_res_1671_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object* v_usingArg_1693_, lean_object* v_snd_1694_, uint8_t v___x_1695_, uint8_t v___x_1696_, uint8_t v___x_1697_, lean_object* v___x_1698_, lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v_simprocs_1701_, lean_object* v_discharge_x3f_1702_, lean_object* v_snd_1703_, lean_object* v___x_1704_, lean_object* v___f_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; 
if (lean_obj_tag(v_usingArg_1693_) == 1)
{
lean_object* v_val_1895_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___x_1947_; lean_object* v_infoState_1948_; uint8_t v_enabled_1949_; 
v_val_1895_ = lean_ctor_get(v_usingArg_1693_, 0);
lean_inc(v_val_1895_);
lean_dec_ref(v_usingArg_1693_);
v___x_1947_ = lean_st_ref_get(v___y_1713_);
v_infoState_1948_ = lean_ctor_get(v___x_1947_, 7);
lean_inc_ref(v_infoState_1948_);
lean_dec(v___x_1947_);
v_enabled_1949_ = lean_ctor_get_uint8(v_infoState_1948_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1948_);
if (v_enabled_1949_ == 0)
{
lean_dec_ref(v___f_1705_);
v___y_1897_ = v___y_1706_;
v___y_1898_ = v___y_1707_;
v___y_1899_ = v___y_1708_;
v___y_1900_ = v___y_1709_;
v___y_1901_ = v___y_1710_;
v___y_1902_ = v___y_1711_;
v___y_1903_ = v___y_1712_;
v___y_1904_ = v___y_1713_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; 
v___x_1950_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_1713_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1950_);
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1952_, 0, v_a_1951_);
lean_inc(v___y_1713_);
lean_inc_ref(v___y_1712_);
lean_inc(v___y_1711_);
lean_inc_ref(v___y_1710_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
v___x_1953_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v___f_1952_, v___f_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_dec_ref(v___x_1953_);
v___y_1897_ = v___y_1706_;
v___y_1898_ = v___y_1707_;
v___y_1899_ = v___y_1708_;
v___y_1900_ = v___y_1709_;
v___y_1901_ = v___y_1710_;
v___y_1902_ = v___y_1711_;
v___y_1903_ = v___y_1712_;
v___y_1904_ = v___y_1713_;
goto v___jp_1896_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_val_1895_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
v___jp_1896_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_st_ref_get(v___y_1902_);
v___x_1906_ = lean_box(0);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1901_);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
v___x_1907_ = l_Lean_Elab_Tactic_elabTerm(v_val_1895_, v___x_1906_, v___x_1695_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1907_);
lean_inc(v_a_1908_);
v___x_1909_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(v_snd_1694_, v_a_1908_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_mctx_1910_; lean_object* v_a_1911_; uint8_t v___x_1912_; 
v_mctx_1910_ = lean_ctor_get(v___x_1905_, 0);
lean_inc_ref(v_mctx_1910_);
lean_dec(v___x_1905_);
v_a_1911_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1909_);
v___x_1912_ = lean_unbox(v_a_1911_);
lean_dec(v_a_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v_mctx_1910_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
v___x_1913_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9);
v___x_1914_ = l_Lean_indentExpr(v_a_1908_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_Expr_mvar___override(v_snd_1694_);
v___x_1919_ = l_Lean_MessageData_ofExpr(v___x_1918_);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1917_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v___x_1920_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
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
else
{
lean_object* v_mvarCounter_1930_; 
v_mvarCounter_1930_ = lean_ctor_get(v_mctx_1910_, 2);
lean_inc(v_mvarCounter_1930_);
lean_dec_ref(v_mctx_1910_);
lean_inc(v_a_1908_);
v___y_1779_ = v_mvarCounter_1930_;
v___y_1780_ = v_a_1908_;
v___y_1781_ = v___x_1906_;
v___y_1782_ = v___x_1906_;
v___y_1783_ = v_a_1908_;
v___y_1784_ = v___y_1897_;
v___y_1785_ = v___y_1898_;
v___y_1786_ = v___y_1899_;
v___y_1787_ = v___y_1900_;
v___y_1788_ = v___y_1901_;
v___y_1789_ = v___y_1902_;
v___y_1790_ = v___y_1903_;
v___y_1791_ = v___y_1904_;
goto v___jp_1778_;
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_a_1908_);
lean_dec(v___x_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1931_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1909_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1909_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v___x_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1939_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1907_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1907_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
lean_object* v_lctx_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v___f_1705_);
lean_dec_ref(v___x_1698_);
lean_dec(v_usingArg_1693_);
v_lctx_1962_ = lean_ctor_get(v___y_1710_, 2);
v___x_1963_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13));
v___x_1964_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_1962_, v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 1)
{
lean_object* v_val_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_val_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_val_1965_);
lean_dec_ref(v___x_1964_);
v___x_1966_ = l_Lean_LocalDecl_fvarId(v_val_1965_);
lean_dec(v_val_1965_);
v___x_1967_ = lean_mk_empty_array_with_capacity(v___x_1699_);
v___x_1968_ = lean_array_push(v___x_1967_, v___x_1966_);
lean_inc(v___y_1713_);
lean_inc_ref(v___y_1712_);
lean_inc(v___y_1711_);
lean_inc_ref(v___y_1710_);
lean_inc_ref(v_snd_1703_);
v___x_1969_ = l_Lean_Meta_simpGoal(v_snd_1694_, v___x_1700_, v_simprocs_1701_, v_discharge_x3f_1702_, v___x_1696_, v___x_1968_, v_snd_1703_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1998_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1998_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1998_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_fst_1974_; 
v_fst_1974_ = lean_ctor_get(v_a_1970_, 0);
if (lean_obj_tag(v_fst_1974_) == 1)
{
lean_object* v_val_1975_; lean_object* v_snd_1976_; lean_object* v_snd_1977_; lean_object* v___x_1978_; 
lean_del_object(v___x_1972_);
lean_dec_ref(v_snd_1703_);
v_val_1975_ = lean_ctor_get(v_fst_1974_, 0);
lean_inc(v_val_1975_);
v_snd_1976_ = lean_ctor_get(v_a_1970_, 1);
lean_inc(v_snd_1976_);
lean_dec(v_a_1970_);
v_snd_1977_ = lean_ctor_get(v_val_1975_, 1);
lean_inc(v_snd_1977_);
lean_dec(v_val_1975_);
v___x_1978_ = l_Lean_MVarId_assumption(v_snd_1977_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v___x_1978_, 0);
lean_dec(v_unused_1986_);
v___x_1980_ = v___x_1978_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v___x_1978_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_snd_1976_);
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_snd_1976_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_snd_1976_);
v_a_1987_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1978_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_a_1970_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_snd_1703_);
v___x_1996_ = v___x_1972_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_snd_1703_);
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
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec_ref(v_snd_1703_);
v_a_1999_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1969_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1969_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v___x_2007_; 
lean_dec(v___x_1964_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
v___x_2007_ = l_Lean_MVarId_assumption(v_snd_1694_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; 
v_unused_2015_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2015_);
v___x_2009_ = v___x_2007_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v___x_2007_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v_snd_1703_);
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_snd_1703_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_snd_1703_);
v_a_2016_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2007_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2007_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
v___jp_1715_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v___x_1719_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_snd_1694_, v___y_1716_, v___y_1718_);
lean_dec(v___y_1718_);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v___x_1719_, 0);
lean_dec(v_unused_1727_);
v___x_1721_ = v___x_1719_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_dec(v___x_1719_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___y_1717_);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___y_1717_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
v___jp_1728_:
{
lean_object* v___x_1745_; 
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1738_);
v___x_1745_ = l_Lean_Core_mkFreshUserName(v___y_1736_, v___y_1738_, v___y_1734_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref(v___x_1745_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1732_);
lean_inc(v_a_1746_);
v___x_1747_ = l_Lean_MVarId_rename(v___y_1737_, v___y_1744_, v_a_1746_, v___y_1732_, v___y_1743_, v___y_1738_, v___y_1734_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = lean_box(v___x_1695_);
v___x_1750_ = lean_box(v___x_1696_);
v___x_1751_ = lean_box(v___x_1697_);
lean_inc(v_a_1748_);
v___f_1752_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1752_, 0, v_a_1748_);
lean_closure_set(v___f_1752_, 1, v_a_1746_);
lean_closure_set(v___f_1752_, 2, v___x_1749_);
lean_closure_set(v___f_1752_, 3, v___x_1750_);
lean_closure_set(v___f_1752_, 4, v___x_1751_);
lean_closure_set(v___f_1752_, 5, v___y_1730_);
lean_closure_set(v___f_1752_, 6, v___y_1729_);
lean_closure_set(v___f_1752_, 7, v___x_1698_);
lean_closure_set(v___f_1752_, 8, v___y_1731_);
lean_inc(v___y_1743_);
v___x_1753_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_a_1748_, v___f_1752_, v___y_1735_, v___y_1742_, v___y_1741_, v___y_1740_, v___y_1732_, v___y_1743_, v___y_1738_, v___y_1734_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_dec_ref(v___x_1753_);
v___y_1716_ = v___y_1739_;
v___y_1717_ = v___y_1733_;
v___y_1718_ = v___y_1743_;
goto v___jp_1715_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1733_);
lean_dec(v_snd_1694_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1746_);
lean_dec(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1762_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1747_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1747_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1770_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1745_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1745_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
v___jp_1778_:
{
lean_object* v___x_1792_; 
lean_inc(v_snd_1694_);
v___x_1792_ = l_Lean_MVarId_getType(v_snd_1694_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref(v___x_1792_);
lean_inc(v_snd_1694_);
v___x_1794_ = l_Lean_MVarId_getTag(v_snd_1694_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref(v___x_1794_);
lean_inc_ref(v___y_1788_);
v___x_1796_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1793_, v_a_1795_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_Expr_mvarId_x21(v_a_1797_);
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1));
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
lean_inc_ref(v___y_1783_);
v___x_1800_ = l_Lean_MVarId_note(v___x_1798_, v___x_1799_, v___y_1783_, v___y_1782_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v_fst_1802_; lean_object* v_snd_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1862_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref(v___x_1800_);
v_fst_1802_ = lean_ctor_get(v_a_1801_, 0);
v_snd_1803_ = lean_ctor_get(v_a_1801_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_a_1801_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1805_ = v_a_1801_;
v_isShared_1806_ = v_isSharedCheck_1862_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_snd_1803_);
lean_inc(v_fst_1802_);
lean_dec(v_a_1801_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1862_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_mk_empty_array_with_capacity(v___x_1699_);
lean_inc(v_fst_1802_);
v___x_1808_ = lean_array_push(v___x_1807_, v_fst_1802_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
lean_inc(v___y_1789_);
lean_inc_ref(v___y_1788_);
v___x_1809_ = l_Lean_Meta_simpGoal(v_snd_1803_, v___x_1700_, v_simprocs_1701_, v_discharge_x3f_1702_, v___x_1696_, v___x_1808_, v_snd_1703_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v_fst_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref(v___x_1809_);
v_fst_1811_ = lean_ctor_get(v_a_1810_, 0);
if (lean_obj_tag(v_fst_1811_) == 0)
{
lean_object* v_snd_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_fst_1802_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___x_1698_);
v_snd_1812_ = lean_ctor_get(v_a_1810_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_a_1810_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; 
v_unused_1846_ = lean_ctor_get(v_a_1810_, 0);
lean_dec(v_unused_1846_);
v___x_1814_ = v_a_1810_;
v_isShared_1815_ = v_isSharedCheck_1845_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_snd_1812_);
lean_dec(v_a_1810_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1845_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v_a_1817_; uint8_t v___x_1818_; 
lean_inc_ref(v___y_1790_);
v___x_1816_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1817_);
lean_dec(v_a_1817_);
if (v___x_1818_ == 0)
{
lean_del_object(v___x_1814_);
lean_del_object(v___x_1805_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1783_);
v___y_1716_ = v_a_1797_;
v___y_1717_ = v_snd_1812_;
v___y_1718_ = v___y_1789_;
goto v___jp_1715_;
}
else
{
if (lean_obj_tag(v___y_1783_) == 1)
{
lean_object* v_fvarId_1819_; lean_object* v_lctx_1820_; lean_object* v___x_1821_; 
v_fvarId_1819_ = lean_ctor_get(v___y_1783_, 0);
v_lctx_1820_ = lean_ctor_get(v___y_1788_, 2);
lean_inc(v_fvarId_1819_);
lean_inc_ref(v_lctx_1820_);
v___x_1821_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1820_, v_fvarId_1819_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_dec_ref(v___y_1783_);
lean_del_object(v___x_1814_);
lean_del_object(v___x_1805_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
v___y_1716_ = v_a_1797_;
v___y_1717_ = v_snd_1812_;
v___y_1718_ = v___y_1789_;
goto v___jp_1715_;
}
else
{
lean_dec_ref(v___x_1821_);
if (v___x_1697_ == 0)
{
lean_dec_ref(v___y_1783_);
lean_del_object(v___x_1814_);
lean_del_object(v___x_1805_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
v___y_1716_ = v_a_1797_;
v___y_1717_ = v_snd_1812_;
v___y_1718_ = v___y_1789_;
goto v___jp_1715_;
}
else
{
lean_object* v_ref_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v_ref_1822_ = lean_ctor_get(v___y_1790_, 5);
lean_inc(v_ref_1822_);
v___x_1823_ = l_linter_unnecessarySimpa;
v___x_1824_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3);
v___x_1825_ = l_Lean_MessageData_ofExpr(v___y_1783_);
lean_inc_ref(v___x_1825_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 7);
lean_ctor_set(v___x_1814_, 1, v___x_1825_);
lean_ctor_set(v___x_1814_, 0, v___x_1824_);
v___x_1827_ = v___x_1814_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5);
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 7);
lean_ctor_set(v___x_1805_, 1, v___x_1828_);
lean_ctor_set(v___x_1805_, 0, v___x_1827_);
v___x_1830_ = v___x_1805_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
lean_ctor_set(v___x_1831_, 1, v___x_1825_);
v___x_1832_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v___x_1823_, v_ref_1822_, v___x_1833_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v_ref_1822_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_dec_ref(v___x_1834_);
v___y_1716_ = v_a_1797_;
v___y_1717_ = v_snd_1812_;
v___y_1718_ = v___y_1789_;
goto v___jp_1715_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_snd_1812_);
lean_dec(v_a_1797_);
lean_dec(v___y_1789_);
lean_dec(v_snd_1694_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
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
lean_del_object(v___x_1814_);
lean_del_object(v___x_1805_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1783_);
v___y_1716_ = v_a_1797_;
v___y_1717_ = v_snd_1812_;
v___y_1718_ = v___y_1789_;
goto v___jp_1715_;
}
}
}
}
else
{
lean_object* v_val_1847_; lean_object* v_snd_1848_; lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
lean_del_object(v___x_1805_);
lean_dec_ref(v___y_1783_);
v_val_1847_ = lean_ctor_get(v_fst_1811_, 0);
lean_inc(v_val_1847_);
v_snd_1848_ = lean_ctor_get(v_a_1810_, 1);
lean_inc(v_snd_1848_);
lean_dec(v_a_1810_);
v_fst_1849_ = lean_ctor_get(v_val_1847_, 0);
lean_inc(v_fst_1849_);
v_snd_1850_ = lean_ctor_get(v_val_1847_, 1);
lean_inc(v_snd_1850_);
lean_dec(v_val_1847_);
v___x_1851_ = lean_array_get_size(v_fst_1849_);
v___x_1852_ = lean_nat_dec_lt(v___x_1704_, v___x_1851_);
if (v___x_1852_ == 0)
{
lean_dec(v_fst_1849_);
v___y_1729_ = v___y_1779_;
v___y_1730_ = v___y_1780_;
v___y_1731_ = v___y_1781_;
v___y_1732_ = v___y_1788_;
v___y_1733_ = v_snd_1848_;
v___y_1734_ = v___y_1791_;
v___y_1735_ = v___y_1784_;
v___y_1736_ = v___x_1799_;
v___y_1737_ = v_snd_1850_;
v___y_1738_ = v___y_1790_;
v___y_1739_ = v_a_1797_;
v___y_1740_ = v___y_1787_;
v___y_1741_ = v___y_1786_;
v___y_1742_ = v___y_1785_;
v___y_1743_ = v___y_1789_;
v___y_1744_ = v_fst_1802_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1853_; 
lean_dec(v_fst_1802_);
v___x_1853_ = lean_array_fget(v_fst_1849_, v___x_1704_);
lean_dec(v_fst_1849_);
v___y_1729_ = v___y_1779_;
v___y_1730_ = v___y_1780_;
v___y_1731_ = v___y_1781_;
v___y_1732_ = v___y_1788_;
v___y_1733_ = v_snd_1848_;
v___y_1734_ = v___y_1791_;
v___y_1735_ = v___y_1784_;
v___y_1736_ = v___x_1799_;
v___y_1737_ = v_snd_1850_;
v___y_1738_ = v___y_1790_;
v___y_1739_ = v_a_1797_;
v___y_1740_ = v___y_1787_;
v___y_1741_ = v___y_1786_;
v___y_1742_ = v___y_1785_;
v___y_1743_ = v___y_1789_;
v___y_1744_ = v___x_1853_;
goto v___jp_1728_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_del_object(v___x_1805_);
lean_dec(v_fst_1802_);
lean_dec(v_a_1797_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1854_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1809_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1809_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_a_1797_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1863_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1800_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1800_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1871_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1796_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1796_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_a_1793_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1879_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1794_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1794_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v_snd_1703_);
lean_dec(v_discharge_x3f_1702_);
lean_dec_ref(v_simprocs_1701_);
lean_dec_ref(v___x_1700_);
lean_dec_ref(v___x_1698_);
lean_dec(v_snd_1694_);
v_a_1887_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1792_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1792_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2024_ = _args[0];
lean_object* v_snd_2025_ = _args[1];
lean_object* v___x_2026_ = _args[2];
lean_object* v___x_2027_ = _args[3];
lean_object* v___x_2028_ = _args[4];
lean_object* v___x_2029_ = _args[5];
lean_object* v___x_2030_ = _args[6];
lean_object* v___x_2031_ = _args[7];
lean_object* v_simprocs_2032_ = _args[8];
lean_object* v_discharge_x3f_2033_ = _args[9];
lean_object* v_snd_2034_ = _args[10];
lean_object* v___x_2035_ = _args[11];
lean_object* v___f_2036_ = _args[12];
lean_object* v___y_2037_ = _args[13];
lean_object* v___y_2038_ = _args[14];
lean_object* v___y_2039_ = _args[15];
lean_object* v___y_2040_ = _args[16];
lean_object* v___y_2041_ = _args[17];
lean_object* v___y_2042_ = _args[18];
lean_object* v___y_2043_ = _args[19];
lean_object* v___y_2044_ = _args[20];
lean_object* v___y_2045_ = _args[21];
_start:
{
uint8_t v___x_82136__boxed_2046_; uint8_t v___x_82137__boxed_2047_; uint8_t v___x_82138__boxed_2048_; lean_object* v_res_2049_; 
v___x_82136__boxed_2046_ = lean_unbox(v___x_2026_);
v___x_82137__boxed_2047_ = lean_unbox(v___x_2027_);
v___x_82138__boxed_2048_ = lean_unbox(v___x_2028_);
v_res_2049_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(v_usingArg_2024_, v_snd_2025_, v___x_82136__boxed_2046_, v___x_82137__boxed_2047_, v___x_82138__boxed_2048_, v___x_2029_, v___x_2030_, v___x_2031_, v_simprocs_2032_, v_discharge_x3f_2033_, v_snd_2034_, v___x_2035_, v___f_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___x_2035_);
lean_dec(v___x_2030_);
return v_res_2049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_unsigned_to_nat(32u);
v___x_2054_ = lean_mk_empty_array_with_capacity(v___x_2053_);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4));
v___x_2060_ = l_Lean_MessageData_ofFormat(v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object* v___x_2061_, lean_object* v_tk_2062_, lean_object* v___x_2063_, lean_object* v___x_2064_, lean_object* v___x_2065_, lean_object* v_simprocs_2066_, uint8_t v___x_2067_, lean_object* v_usingArg_2068_, uint8_t v___x_2069_, uint8_t v___x_2070_, lean_object* v___x_2071_, lean_object* v___x_2072_, lean_object* v_usingTk_x3f_2073_, lean_object* v_discharge_x3f_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___y_2085_; 
if (lean_obj_tag(v_usingTk_x3f_2073_) == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_box(0);
v___y_2085_ = v___x_2189_;
goto v___jp_2084_;
}
else
{
lean_object* v_val_2190_; 
v_val_2190_ = lean_ctor_get(v_usingTk_x3f_2073_, 0);
lean_inc(v_val_2190_);
lean_dec_ref(v_usingTk_x3f_2073_);
v___y_2085_ = v_val_2190_;
goto v___jp_2084_;
}
v___jp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2086_ = lean_mk_empty_array_with_capacity(v___x_2061_);
v___x_2087_ = lean_array_push(v___x_2086_, v_tk_2062_);
v___x_2088_ = lean_array_push(v___x_2087_, v___y_2085_);
v___x_2089_ = lean_box(2);
v___x_2090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2063_);
lean_ctor_set(v___x_2090_, 2, v___x_2088_);
v___x_2091_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2090_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2076_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2093_);
v___x_2095_ = lean_mk_empty_array_with_capacity(v___x_2064_);
v___x_2096_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1);
lean_inc(v___x_2064_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v___x_2064_);
v___x_2098_ = lean_unsigned_to_nat(32u);
v___x_2099_ = lean_mk_empty_array_with_capacity(v___x_2098_);
v___x_2100_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2);
v___x_2101_ = ((size_t)5ULL);
lean_inc_n(v___x_2064_, 2);
v___x_2102_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2099_);
lean_ctor_set(v___x_2102_, 2, v___x_2064_);
lean_ctor_set(v___x_2102_, 3, v___x_2064_);
lean_ctor_set_usize(v___x_2102_, 4, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2096_);
lean_ctor_set(v___x_2103_, 1, v___x_2096_);
lean_ctor_set(v___x_2103_, 2, v___x_2096_);
lean_ctor_set(v___x_2103_, 3, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2097_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc_ref(v___x_2104_);
lean_inc(v_discharge_x3f_2074_);
lean_inc_ref(v_simprocs_2066_);
lean_inc_ref(v___x_2065_);
v___x_2105_ = l_Lean_Meta_simpGoal(v_a_2094_, v___x_2065_, v_simprocs_2066_, v_discharge_x3f_2074_, v___x_2067_, v___x_2095_, v___x_2104_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v_fst_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v_fst_2107_ = lean_ctor_get(v_a_2106_, 0);
if (lean_obj_tag(v_fst_2107_) == 1)
{
lean_object* v_val_2108_; lean_object* v_snd_2109_; lean_object* v_snd_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v___x_2104_);
v_val_2108_ = lean_ctor_get(v_fst_2107_, 0);
lean_inc(v_val_2108_);
v_snd_2109_ = lean_ctor_get(v_a_2106_, 1);
lean_inc(v_snd_2109_);
lean_dec(v_a_2106_);
v_snd_2110_ = lean_ctor_get(v_val_2108_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_val_2108_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_val_2108_, 0);
lean_dec(v_unused_2134_);
v___x_2112_ = v_val_2108_;
v_isShared_2113_ = v_isSharedCheck_2133_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snd_2110_);
lean_dec(v_val_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2133_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_box(0);
lean_inc(v_snd_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 1);
lean_ctor_set(v___x_2112_, 1, v___x_2114_);
lean_ctor_set(v___x_2112_, 0, v_snd_2110_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_snd_2110_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2116_, v___y_2076_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___f_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___y_2122_; lean_object* v___x_2123_; 
lean_dec_ref(v___x_2117_);
v___f_2118_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2118_, 0, v_a_2092_);
v___x_2119_ = lean_box(v___x_2067_);
v___x_2120_ = lean_box(v___x_2069_);
v___x_2121_ = lean_box(v___x_2070_);
lean_inc(v_snd_2110_);
v___y_2122_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 22, 13);
lean_closure_set(v___y_2122_, 0, v_usingArg_2068_);
lean_closure_set(v___y_2122_, 1, v_snd_2110_);
lean_closure_set(v___y_2122_, 2, v___x_2119_);
lean_closure_set(v___y_2122_, 3, v___x_2120_);
lean_closure_set(v___y_2122_, 4, v___x_2121_);
lean_closure_set(v___y_2122_, 5, v___x_2071_);
lean_closure_set(v___y_2122_, 6, v___x_2072_);
lean_closure_set(v___y_2122_, 7, v___x_2065_);
lean_closure_set(v___y_2122_, 8, v_simprocs_2066_);
lean_closure_set(v___y_2122_, 9, v_discharge_x3f_2074_);
lean_closure_set(v___y_2122_, 10, v_snd_2109_);
lean_closure_set(v___y_2122_, 11, v___x_2064_);
lean_closure_set(v___y_2122_, 12, v___f_2118_);
v___x_2123_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_snd_2110_, v___y_2122_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
return v___x_2123_;
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_snd_2110_);
lean_dec(v_snd_2109_);
lean_dec(v_a_2092_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_discharge_x3f_2074_);
lean_dec(v___x_2072_);
lean_dec_ref(v___x_2071_);
lean_dec(v_usingArg_2068_);
lean_dec_ref(v_simprocs_2066_);
lean_dec_ref(v___x_2065_);
lean_dec(v___x_2064_);
v_a_2124_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2117_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2117_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_a_2106_);
lean_dec(v_a_2092_);
lean_dec(v_discharge_x3f_2074_);
lean_dec(v___x_2072_);
lean_dec_ref(v___x_2071_);
lean_dec(v_usingArg_2068_);
lean_dec_ref(v_simprocs_2066_);
lean_dec_ref(v___x_2065_);
lean_dec(v___x_2064_);
lean_inc_ref(v___y_2081_);
v___x_2135_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2164_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2164_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
uint8_t v___x_2140_; 
v___x_2140_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2136_);
lean_dec(v_a_2136_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2142_; 
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2104_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2104_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
else
{
lean_object* v_ref_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_del_object(v___x_2138_);
v_ref_2144_ = lean_ctor_get(v___y_2081_, 5);
lean_inc(v_ref_2144_);
v___x_2145_ = l_linter_unnecessarySimpa;
v___x_2146_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5);
v___x_2147_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v___x_2145_, v_ref_2144_, v___x_2146_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_ref_2144_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v___x_2147_, 0);
lean_dec(v_unused_2155_);
v___x_2149_ = v___x_2147_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v___x_2147_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2104_);
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2104_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v___x_2104_);
v_a_2156_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2147_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2147_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v___x_2104_);
lean_dec(v_a_2092_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_discharge_x3f_2074_);
lean_dec(v___x_2072_);
lean_dec_ref(v___x_2071_);
lean_dec(v_usingArg_2068_);
lean_dec_ref(v_simprocs_2066_);
lean_dec_ref(v___x_2065_);
lean_dec(v___x_2064_);
v_a_2165_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2105_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2105_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2092_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_discharge_x3f_2074_);
lean_dec(v___x_2072_);
lean_dec_ref(v___x_2071_);
lean_dec(v_usingArg_2068_);
lean_dec_ref(v_simprocs_2066_);
lean_dec_ref(v___x_2065_);
lean_dec(v___x_2064_);
v_a_2173_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2093_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2093_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v_discharge_x3f_2074_);
lean_dec(v___x_2072_);
lean_dec_ref(v___x_2071_);
lean_dec(v_usingArg_2068_);
lean_dec_ref(v_simprocs_2066_);
lean_dec_ref(v___x_2065_);
lean_dec(v___x_2064_);
v_a_2181_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2091_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2091_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object** _args){
lean_object* v___x_2191_ = _args[0];
lean_object* v_tk_2192_ = _args[1];
lean_object* v___x_2193_ = _args[2];
lean_object* v___x_2194_ = _args[3];
lean_object* v___x_2195_ = _args[4];
lean_object* v_simprocs_2196_ = _args[5];
lean_object* v___x_2197_ = _args[6];
lean_object* v_usingArg_2198_ = _args[7];
lean_object* v___x_2199_ = _args[8];
lean_object* v___x_2200_ = _args[9];
lean_object* v___x_2201_ = _args[10];
lean_object* v___x_2202_ = _args[11];
lean_object* v_usingTk_x3f_2203_ = _args[12];
lean_object* v_discharge_x3f_2204_ = _args[13];
lean_object* v___y_2205_ = _args[14];
lean_object* v___y_2206_ = _args[15];
lean_object* v___y_2207_ = _args[16];
lean_object* v___y_2208_ = _args[17];
lean_object* v___y_2209_ = _args[18];
lean_object* v___y_2210_ = _args[19];
lean_object* v___y_2211_ = _args[20];
lean_object* v___y_2212_ = _args[21];
lean_object* v___y_2213_ = _args[22];
_start:
{
uint8_t v___x_82858__boxed_2214_; uint8_t v___x_82859__boxed_2215_; uint8_t v___x_82860__boxed_2216_; lean_object* v_res_2217_; 
v___x_82858__boxed_2214_ = lean_unbox(v___x_2197_);
v___x_82859__boxed_2215_ = lean_unbox(v___x_2199_);
v___x_82860__boxed_2216_ = lean_unbox(v___x_2200_);
v_res_2217_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(v___x_2191_, v_tk_2192_, v___x_2193_, v___x_2194_, v___x_2195_, v_simprocs_2196_, v___x_82858__boxed_2214_, v_usingArg_2198_, v___x_82859__boxed_2215_, v___x_82860__boxed_2216_, v___x_2201_, v___x_2202_, v_usingTk_x3f_2203_, v_discharge_x3f_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___x_2191_);
return v_res_2217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Array_mkArray0(lean_box(0));
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2237_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16));
v___x_2238_ = lean_unsigned_to_nat(15u);
v___x_2239_ = lean_unsigned_to_nat(116u);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15));
v___x_2241_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14));
v___x_2242_ = l_mkPanicMessageWithDecl(v___x_2241_, v___x_2240_, v___x_2239_, v___x_2238_, v___x_2237_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object* v_tk_2244_, lean_object* v___x_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v___x_2248_, lean_object* v___x_2249_, uint8_t v___x_2250_, lean_object* v___x_2251_, lean_object* v___f_2252_, lean_object* v___x_2253_, lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v_usingArg_2259_, lean_object* v___x_2260_, uint8_t v___x_2261_, lean_object* v_usingTk_x3f_2262_, lean_object* v_squeeze_2263_, lean_object* v_unfold_2264_, lean_object* v_args_2265_, lean_object* v_only_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___y_2278_; lean_object* v___y_2282_; lean_object* v_stx_2283_; lean_object* v___y_2284_; lean_object* v_ref_2285_; lean_object* v___y_2286_; lean_object* v___y_2304_; lean_object* v_stx_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v_options_2309_; lean_object* v_ref_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; uint8_t v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v_args_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; lean_object* v___y_2577_; lean_object* v_only_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2606_; lean_object* v___y_2607_; uint8_t v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2666_; lean_object* v___y_2667_; uint8_t v___y_2668_; lean_object* v___y_2679_; lean_object* v___y_2680_; uint8_t v___y_2681_; uint8_t v___y_2682_; lean_object* v___y_2684_; lean_object* v___y_2685_; uint8_t v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2760_; 
v_options_2309_ = lean_ctor_get(v___y_2274_, 2);
v_ref_2310_ = lean_ctor_get(v___y_2274_, 5);
v___x_2311_ = 0;
v___x_2312_ = l_Lean_SourceInfo_fromRef(v_ref_2310_, v___x_2311_);
v___x_2313_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3));
lean_inc_ref(v___x_2247_);
lean_inc_ref(v___x_2246_);
lean_inc_ref(v___x_2245_);
v___x_2314_ = l_Lean_Name_mkStr4(v___x_2245_, v___x_2246_, v___x_2247_, v___x_2313_);
lean_inc(v___x_2312_);
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2312_);
lean_ctor_set(v___x_2315_, 1, v___x_2313_);
v___x_2316_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5));
v___x_2317_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6);
if (lean_obj_tag(v___y_2267_) == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2760_ = v___x_2769_;
goto v___jp_2759_;
}
else
{
lean_object* v_val_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_val_2770_ = lean_ctor_get(v___y_2267_, 0);
lean_inc(v_val_2770_);
lean_dec_ref(v___y_2267_);
v___x_2771_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___x_2772_ = lean_array_push(v___x_2771_, v_val_2770_);
v___y_2760_ = v___x_2772_;
goto v___jp_2759_;
}
v___jp_2277_:
{
lean_object* v_diag_2279_; lean_object* v___x_2280_; 
v_diag_2279_ = lean_ctor_get(v___y_2278_, 1);
lean_inc_ref(v_diag_2279_);
lean_dec_ref(v___y_2278_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_diag_2279_);
return v___x_2280_;
}
v___jp_2281_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; 
v___x_2287_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1));
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v_stx_2283_);
v___x_2289_ = lean_box(0);
v___x_2290_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
lean_ctor_set(v___x_2290_, 2, v___x_2289_);
lean_ctor_set(v___x_2290_, 3, v___x_2289_);
lean_ctor_set(v___x_2290_, 4, v___x_2289_);
lean_ctor_set(v___x_2290_, 5, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_ref_2285_);
v___x_2292_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2));
v___x_2293_ = 4;
v___x_2294_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2244_, v___x_2290_, v___x_2291_, v___x_2292_, v___x_2289_, v___x_2293_, v___y_2284_, v___y_2286_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref(v___x_2294_);
v___y_2278_ = v___y_2282_;
goto v___jp_2277_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v___y_2282_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
v___jp_2303_:
{
lean_object* v_ref_2308_; 
v_ref_2308_ = lean_ctor_get(v___y_2306_, 5);
lean_inc(v_ref_2308_);
v___y_2282_ = v___y_2304_;
v_stx_2283_ = v_stx_2305_;
v___y_2284_ = v___y_2306_;
v_ref_2285_ = v_ref_2308_;
v___y_2286_ = v___y_2307_;
goto v___jp_2281_;
}
v___jp_2318_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2330_ = l_Array_append___redArg(v___x_2317_, v___y_2329_);
lean_dec_ref(v___y_2329_);
lean_inc(v___y_2322_);
v___x_2331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2331_, 0, v___y_2322_);
lean_ctor_set(v___x_2331_, 1, v___x_2316_);
lean_ctor_set(v___x_2331_, 2, v___x_2330_);
lean_inc(v___y_2322_);
v___x_2332_ = l_Lean_Syntax_node5(v___y_2322_, v___x_2248_, v___y_2319_, v___y_2326_, v___y_2325_, v___y_2327_, v___x_2331_);
lean_inc(v___y_2323_);
v___x_2333_ = l_Lean_Syntax_node4(v___y_2322_, v___x_2251_, v___y_2324_, v___y_2323_, v___y_2323_, v___x_2332_);
v___y_2304_ = v___y_2320_;
v_stx_2305_ = v___x_2333_;
v___y_2306_ = v___y_2321_;
v___y_2307_ = v___y_2328_;
goto v___jp_2303_;
}
v___jp_2334_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = l_Array_append___redArg(v___x_2317_, v___y_2345_);
lean_dec_ref(v___y_2345_);
lean_inc(v___y_2339_);
v___x_2347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2347_, 0, v___y_2339_);
lean_ctor_set(v___x_2347_, 1, v___x_2316_);
lean_ctor_set(v___x_2347_, 2, v___x_2346_);
if (lean_obj_tag(v___y_2337_) == 1)
{
lean_object* v_val_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec(v___x_2249_);
v_val_2348_ = lean_ctor_get(v___y_2337_, 0);
lean_inc(v_val_2348_);
lean_dec_ref(v___y_2337_);
v___x_2349_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2339_);
v___x_2350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___y_2339_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l_Array_mkArray2___redArg(v___x_2350_, v_val_2348_);
v___y_2319_ = v___y_2335_;
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2338_;
v___y_2322_ = v___y_2339_;
v___y_2323_ = v___y_2342_;
v___y_2324_ = v___y_2341_;
v___y_2325_ = v___y_2340_;
v___y_2326_ = v___y_2343_;
v___y_2327_ = v___x_2347_;
v___y_2328_ = v___y_2344_;
v___y_2329_ = v___x_2351_;
goto v___jp_2318_;
}
else
{
lean_object* v___x_2352_; 
lean_dec(v___y_2337_);
v___x_2352_ = lean_mk_empty_array_with_capacity(v___x_2249_);
lean_dec(v___x_2249_);
v___y_2319_ = v___y_2335_;
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2338_;
v___y_2322_ = v___y_2339_;
v___y_2323_ = v___y_2342_;
v___y_2324_ = v___y_2341_;
v___y_2325_ = v___y_2340_;
v___y_2326_ = v___y_2343_;
v___y_2327_ = v___x_2347_;
v___y_2328_ = v___y_2344_;
v___y_2329_ = v___x_2352_;
goto v___jp_2318_;
}
}
v___jp_2353_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = l_Array_append___redArg(v___x_2317_, v___y_2364_);
lean_dec_ref(v___y_2364_);
lean_inc(v___y_2359_);
v___x_2366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2366_, 0, v___y_2359_);
lean_ctor_set(v___x_2366_, 1, v___x_2316_);
lean_ctor_set(v___x_2366_, 2, v___x_2365_);
if (lean_obj_tag(v___y_2355_) == 1)
{
lean_object* v_val_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_val_2367_ = lean_ctor_get(v___y_2355_, 0);
lean_inc(v_val_2367_);
lean_dec_ref(v___y_2355_);
v___x_2368_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2369_ = l_Lean_Name_mkStr4(v___x_2245_, v___x_2246_, v___x_2247_, v___x_2368_);
v___x_2370_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc(v___y_2359_);
v___x_2371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___y_2359_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Array_append___redArg(v___x_2317_, v_val_2367_);
lean_dec(v_val_2367_);
lean_inc(v___y_2359_);
v___x_2373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2373_, 0, v___y_2359_);
lean_ctor_set(v___x_2373_, 1, v___x_2316_);
lean_ctor_set(v___x_2373_, 2, v___x_2372_);
v___x_2374_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
lean_inc(v___y_2359_);
v___x_2375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___y_2359_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
lean_inc(v___y_2359_);
v___x_2376_ = l_Lean_Syntax_node3(v___y_2359_, v___x_2369_, v___x_2371_, v___x_2373_, v___x_2375_);
v___x_2377_ = l_Array_mkArray1___redArg(v___x_2376_);
v___y_2335_ = v___y_2354_;
v___y_2336_ = v___y_2356_;
v___y_2337_ = v___y_2357_;
v___y_2338_ = v___y_2358_;
v___y_2339_ = v___y_2359_;
v___y_2340_ = v___x_2366_;
v___y_2341_ = v___y_2361_;
v___y_2342_ = v___y_2360_;
v___y_2343_ = v___y_2362_;
v___y_2344_ = v___y_2363_;
v___y_2345_ = v___x_2377_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2378_; 
lean_dec(v___y_2355_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
v___x_2378_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2335_ = v___y_2354_;
v___y_2336_ = v___y_2356_;
v___y_2337_ = v___y_2357_;
v___y_2338_ = v___y_2358_;
v___y_2339_ = v___y_2359_;
v___y_2340_ = v___x_2366_;
v___y_2341_ = v___y_2361_;
v___y_2342_ = v___y_2360_;
v___y_2343_ = v___y_2362_;
v___y_2344_ = v___y_2363_;
v___y_2345_ = v___x_2378_;
goto v___jp_2334_;
}
}
v___jp_2379_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = l_Array_append___redArg(v___x_2317_, v___y_2390_);
lean_dec_ref(v___y_2390_);
lean_inc(v___y_2386_);
v___x_2392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2392_, 0, v___y_2386_);
lean_ctor_set(v___x_2392_, 1, v___x_2316_);
lean_ctor_set(v___x_2392_, 2, v___x_2391_);
if (lean_obj_tag(v___y_2385_) == 1)
{
lean_object* v_val_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_val_2393_ = lean_ctor_get(v___y_2385_, 0);
lean_inc(v_val_2393_);
lean_dec_ref(v___y_2385_);
v___x_2394_ = l_Lean_SourceInfo_fromRef(v_val_2393_, v___x_2250_);
lean_dec(v_val_2393_);
v___x_2395_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Array_mkArray1___redArg(v___x_2396_);
v___y_2354_ = v___y_2380_;
v___y_2355_ = v___y_2381_;
v___y_2356_ = v___y_2382_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2384_;
v___y_2359_ = v___y_2386_;
v___y_2360_ = v___y_2388_;
v___y_2361_ = v___y_2387_;
v___y_2362_ = v___x_2392_;
v___y_2363_ = v___y_2389_;
v___y_2364_ = v___x_2397_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2398_; 
lean_dec(v___y_2385_);
v___x_2398_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2354_ = v___y_2380_;
v___y_2355_ = v___y_2381_;
v___y_2356_ = v___y_2382_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2384_;
v___y_2359_ = v___y_2386_;
v___y_2360_ = v___y_2388_;
v___y_2361_ = v___y_2387_;
v___y_2362_ = v___x_2392_;
v___y_2363_ = v___y_2389_;
v___y_2364_ = v___x_2398_;
goto v___jp_2353_;
}
}
v___jp_2399_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2411_ = l_Array_append___redArg(v___x_2317_, v___y_2410_);
lean_dec_ref(v___y_2410_);
lean_inc(v___y_2402_);
v___x_2412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2412_, 0, v___y_2402_);
lean_ctor_set(v___x_2412_, 1, v___x_2316_);
lean_ctor_set(v___x_2412_, 2, v___x_2411_);
lean_inc(v___y_2402_);
v___x_2413_ = l_Lean_Syntax_node5(v___y_2402_, v___x_2248_, v___y_2401_, v___y_2406_, v___y_2407_, v___y_2403_, v___x_2412_);
v___x_2414_ = l_Lean_Syntax_node2(v___y_2402_, v___y_2400_, v___y_2409_, v___x_2413_);
v___y_2304_ = v___y_2404_;
v_stx_2305_ = v___x_2414_;
v___y_2306_ = v___y_2405_;
v___y_2307_ = v___y_2408_;
goto v___jp_2303_;
}
v___jp_2415_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = l_Array_append___redArg(v___x_2317_, v___y_2426_);
lean_dec_ref(v___y_2426_);
lean_inc(v___y_2418_);
v___x_2428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2418_);
lean_ctor_set(v___x_2428_, 1, v___x_2316_);
lean_ctor_set(v___x_2428_, 2, v___x_2427_);
if (lean_obj_tag(v___y_2420_) == 1)
{
lean_object* v_val_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_dec(v___x_2249_);
v_val_2429_ = lean_ctor_get(v___y_2420_, 0);
lean_inc(v_val_2429_);
lean_dec_ref(v___y_2420_);
v___x_2430_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2418_);
v___x_2431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___y_2418_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = l_Array_mkArray2___redArg(v___x_2431_, v_val_2429_);
v___y_2400_ = v___y_2417_;
v___y_2401_ = v___y_2416_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___x_2428_;
v___y_2404_ = v___y_2419_;
v___y_2405_ = v___y_2421_;
v___y_2406_ = v___y_2422_;
v___y_2407_ = v___y_2423_;
v___y_2408_ = v___y_2425_;
v___y_2409_ = v___y_2424_;
v___y_2410_ = v___x_2432_;
goto v___jp_2399_;
}
else
{
lean_object* v___x_2433_; 
lean_dec(v___y_2420_);
v___x_2433_ = lean_mk_empty_array_with_capacity(v___x_2249_);
lean_dec(v___x_2249_);
v___y_2400_ = v___y_2417_;
v___y_2401_ = v___y_2416_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___x_2428_;
v___y_2404_ = v___y_2419_;
v___y_2405_ = v___y_2421_;
v___y_2406_ = v___y_2422_;
v___y_2407_ = v___y_2423_;
v___y_2408_ = v___y_2425_;
v___y_2409_ = v___y_2424_;
v___y_2410_ = v___x_2433_;
goto v___jp_2399_;
}
}
v___jp_2434_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = l_Array_append___redArg(v___x_2317_, v___y_2445_);
lean_dec_ref(v___y_2445_);
lean_inc(v___y_2437_);
v___x_2447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2447_, 0, v___y_2437_);
lean_ctor_set(v___x_2447_, 1, v___x_2316_);
lean_ctor_set(v___x_2447_, 2, v___x_2446_);
if (lean_obj_tag(v___y_2438_) == 1)
{
lean_object* v_val_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_val_2448_ = lean_ctor_get(v___y_2438_, 0);
lean_inc(v_val_2448_);
lean_dec_ref(v___y_2438_);
v___x_2449_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2450_ = l_Lean_Name_mkStr4(v___x_2245_, v___x_2246_, v___x_2247_, v___x_2449_);
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc(v___y_2437_);
v___x_2452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___y_2437_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = l_Array_append___redArg(v___x_2317_, v_val_2448_);
lean_dec(v_val_2448_);
lean_inc(v___y_2437_);
v___x_2454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2437_);
lean_ctor_set(v___x_2454_, 1, v___x_2316_);
lean_ctor_set(v___x_2454_, 2, v___x_2453_);
v___x_2455_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
lean_inc(v___y_2437_);
v___x_2456_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___y_2437_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
lean_inc(v___y_2437_);
v___x_2457_ = l_Lean_Syntax_node3(v___y_2437_, v___x_2450_, v___x_2452_, v___x_2454_, v___x_2456_);
v___x_2458_ = l_Array_mkArray1___redArg(v___x_2457_);
v___y_2416_ = v___y_2436_;
v___y_2417_ = v___y_2435_;
v___y_2418_ = v___y_2437_;
v___y_2419_ = v___y_2439_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2441_;
v___y_2422_ = v___y_2442_;
v___y_2423_ = v___x_2447_;
v___y_2424_ = v___y_2444_;
v___y_2425_ = v___y_2443_;
v___y_2426_ = v___x_2458_;
goto v___jp_2415_;
}
else
{
lean_object* v___x_2459_; 
lean_dec(v___y_2438_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
v___x_2459_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2416_ = v___y_2436_;
v___y_2417_ = v___y_2435_;
v___y_2418_ = v___y_2437_;
v___y_2419_ = v___y_2439_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2441_;
v___y_2422_ = v___y_2442_;
v___y_2423_ = v___x_2447_;
v___y_2424_ = v___y_2444_;
v___y_2425_ = v___y_2443_;
v___y_2426_ = v___x_2459_;
goto v___jp_2415_;
}
}
v___jp_2460_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = l_Array_append___redArg(v___x_2317_, v___y_2471_);
lean_dec_ref(v___y_2471_);
lean_inc(v___y_2463_);
v___x_2473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2473_, 0, v___y_2463_);
lean_ctor_set(v___x_2473_, 1, v___x_2316_);
lean_ctor_set(v___x_2473_, 2, v___x_2472_);
if (lean_obj_tag(v___y_2468_) == 1)
{
lean_object* v_val_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_val_2474_ = lean_ctor_get(v___y_2468_, 0);
lean_inc(v_val_2474_);
lean_dec_ref(v___y_2468_);
v___x_2475_ = l_Lean_SourceInfo_fromRef(v_val_2474_, v___x_2250_);
lean_dec(v_val_2474_);
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2477_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l_Array_mkArray1___redArg(v___x_2477_);
v___y_2435_ = v___y_2462_;
v___y_2436_ = v___y_2461_;
v___y_2437_ = v___y_2463_;
v___y_2438_ = v___y_2464_;
v___y_2439_ = v___y_2465_;
v___y_2440_ = v___y_2466_;
v___y_2441_ = v___y_2467_;
v___y_2442_ = v___x_2473_;
v___y_2443_ = v___y_2470_;
v___y_2444_ = v___y_2469_;
v___y_2445_ = v___x_2478_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2479_; 
lean_dec(v___y_2468_);
v___x_2479_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2435_ = v___y_2462_;
v___y_2436_ = v___y_2461_;
v___y_2437_ = v___y_2463_;
v___y_2438_ = v___y_2464_;
v___y_2439_ = v___y_2465_;
v___y_2440_ = v___y_2466_;
v___y_2441_ = v___y_2467_;
v___y_2442_ = v___x_2473_;
v___y_2443_ = v___y_2470_;
v___y_2444_ = v___y_2469_;
v___y_2445_ = v___x_2479_;
goto v___jp_2434_;
}
}
v___jp_2480_:
{
if (v___y_2484_ == 0)
{
lean_object* v___x_2496_; 
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2483_);
v___x_2496_ = lean_apply_9(v___f_2252_, v___y_2491_, v___y_2489_, v___y_2485_, v___y_2487_, v___y_2493_, v___y_2492_, v___y_2483_, v___y_2494_, lean_box(0));
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2496_);
lean_inc(v_a_2497_);
v___x_2498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_a_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_2253_);
lean_inc(v_a_2497_);
v___x_2499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2316_);
lean_ctor_set(v___x_2499_, 2, v___x_2317_);
if (lean_obj_tag(v___y_2495_) == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2380_ = v___y_2486_;
v___y_2381_ = v___y_2481_;
v___y_2382_ = v___y_2488_;
v___y_2383_ = v___y_2482_;
v___y_2384_ = v___y_2483_;
v___y_2385_ = v___y_2490_;
v___y_2386_ = v_a_2497_;
v___y_2387_ = v___x_2498_;
v___y_2388_ = v___x_2499_;
v___y_2389_ = v___y_2494_;
v___y_2390_ = v___x_2500_;
goto v___jp_2379_;
}
else
{
lean_object* v_val_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_val_2501_ = lean_ctor_get(v___y_2495_, 0);
lean_inc(v_val_2501_);
lean_dec_ref(v___y_2495_);
v___x_2502_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___x_2503_ = lean_array_push(v___x_2502_, v_val_2501_);
v___y_2380_ = v___y_2486_;
v___y_2381_ = v___y_2481_;
v___y_2382_ = v___y_2488_;
v___y_2383_ = v___y_2482_;
v___y_2384_ = v___y_2483_;
v___y_2385_ = v___y_2490_;
v___y_2386_ = v_a_2497_;
v___y_2387_ = v___x_2498_;
v___y_2388_ = v___x_2499_;
v___y_2389_ = v___y_2494_;
v___y_2390_ = v___x_2503_;
goto v___jp_2379_;
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___x_2253_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
lean_dec(v_tk_2244_);
v_a_2504_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2496_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2496_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v___x_2512_; 
lean_dec_ref(v___x_2253_);
lean_dec(v___x_2251_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2483_);
v___x_2512_ = lean_apply_9(v___f_2252_, v___y_2491_, v___y_2489_, v___y_2485_, v___y_2487_, v___y_2493_, v___y_2492_, v___y_2483_, v___y_2494_, lean_box(0));
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___x_2512_);
v___x_2514_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12));
lean_inc_ref(v___x_2247_);
lean_inc_ref(v___x_2246_);
lean_inc_ref(v___x_2245_);
v___x_2515_ = l_Lean_Name_mkStr4(v___x_2245_, v___x_2246_, v___x_2247_, v___x_2514_);
v___x_2516_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13));
lean_inc(v_a_2513_);
v___x_2517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2513_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
if (lean_obj_tag(v___y_2495_) == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2461_ = v___y_2486_;
v___y_2462_ = v___x_2515_;
v___y_2463_ = v_a_2513_;
v___y_2464_ = v___y_2481_;
v___y_2465_ = v___y_2488_;
v___y_2466_ = v___y_2482_;
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2490_;
v___y_2469_ = v___x_2517_;
v___y_2470_ = v___y_2494_;
v___y_2471_ = v___x_2518_;
goto v___jp_2460_;
}
else
{
lean_object* v_val_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_val_2519_ = lean_ctor_get(v___y_2495_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v___y_2495_);
v___x_2520_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___x_2521_ = lean_array_push(v___x_2520_, v_val_2519_);
v___y_2461_ = v___y_2486_;
v___y_2462_ = v___x_2515_;
v___y_2463_ = v_a_2513_;
v___y_2464_ = v___y_2481_;
v___y_2465_ = v___y_2488_;
v___y_2466_ = v___y_2482_;
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2490_;
v___y_2469_ = v___x_2517_;
v___y_2470_ = v___y_2494_;
v___y_2471_ = v___x_2521_;
goto v___jp_2460_;
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
lean_dec(v_tk_2244_);
v_a_2522_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2512_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2512_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
v___jp_2530_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2547_ = lean_unsigned_to_nat(5u);
v___x_2548_ = l_Lean_Syntax_getArg(v___y_2537_, v___x_2547_);
lean_dec(v___y_2537_);
v___x_2549_ = l_Lean_Syntax_matchesNull(v___x_2548_, v___x_2249_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v_args_2538_);
lean_dec(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec(v___y_2531_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
v___x_2550_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
v___x_2551_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2550_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref(v___x_2551_);
v___y_2304_ = v___y_2532_;
v_stx_2305_ = v_a_2552_;
v___y_2306_ = v___y_2545_;
v___y_2307_ = v___y_2546_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___y_2532_);
lean_dec(v_tk_2244_);
v_a_2553_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2551_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2551_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Syntax_getOptional_x3f(v___y_2535_);
lean_dec(v___y_2535_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_box(0);
v___y_2481_ = v_args_2538_;
v___y_2482_ = v___y_2533_;
v___y_2483_ = v___y_2545_;
v___y_2484_ = v___y_2536_;
v___y_2485_ = v___y_2541_;
v___y_2486_ = v___y_2531_;
v___y_2487_ = v___y_2542_;
v___y_2488_ = v___y_2532_;
v___y_2489_ = v___y_2540_;
v___y_2490_ = v___y_2534_;
v___y_2491_ = v___y_2539_;
v___y_2492_ = v___y_2544_;
v___y_2493_ = v___y_2543_;
v___y_2494_ = v___y_2546_;
v___y_2495_ = v___x_2562_;
goto v___jp_2480_;
}
else
{
lean_object* v_val_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_val_2563_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2561_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_val_2563_);
lean_dec(v___x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_val_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
v___y_2481_ = v_args_2538_;
v___y_2482_ = v___y_2533_;
v___y_2483_ = v___y_2545_;
v___y_2484_ = v___y_2536_;
v___y_2485_ = v___y_2541_;
v___y_2486_ = v___y_2531_;
v___y_2487_ = v___y_2542_;
v___y_2488_ = v___y_2532_;
v___y_2489_ = v___y_2540_;
v___y_2490_ = v___y_2534_;
v___y_2491_ = v___y_2539_;
v___y_2492_ = v___y_2544_;
v___y_2493_ = v___y_2543_;
v___y_2494_ = v___y_2546_;
v___y_2495_ = v___x_2568_;
goto v___jp_2480_;
}
}
}
}
}
v___jp_2571_:
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = l_Lean_Syntax_getArg(v___y_2577_, v___x_2254_);
v___x_2588_ = l_Lean_Syntax_isNone(v___x_2587_);
if (v___x_2588_ == 0)
{
uint8_t v___x_2589_; 
lean_inc(v___x_2587_);
v___x_2589_ = l_Lean_Syntax_matchesNull(v___x_2587_, v___x_2255_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v___x_2587_);
lean_dec(v_only_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2572_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
v___x_2590_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
lean_inc(v___y_2586_);
lean_inc_ref(v___y_2585_);
v___x_2591_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2590_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
v___y_2304_ = v___y_2573_;
v_stx_2305_ = v_a_2592_;
v___y_2306_ = v___y_2585_;
v___y_2307_ = v___y_2586_;
goto v___jp_2303_;
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2573_);
lean_dec(v_tk_2244_);
v_a_2593_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2591_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2591_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = l_Lean_Syntax_getArg(v___x_2587_, v___x_2256_);
lean_dec(v___x_2256_);
lean_dec(v___x_2587_);
v___x_2602_ = l_Lean_Syntax_getArgs(v___x_2601_);
lean_dec(v___x_2601_);
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
v___y_2531_ = v___y_2572_;
v___y_2532_ = v___y_2573_;
v___y_2533_ = v___y_2574_;
v___y_2534_ = v_only_2578_;
v___y_2535_ = v___y_2575_;
v___y_2536_ = v___y_2576_;
v___y_2537_ = v___y_2577_;
v_args_2538_ = v___x_2603_;
v___y_2539_ = v___y_2579_;
v___y_2540_ = v___y_2580_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2584_;
v___y_2545_ = v___y_2585_;
v___y_2546_ = v___y_2586_;
goto v___jp_2530_;
}
}
else
{
lean_object* v___x_2604_; 
lean_dec(v___x_2587_);
lean_dec(v___x_2256_);
v___x_2604_ = lean_box(0);
v___y_2531_ = v___y_2572_;
v___y_2532_ = v___y_2573_;
v___y_2533_ = v___y_2574_;
v___y_2534_ = v_only_2578_;
v___y_2535_ = v___y_2575_;
v___y_2536_ = v___y_2576_;
v___y_2537_ = v___y_2577_;
v_args_2538_ = v___x_2604_;
v___y_2539_ = v___y_2579_;
v___y_2540_ = v___y_2580_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2584_;
v___y_2545_ = v___y_2585_;
v___y_2546_ = v___y_2586_;
goto v___jp_2530_;
}
}
v___jp_2605_:
{
lean_object* v_usedTheorems_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_usedTheorems_2610_ = lean_ctor_get(v___y_2606_, 0);
v___x_2611_ = l_Lean_Syntax_unsetTrailing(v___y_2607_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
v___x_2612_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2611_, v_usedTheorems_2610_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; uint8_t v___x_2614_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
lean_inc(v_a_2613_);
v___x_2614_ = l_Lean_Syntax_isOfKind(v_a_2613_, v___x_2314_);
lean_dec(v___x_2314_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_inc(v_ref_2310_);
lean_dec(v_a_2613_);
lean_dec(v___y_2609_);
lean_dec(v___x_2258_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
v___x_2615_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
v___x_2616_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2615_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref(v___x_2616_);
v___y_2282_ = v___y_2606_;
v_stx_2283_ = v_a_2617_;
v___y_2284_ = v___y_2274_;
v_ref_2285_ = v_ref_2310_;
v___y_2286_ = v___y_2275_;
goto v___jp_2281_;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v___y_2606_);
lean_dec(v_ref_2310_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v_tk_2244_);
v_a_2618_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2616_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = l_Lean_Syntax_getArg(v_a_2613_, v___x_2256_);
lean_inc(v___x_2626_);
v___x_2627_ = l_Lean_Syntax_isOfKind(v___x_2626_, v___x_2257_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_inc(v_ref_2310_);
lean_dec(v___x_2626_);
lean_dec(v_a_2613_);
lean_dec(v___y_2609_);
lean_dec(v___x_2258_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
v___x_2628_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
v___x_2629_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2628_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2629_);
v___y_2282_ = v___y_2606_;
v_stx_2283_ = v_a_2630_;
v___y_2284_ = v___y_2274_;
v_ref_2285_ = v_ref_2310_;
v___y_2286_ = v___y_2275_;
goto v___jp_2281_;
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___y_2606_);
lean_dec(v_ref_2310_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v_tk_2244_);
v_a_2631_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2629_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2629_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2639_ = l_Lean_Syntax_getArg(v_a_2613_, v___x_2258_);
lean_dec(v___x_2258_);
v___x_2640_ = l_Lean_Syntax_getArg(v_a_2613_, v___x_2255_);
v___x_2641_ = l_Lean_Syntax_isNone(v___x_2640_);
if (v___x_2641_ == 0)
{
uint8_t v___x_2642_; 
lean_inc(v___x_2640_);
v___x_2642_ = l_Lean_Syntax_matchesNull(v___x_2640_, v___x_2256_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_inc(v_ref_2310_);
lean_dec(v___x_2640_);
lean_dec(v___x_2639_);
lean_dec(v___x_2626_);
lean_dec(v_a_2613_);
lean_dec(v___y_2609_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
v___x_2643_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
v___x_2644_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2643_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2644_);
v___y_2282_ = v___y_2606_;
v_stx_2283_ = v_a_2645_;
v___y_2284_ = v___y_2274_;
v_ref_2285_ = v_ref_2310_;
v___y_2286_ = v___y_2275_;
goto v___jp_2281_;
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v___y_2606_);
lean_dec(v_ref_2310_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v_tk_2244_);
v_a_2646_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2644_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2644_);
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
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = l_Lean_Syntax_getArg(v___x_2640_, v___x_2249_);
lean_dec(v___x_2640_);
v___x_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
v___y_2572_ = v___x_2626_;
v___y_2573_ = v___y_2606_;
v___y_2574_ = v___y_2609_;
v___y_2575_ = v___x_2639_;
v___y_2576_ = v___y_2608_;
v___y_2577_ = v_a_2613_;
v_only_2578_ = v___x_2655_;
v___y_2579_ = v___y_2268_;
v___y_2580_ = v___y_2269_;
v___y_2581_ = v___y_2270_;
v___y_2582_ = v___y_2271_;
v___y_2583_ = v___y_2272_;
v___y_2584_ = v___y_2273_;
v___y_2585_ = v___y_2274_;
v___y_2586_ = v___y_2275_;
goto v___jp_2571_;
}
}
else
{
lean_object* v___x_2656_; 
lean_dec(v___x_2640_);
v___x_2656_ = lean_box(0);
v___y_2572_ = v___x_2626_;
v___y_2573_ = v___y_2606_;
v___y_2574_ = v___y_2609_;
v___y_2575_ = v___x_2639_;
v___y_2576_ = v___y_2608_;
v___y_2577_ = v_a_2613_;
v_only_2578_ = v___x_2656_;
v___y_2579_ = v___y_2268_;
v___y_2580_ = v___y_2269_;
v___y_2581_ = v___y_2270_;
v___y_2582_ = v___y_2271_;
v___y_2583_ = v___y_2272_;
v___y_2584_ = v___y_2273_;
v___y_2585_ = v___y_2274_;
v___y_2586_ = v___y_2275_;
goto v___jp_2571_;
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2606_);
lean_dec(v___x_2314_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___x_2258_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
lean_dec(v_tk_2244_);
v_a_2657_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2612_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2612_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
v___jp_2665_:
{
if (lean_obj_tag(v_usingArg_2259_) == 0)
{
v___y_2606_ = v___y_2666_;
v___y_2607_ = v___y_2667_;
v___y_2608_ = v___y_2668_;
v___y_2609_ = v_usingArg_2259_;
goto v___jp_2605_;
}
else
{
lean_object* v_val_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2677_; 
v_val_2669_ = lean_ctor_get(v_usingArg_2259_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_usingArg_2259_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2671_ = v_usingArg_2259_;
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_val_2669_);
lean_dec(v_usingArg_2259_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = l_Lean_Syntax_unsetTrailing(v_val_2669_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
v___y_2606_ = v___y_2666_;
v___y_2607_ = v___y_2667_;
v___y_2608_ = v___y_2668_;
v___y_2609_ = v___x_2675_;
goto v___jp_2605_;
}
}
}
}
v___jp_2678_:
{
if (v___y_2682_ == 0)
{
lean_dec(v___y_2680_);
lean_dec(v___x_2314_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v_usingArg_2259_);
lean_dec(v___x_2258_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
lean_dec(v_tk_2244_);
v___y_2278_ = v___y_2679_;
goto v___jp_2277_;
}
else
{
v___y_2666_ = v___y_2679_;
v___y_2667_ = v___y_2680_;
v___y_2668_ = v___y_2681_;
goto v___jp_2665_;
}
}
v___jp_2683_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___f_2693_; lean_object* v___x_2694_; 
v___x_2689_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_2688_, v___x_2311_);
v___x_2690_ = lean_box(v___x_2250_);
v___x_2691_ = lean_box(v___x_2311_);
v___x_2692_ = lean_box(v___x_2261_);
lean_inc(v___x_2256_);
lean_inc_ref(v___x_2253_);
lean_inc(v_usingArg_2259_);
lean_inc(v___x_2249_);
lean_inc(v_tk_2244_);
lean_inc(v___x_2258_);
v___f_2693_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 23, 13);
lean_closure_set(v___f_2693_, 0, v___x_2258_);
lean_closure_set(v___f_2693_, 1, v_tk_2244_);
lean_closure_set(v___f_2693_, 2, v___x_2316_);
lean_closure_set(v___f_2693_, 3, v___x_2249_);
lean_closure_set(v___f_2693_, 4, v___x_2689_);
lean_closure_set(v___f_2693_, 5, v___y_2684_);
lean_closure_set(v___f_2693_, 6, v___x_2690_);
lean_closure_set(v___f_2693_, 7, v_usingArg_2259_);
lean_closure_set(v___f_2693_, 8, v___x_2691_);
lean_closure_set(v___f_2693_, 9, v___x_2692_);
lean_closure_set(v___f_2693_, 10, v___x_2253_);
lean_closure_set(v___f_2693_, 11, v___x_2256_);
lean_closure_set(v___f_2693_, 12, v_usingTk_x3f_2262_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
v___x_2694_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_2687_, v___f_2693_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2687_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_2697_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_2309_, v___x_2696_);
if (v___x_2697_ == 0)
{
if (lean_obj_tag(v_squeeze_2263_) == 0)
{
v___y_2679_ = v_a_2695_;
v___y_2680_ = v___y_2685_;
v___y_2681_ = v___y_2686_;
v___y_2682_ = v___x_2697_;
goto v___jp_2678_;
}
else
{
v___y_2679_ = v_a_2695_;
v___y_2680_ = v___y_2685_;
v___y_2681_ = v___y_2686_;
v___y_2682_ = v___x_2261_;
goto v___jp_2678_;
}
}
else
{
v___y_2666_ = v_a_2695_;
v___y_2667_ = v___y_2685_;
v___y_2668_ = v___y_2686_;
goto v___jp_2665_;
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v___y_2685_);
lean_dec(v___x_2314_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v_usingArg_2259_);
lean_dec(v___x_2258_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
lean_dec(v_tk_2244_);
v_a_2698_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2694_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2694_);
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
v___jp_2706_:
{
v___y_2684_ = v___y_2708_;
v___y_2685_ = v___y_2710_;
v___y_2686_ = v___x_2311_;
v___y_2687_ = v___y_2707_;
v___y_2688_ = v___y_2709_;
goto v___jp_2683_;
}
v___jp_2711_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2715_ = l_Array_append___redArg(v___x_2317_, v___y_2714_);
lean_dec_ref(v___y_2714_);
lean_inc(v___x_2312_);
v___x_2716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2312_);
lean_ctor_set(v___x_2716_, 1, v___x_2316_);
lean_ctor_set(v___x_2716_, 2, v___x_2715_);
lean_inc(v___x_2312_);
v___x_2717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2312_);
lean_ctor_set(v___x_2717_, 1, v___x_2316_);
lean_ctor_set(v___x_2717_, 2, v___x_2317_);
lean_inc(v___x_2314_);
v___x_2718_ = l_Lean_Syntax_node6(v___x_2312_, v___x_2314_, v___x_2315_, v___x_2260_, v___y_2712_, v___y_2713_, v___x_2716_, v___x_2717_);
v___x_2719_ = 0;
v___x_2720_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18));
v___x_2721_ = lean_box(v___x_2311_);
v___x_2722_ = lean_box(v___x_2719_);
v___x_2723_ = lean_box(v___x_2311_);
lean_inc(v___x_2718_);
v___x_2724_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_2724_, 0, v___x_2718_);
lean_closure_set(v___x_2724_, 1, v___x_2721_);
lean_closure_set(v___x_2724_, 2, v___x_2722_);
lean_closure_set(v___x_2724_, 3, v___x_2723_);
lean_closure_set(v___x_2724_, 4, v___x_2720_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
v___x_2725_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2724_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref(v___x_2725_);
if (lean_obj_tag(v_unfold_2264_) == 0)
{
lean_object* v_ctx_2727_; lean_object* v_simprocs_2728_; lean_object* v_dischargeWrapper_2729_; 
v_ctx_2727_ = lean_ctor_get(v_a_2726_, 0);
lean_inc_ref(v_ctx_2727_);
v_simprocs_2728_ = lean_ctor_get(v_a_2726_, 1);
lean_inc_ref(v_simprocs_2728_);
v_dischargeWrapper_2729_ = lean_ctor_get(v_a_2726_, 2);
lean_inc(v_dischargeWrapper_2729_);
lean_dec(v_a_2726_);
v___y_2707_ = v_dischargeWrapper_2729_;
v___y_2708_ = v_simprocs_2728_;
v___y_2709_ = v_ctx_2727_;
v___y_2710_ = v___x_2718_;
goto v___jp_2706_;
}
else
{
if (v___x_2261_ == 0)
{
lean_object* v_ctx_2730_; lean_object* v_simprocs_2731_; lean_object* v_dischargeWrapper_2732_; 
v_ctx_2730_ = lean_ctor_get(v_a_2726_, 0);
lean_inc_ref(v_ctx_2730_);
v_simprocs_2731_ = lean_ctor_get(v_a_2726_, 1);
lean_inc_ref(v_simprocs_2731_);
v_dischargeWrapper_2732_ = lean_ctor_get(v_a_2726_, 2);
lean_inc(v_dischargeWrapper_2732_);
lean_dec(v_a_2726_);
v___y_2707_ = v_dischargeWrapper_2732_;
v___y_2708_ = v_simprocs_2731_;
v___y_2709_ = v_ctx_2730_;
v___y_2710_ = v___x_2718_;
goto v___jp_2706_;
}
else
{
lean_object* v_ctx_2733_; lean_object* v_simprocs_2734_; lean_object* v_dischargeWrapper_2735_; lean_object* v___x_2736_; 
v_ctx_2733_ = lean_ctor_get(v_a_2726_, 0);
lean_inc_ref(v_ctx_2733_);
v_simprocs_2734_ = lean_ctor_get(v_a_2726_, 1);
lean_inc_ref(v_simprocs_2734_);
v_dischargeWrapper_2735_ = lean_ctor_get(v_a_2726_, 2);
lean_inc(v_dischargeWrapper_2735_);
lean_dec(v_a_2726_);
v___x_2736_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2733_);
v___y_2684_ = v_simprocs_2734_;
v___y_2685_ = v___x_2718_;
v___y_2686_ = v___x_2261_;
v___y_2687_ = v_dischargeWrapper_2735_;
v___y_2688_ = v___x_2736_;
goto v___jp_2683_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v___x_2718_);
lean_dec(v___x_2314_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v_usingTk_x3f_2262_);
lean_dec(v_usingArg_2259_);
lean_dec(v___x_2258_);
lean_dec(v___x_2256_);
lean_dec_ref(v___x_2253_);
lean_dec_ref(v___f_2252_);
lean_dec(v___x_2251_);
lean_dec(v___x_2249_);
lean_dec(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec_ref(v___x_2245_);
lean_dec(v_tk_2244_);
v_a_2737_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2725_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2725_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
v___jp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = l_Array_append___redArg(v___x_2317_, v___y_2747_);
lean_dec_ref(v___y_2747_);
lean_inc(v___x_2312_);
v___x_2749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2312_);
lean_ctor_set(v___x_2749_, 1, v___x_2316_);
lean_ctor_set(v___x_2749_, 2, v___x_2748_);
if (lean_obj_tag(v_args_2265_) == 1)
{
lean_object* v_val_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_val_2750_ = lean_ctor_get(v_args_2265_, 0);
v___x_2751_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc(v___x_2312_);
v___x_2752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2312_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = l_Array_append___redArg(v___x_2317_, v_val_2750_);
lean_inc(v___x_2312_);
v___x_2754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2312_);
lean_ctor_set(v___x_2754_, 1, v___x_2316_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
lean_inc(v___x_2312_);
v___x_2756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2312_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Array_mkArray3___redArg(v___x_2752_, v___x_2754_, v___x_2756_);
v___y_2712_ = v___y_2746_;
v___y_2713_ = v___x_2749_;
v___y_2714_ = v___x_2757_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2712_ = v___y_2746_;
v___y_2713_ = v___x_2749_;
v___y_2714_ = v___x_2758_;
goto v___jp_2711_;
}
}
v___jp_2759_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = l_Array_append___redArg(v___x_2317_, v___y_2760_);
lean_dec_ref(v___y_2760_);
lean_inc(v___x_2312_);
v___x_2762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2312_);
lean_ctor_set(v___x_2762_, 1, v___x_2316_);
lean_ctor_set(v___x_2762_, 2, v___x_2761_);
if (lean_obj_tag(v_only_2266_) == 1)
{
lean_object* v_val_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_val_2763_ = lean_ctor_get(v_only_2266_, 0);
v___x_2764_ = l_Lean_SourceInfo_fromRef(v_val_2763_, v___x_2250_);
v___x_2765_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = l_Array_mkArray1___redArg(v___x_2766_);
v___y_2746_ = v___x_2762_;
v___y_2747_ = v___x_2767_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_mk_empty_array_with_capacity(v___x_2249_);
v___y_2746_ = v___x_2762_;
v___y_2747_ = v___x_2768_;
goto v___jp_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object** _args){
lean_object* v_tk_2773_ = _args[0];
lean_object* v___x_2774_ = _args[1];
lean_object* v___x_2775_ = _args[2];
lean_object* v___x_2776_ = _args[3];
lean_object* v___x_2777_ = _args[4];
lean_object* v___x_2778_ = _args[5];
lean_object* v___x_2779_ = _args[6];
lean_object* v___x_2780_ = _args[7];
lean_object* v___f_2781_ = _args[8];
lean_object* v___x_2782_ = _args[9];
lean_object* v___x_2783_ = _args[10];
lean_object* v___x_2784_ = _args[11];
lean_object* v___x_2785_ = _args[12];
lean_object* v___x_2786_ = _args[13];
lean_object* v___x_2787_ = _args[14];
lean_object* v_usingArg_2788_ = _args[15];
lean_object* v___x_2789_ = _args[16];
lean_object* v___x_2790_ = _args[17];
lean_object* v_usingTk_x3f_2791_ = _args[18];
lean_object* v_squeeze_2792_ = _args[19];
lean_object* v_unfold_2793_ = _args[20];
lean_object* v_args_2794_ = _args[21];
lean_object* v_only_2795_ = _args[22];
lean_object* v___y_2796_ = _args[23];
lean_object* v___y_2797_ = _args[24];
lean_object* v___y_2798_ = _args[25];
lean_object* v___y_2799_ = _args[26];
lean_object* v___y_2800_ = _args[27];
lean_object* v___y_2801_ = _args[28];
lean_object* v___y_2802_ = _args[29];
lean_object* v___y_2803_ = _args[30];
lean_object* v___y_2804_ = _args[31];
lean_object* v___y_2805_ = _args[32];
_start:
{
uint8_t v___x_83242__boxed_2806_; uint8_t v___x_83252__boxed_2807_; lean_object* v_res_2808_; 
v___x_83242__boxed_2806_ = lean_unbox(v___x_2779_);
v___x_83252__boxed_2807_ = lean_unbox(v___x_2790_);
v_res_2808_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(v_tk_2773_, v___x_2774_, v___x_2775_, v___x_2776_, v___x_2777_, v___x_2778_, v___x_83242__boxed_2806_, v___x_2780_, v___f_2781_, v___x_2782_, v___x_2783_, v___x_2784_, v___x_2785_, v___x_2786_, v___x_2787_, v_usingArg_2788_, v___x_2789_, v___x_83252__boxed_2807_, v_usingTk_x3f_2791_, v_squeeze_2792_, v_unfold_2793_, v_args_2794_, v_only_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v_only_2795_);
lean_dec(v_args_2794_);
lean_dec(v_unfold_2793_);
lean_dec(v_squeeze_2792_);
lean_dec(v___x_2786_);
lean_dec(v___x_2784_);
lean_dec(v___x_2783_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_stx_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2845_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0));
v___x_2846_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1));
v___x_2847_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_2848_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2));
v___x_2849_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
lean_inc(v_stx_2835_);
v___x_2850_ = l_Lean_Syntax_isOfKind(v_stx_2835_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_stx_2835_);
v___x_2851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2851_;
}
else
{
lean_object* v___f_2852_; lean_object* v___x_2853_; lean_object* v_tk_2854_; lean_object* v___x_2855_; lean_object* v___y_2857_; uint8_t v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2885_; uint8_t v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v_usingTk_x3f_2905_; lean_object* v_usingArg_2906_; lean_object* v___y_2918_; lean_object* v___y_2919_; uint8_t v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v_args_2938_; uint8_t v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v_only_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v_unfold_2994_; lean_object* v_squeeze_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___f_2852_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4));
v___x_2853_ = lean_unsigned_to_nat(0u);
v_tk_2854_ = l_Lean_Syntax_getArg(v_stx_2835_, v___x_2853_);
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_3030_ = l_Lean_Syntax_getArg(v_stx_2835_, v___x_2855_);
v___x_3031_ = l_Lean_Syntax_isNone(v___x_3030_);
if (v___x_3031_ == 0)
{
uint8_t v___x_3032_; 
lean_inc(v___x_3030_);
v___x_3032_ = l_Lean_Syntax_matchesNull(v___x_3030_, v___x_2855_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
lean_dec(v___x_3030_);
lean_dec(v_tk_2854_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_stx_2835_);
v___x_3033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3033_;
}
else
{
lean_object* v_squeeze_3034_; lean_object* v___x_3035_; 
v_squeeze_3034_ = l_Lean_Syntax_getArg(v___x_3030_, v___x_2853_);
lean_dec(v___x_3030_);
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_squeeze_3034_);
v_squeeze_3013_ = v___x_3035_;
v___y_3014_ = v_a_2836_;
v___y_3015_ = v_a_2837_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
v___y_3019_ = v_a_2841_;
v___y_3020_ = v_a_2842_;
v___y_3021_ = v_a_2843_;
goto v___jp_3012_;
}
}
else
{
lean_object* v___x_3036_; 
lean_dec(v___x_3030_);
v___x_3036_ = lean_box(0);
v_squeeze_3013_ = v___x_3036_;
v___y_3014_ = v_a_2836_;
v___y_3015_ = v_a_2837_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
v___y_3019_ = v_a_2841_;
v___y_3020_ = v_a_2842_;
v___y_3021_ = v_a_2843_;
goto v___jp_3012_;
}
v___jp_2856_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___f_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2879_ = lean_box(v___x_2850_);
v___x_2880_ = lean_box(v___y_2858_);
v___f_2881_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 33, 24);
lean_closure_set(v___f_2881_, 0, v_tk_2854_);
lean_closure_set(v___f_2881_, 1, v___x_2845_);
lean_closure_set(v___f_2881_, 2, v___x_2846_);
lean_closure_set(v___f_2881_, 3, v___x_2847_);
lean_closure_set(v___f_2881_, 4, v___y_2864_);
lean_closure_set(v___f_2881_, 5, v___x_2853_);
lean_closure_set(v___f_2881_, 6, v___x_2879_);
lean_closure_set(v___f_2881_, 7, v___x_2849_);
lean_closure_set(v___f_2881_, 8, v___f_2852_);
lean_closure_set(v___f_2881_, 9, v___x_2848_);
lean_closure_set(v___f_2881_, 10, v___y_2875_);
lean_closure_set(v___f_2881_, 11, v___y_2867_);
lean_closure_set(v___f_2881_, 12, v___x_2855_);
lean_closure_set(v___f_2881_, 13, v___y_2857_);
lean_closure_set(v___f_2881_, 14, v___y_2869_);
lean_closure_set(v___f_2881_, 15, v___y_2859_);
lean_closure_set(v___f_2881_, 16, v___y_2872_);
lean_closure_set(v___f_2881_, 17, v___x_2880_);
lean_closure_set(v___f_2881_, 18, v___y_2862_);
lean_closure_set(v___f_2881_, 19, v___y_2876_);
lean_closure_set(v___f_2881_, 20, v___y_2870_);
lean_closure_set(v___f_2881_, 21, v___y_2868_);
lean_closure_set(v___f_2881_, 22, v___y_2877_);
lean_closure_set(v___f_2881_, 23, v___y_2878_);
v___x_2882_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2882_, 0, v___f_2881_);
v___x_2883_ = l_Lean_Elab_Tactic_focus___redArg(v___x_2882_, v___y_2860_, v___y_2866_, v___y_2874_, v___y_2861_, v___y_2863_, v___y_2871_, v___y_2865_, v___y_2873_);
return v___x_2883_;
}
v___jp_2884_:
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_Syntax_getOptional_x3f(v___y_2899_);
lean_dec(v___y_2899_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_box(0);
v___y_2857_ = v___y_2885_;
v___y_2858_ = v___y_2886_;
v___y_2859_ = v_usingArg_2906_;
v___y_2860_ = v___y_2887_;
v___y_2861_ = v___y_2888_;
v___y_2862_ = v_usingTk_x3f_2905_;
v___y_2863_ = v___y_2889_;
v___y_2864_ = v___y_2890_;
v___y_2865_ = v___y_2891_;
v___y_2866_ = v___y_2892_;
v___y_2867_ = v___y_2893_;
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2895_;
v___y_2870_ = v___y_2896_;
v___y_2871_ = v___y_2898_;
v___y_2872_ = v___y_2897_;
v___y_2873_ = v___y_2901_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2902_;
v___y_2876_ = v___y_2903_;
v___y_2877_ = v___y_2904_;
v___y_2878_ = v___x_2908_;
goto v___jp_2856_;
}
else
{
lean_object* v_val_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_val_2909_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2907_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_val_2909_);
lean_dec(v___x_2907_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_val_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
v___y_2857_ = v___y_2885_;
v___y_2858_ = v___y_2886_;
v___y_2859_ = v_usingArg_2906_;
v___y_2860_ = v___y_2887_;
v___y_2861_ = v___y_2888_;
v___y_2862_ = v_usingTk_x3f_2905_;
v___y_2863_ = v___y_2889_;
v___y_2864_ = v___y_2890_;
v___y_2865_ = v___y_2891_;
v___y_2866_ = v___y_2892_;
v___y_2867_ = v___y_2893_;
v___y_2868_ = v___y_2894_;
v___y_2869_ = v___y_2895_;
v___y_2870_ = v___y_2896_;
v___y_2871_ = v___y_2898_;
v___y_2872_ = v___y_2897_;
v___y_2873_ = v___y_2901_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2902_;
v___y_2876_ = v___y_2903_;
v___y_2877_ = v___y_2904_;
v___y_2878_ = v___x_2914_;
goto v___jp_2856_;
}
}
}
}
v___jp_2917_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2939_ = lean_unsigned_to_nat(4u);
v___x_2940_ = l_Lean_Syntax_getArg(v___y_2936_, v___x_2939_);
lean_dec(v___y_2936_);
v___x_2941_ = l_Lean_Syntax_isNone(v___x_2940_);
if (v___x_2941_ == 0)
{
uint8_t v___x_2942_; 
lean_inc(v___x_2940_);
v___x_2942_ = l_Lean_Syntax_matchesNull(v___x_2940_, v___y_2918_);
lean_dec(v___y_2918_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v___x_2940_);
lean_dec(v_args_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2919_);
lean_dec(v_tk_2854_);
v___x_2943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2943_;
}
else
{
lean_object* v_usingTk_x3f_2944_; lean_object* v_usingArg_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_usingTk_x3f_2944_ = l_Lean_Syntax_getArg(v___x_2940_, v___x_2853_);
v_usingArg_2945_ = l_Lean_Syntax_getArg(v___x_2940_, v___x_2855_);
lean_dec(v___x_2940_);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_usingTk_x3f_2944_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_usingArg_2945_);
v___y_2885_ = v___y_2919_;
v___y_2886_ = v___y_2920_;
v___y_2887_ = v___y_2921_;
v___y_2888_ = v___y_2922_;
v___y_2889_ = v___y_2923_;
v___y_2890_ = v___y_2924_;
v___y_2891_ = v___y_2925_;
v___y_2892_ = v___y_2926_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v_args_2938_;
v___y_2895_ = v___y_2928_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2931_;
v___y_2898_ = v___y_2930_;
v___y_2899_ = v___y_2934_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2932_;
v___y_2902_ = v___x_2939_;
v___y_2903_ = v___y_2935_;
v___y_2904_ = v___y_2937_;
v_usingTk_x3f_2905_ = v___x_2946_;
v_usingArg_2906_ = v___x_2947_;
goto v___jp_2884_;
}
}
else
{
lean_object* v___x_2948_; 
lean_dec(v___x_2940_);
lean_dec(v___y_2918_);
v___x_2948_ = lean_box(0);
v___y_2885_ = v___y_2919_;
v___y_2886_ = v___y_2920_;
v___y_2887_ = v___y_2921_;
v___y_2888_ = v___y_2922_;
v___y_2889_ = v___y_2923_;
v___y_2890_ = v___y_2924_;
v___y_2891_ = v___y_2925_;
v___y_2892_ = v___y_2926_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v_args_2938_;
v___y_2895_ = v___y_2928_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2931_;
v___y_2898_ = v___y_2930_;
v___y_2899_ = v___y_2934_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2932_;
v___y_2902_ = v___x_2939_;
v___y_2903_ = v___y_2935_;
v___y_2904_ = v___y_2937_;
v_usingTk_x3f_2905_ = v___x_2948_;
v_usingArg_2906_ = v___x_2948_;
goto v___jp_2884_;
}
}
v___jp_2949_:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = l_Lean_Syntax_getArg(v___y_2961_, v___y_2958_);
lean_dec(v___y_2958_);
v___x_2972_ = l_Lean_Syntax_isNone(v___x_2971_);
if (v___x_2972_ == 0)
{
uint8_t v___x_2973_; 
lean_inc(v___x_2971_);
v___x_2973_ = l_Lean_Syntax_matchesNull(v___x_2971_, v___x_2855_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec(v___x_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v_only_2962_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec(v_tk_2854_);
v___x_2974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2974_;
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2975_ = l_Lean_Syntax_getArg(v___x_2971_, v___x_2853_);
lean_dec(v___x_2971_);
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5));
lean_inc(v___x_2975_);
v___x_2977_ = l_Lean_Syntax_isOfKind(v___x_2975_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v___x_2975_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v_only_2962_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec(v_tk_2854_);
v___x_2978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; lean_object* v_args_2980_; lean_object* v___x_2981_; 
v___x_2979_ = l_Lean_Syntax_getArg(v___x_2975_, v___x_2855_);
lean_dec(v___x_2975_);
v_args_2980_ = l_Lean_Syntax_getArgs(v___x_2979_);
lean_dec(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_args_2980_);
v___y_2918_ = v___y_2959_;
v___y_2919_ = v___y_2951_;
v___y_2920_ = v___y_2950_;
v___y_2921_ = v___y_2963_;
v___y_2922_ = v___y_2966_;
v___y_2923_ = v___y_2967_;
v___y_2924_ = v___y_2956_;
v___y_2925_ = v___y_2969_;
v___y_2926_ = v___y_2964_;
v___y_2927_ = v___y_2952_;
v___y_2928_ = v___y_2953_;
v___y_2929_ = v___y_2954_;
v___y_2930_ = v___y_2968_;
v___y_2931_ = v___y_2955_;
v___y_2932_ = v___y_2970_;
v___y_2933_ = v___y_2965_;
v___y_2934_ = v___y_2960_;
v___y_2935_ = v___y_2957_;
v___y_2936_ = v___y_2961_;
v___y_2937_ = v_only_2962_;
v_args_2938_ = v___x_2981_;
goto v___jp_2917_;
}
}
}
else
{
lean_object* v___x_2982_; 
lean_dec(v___x_2971_);
v___x_2982_ = lean_box(0);
v___y_2918_ = v___y_2959_;
v___y_2919_ = v___y_2951_;
v___y_2920_ = v___y_2950_;
v___y_2921_ = v___y_2963_;
v___y_2922_ = v___y_2966_;
v___y_2923_ = v___y_2967_;
v___y_2924_ = v___y_2956_;
v___y_2925_ = v___y_2969_;
v___y_2926_ = v___y_2964_;
v___y_2927_ = v___y_2952_;
v___y_2928_ = v___y_2953_;
v___y_2929_ = v___y_2954_;
v___y_2930_ = v___y_2968_;
v___y_2931_ = v___y_2955_;
v___y_2932_ = v___y_2970_;
v___y_2933_ = v___y_2965_;
v___y_2934_ = v___y_2960_;
v___y_2935_ = v___y_2957_;
v___y_2936_ = v___y_2961_;
v___y_2937_ = v_only_2962_;
v_args_2938_ = v___x_2982_;
goto v___jp_2917_;
}
}
v___jp_2983_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2995_ = lean_unsigned_to_nat(3u);
v___x_2996_ = l_Lean_Syntax_getArg(v_stx_2835_, v___x_2995_);
lean_dec(v_stx_2835_);
v___x_2997_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7));
lean_inc(v___x_2996_);
v___x_2998_ = l_Lean_Syntax_isOfKind(v___x_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
lean_dec(v___x_2996_);
lean_dec(v_unfold_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v_tk_2854_);
v___x_2999_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3000_ = l_Lean_Syntax_getArg(v___x_2996_, v___x_2853_);
v___x_3001_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9));
lean_inc(v___x_3000_);
v___x_3002_ = l_Lean_Syntax_isOfKind(v___x_3000_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
lean_dec(v___x_3000_);
lean_dec(v___x_2996_);
lean_dec(v_unfold_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v_tk_2854_);
v___x_3003_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3004_ = l_Lean_Syntax_getArg(v___x_2996_, v___x_2855_);
v___x_3005_ = l_Lean_Syntax_getArg(v___x_2996_, v___y_2989_);
v___x_3006_ = l_Lean_Syntax_isNone(v___x_3005_);
if (v___x_3006_ == 0)
{
uint8_t v___x_3007_; 
lean_inc(v___x_3005_);
v___x_3007_ = l_Lean_Syntax_matchesNull(v___x_3005_, v___x_2855_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec(v___x_3005_);
lean_dec(v___x_3004_);
lean_dec(v___x_3000_);
lean_dec(v___x_2996_);
lean_dec(v_unfold_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v_tk_2854_);
v___x_3008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3008_;
}
else
{
lean_object* v_only_3009_; lean_object* v___x_3010_; 
v_only_3009_ = l_Lean_Syntax_getArg(v___x_3005_, v___x_2853_);
lean_dec(v___x_3005_);
v___x_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_only_3009_);
lean_inc(v___y_2989_);
v___y_2950_ = v___x_3002_;
v___y_2951_ = v___x_3001_;
v___y_2952_ = v___x_2995_;
v___y_2953_ = v___y_2989_;
v___y_2954_ = v_unfold_2994_;
v___y_2955_ = v___x_3000_;
v___y_2956_ = v___x_2997_;
v___y_2957_ = v___y_2992_;
v___y_2958_ = v___x_2995_;
v___y_2959_ = v___y_2989_;
v___y_2960_ = v___x_3004_;
v___y_2961_ = v___x_2996_;
v_only_2962_ = v___x_3010_;
v___y_2963_ = v___y_2986_;
v___y_2964_ = v___y_2988_;
v___y_2965_ = v___y_2990_;
v___y_2966_ = v___y_2985_;
v___y_2967_ = v___y_2993_;
v___y_2968_ = v___y_2987_;
v___y_2969_ = v___y_2984_;
v___y_2970_ = v___y_2991_;
goto v___jp_2949_;
}
}
else
{
lean_object* v___x_3011_; 
lean_dec(v___x_3005_);
v___x_3011_ = lean_box(0);
lean_inc(v___y_2989_);
v___y_2950_ = v___x_3002_;
v___y_2951_ = v___x_3001_;
v___y_2952_ = v___x_2995_;
v___y_2953_ = v___y_2989_;
v___y_2954_ = v_unfold_2994_;
v___y_2955_ = v___x_3000_;
v___y_2956_ = v___x_2997_;
v___y_2957_ = v___y_2992_;
v___y_2958_ = v___x_2995_;
v___y_2959_ = v___y_2989_;
v___y_2960_ = v___x_3004_;
v___y_2961_ = v___x_2996_;
v_only_2962_ = v___x_3011_;
v___y_2963_ = v___y_2986_;
v___y_2964_ = v___y_2988_;
v___y_2965_ = v___y_2990_;
v___y_2966_ = v___y_2985_;
v___y_2967_ = v___y_2993_;
v___y_2968_ = v___y_2987_;
v___y_2969_ = v___y_2984_;
v___y_2970_ = v___y_2991_;
goto v___jp_2949_;
}
}
}
}
v___jp_3012_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_unsigned_to_nat(2u);
v___x_3023_ = l_Lean_Syntax_getArg(v_stx_2835_, v___x_3022_);
v___x_3024_ = l_Lean_Syntax_isNone(v___x_3023_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
lean_inc(v___x_3023_);
v___x_3025_ = l_Lean_Syntax_matchesNull(v___x_3023_, v___x_2855_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_dec(v___x_3023_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v_squeeze_3013_);
lean_dec(v_tk_2854_);
lean_dec(v_stx_2835_);
v___x_3026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3026_;
}
else
{
lean_object* v_unfold_3027_; lean_object* v___x_3028_; 
v_unfold_3027_ = l_Lean_Syntax_getArg(v___x_3023_, v___x_2853_);
lean_dec(v___x_3023_);
v___x_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3028_, 0, v_unfold_3027_);
v___y_2984_ = v___y_3020_;
v___y_2985_ = v___y_3017_;
v___y_2986_ = v___y_3014_;
v___y_2987_ = v___y_3019_;
v___y_2988_ = v___y_3015_;
v___y_2989_ = v___x_3022_;
v___y_2990_ = v___y_3016_;
v___y_2991_ = v___y_3021_;
v___y_2992_ = v_squeeze_3013_;
v___y_2993_ = v___y_3018_;
v_unfold_2994_ = v___x_3028_;
goto v___jp_2983_;
}
}
else
{
lean_object* v___x_3029_; 
lean_dec(v___x_3023_);
v___x_3029_ = lean_box(0);
v___y_2984_ = v___y_3020_;
v___y_2985_ = v___y_3017_;
v___y_2986_ = v___y_3014_;
v___y_2987_ = v___y_3019_;
v___y_2988_ = v___y_3015_;
v___y_2989_ = v___x_3022_;
v___y_2990_ = v___y_3016_;
v___y_2991_ = v___y_3021_;
v___y_2992_ = v_squeeze_3013_;
v___y_2993_ = v___y_3018_;
v_unfold_2994_ = v___x_3029_;
goto v___jp_2983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_stx_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_stx_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(lean_object* v_mvarId_3048_, lean_object* v_val_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_3048_, v_val_3049_, v___y_3055_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___boxed(lean_object* v_mvarId_3060_, lean_object* v_val_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(v_mvarId_3060_, v_val_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(lean_object* v_o_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_o_3072_, v___y_3080_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___boxed(lean_object* v_o_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(v_o_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(lean_object* v_00_u03b1_3094_, lean_object* v_msg_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v_msg_3095_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___boxed(lean_object* v_00_u03b1_3106_, lean_object* v_msg_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(v_00_u03b1_3106_, v_msg_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(lean_object* v_00_u03b1_3118_, lean_object* v_x_3119_, lean_object* v_mkInfoTree_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v_x_3119_, v_mkInfoTree_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___boxed(lean_object* v_00_u03b1_3131_, lean_object* v_x_3132_, lean_object* v_mkInfoTree_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(v_00_u03b1_3131_, v_x_3132_, v_mkInfoTree_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3(lean_object* v_00_u03b2_3144_, lean_object* v_x_3145_, lean_object* v_x_3146_, lean_object* v_x_3147_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_x_3145_, v_x_3146_, v_x_3147_);
return v___x_3148_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3149_, lean_object* v_m_3150_, lean_object* v_a_3151_){
_start:
{
uint8_t v___x_3152_; 
v___x_3152_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_m_3150_, v_a_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3153_, lean_object* v_m_3154_, lean_object* v_a_3155_){
_start:
{
uint8_t v_res_3156_; lean_object* v_r_3157_; 
v_res_3156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(v_00_u03b2_3153_, v_m_3154_, v_a_3155_);
lean_dec_ref(v_a_3155_);
lean_dec_ref(v_m_3154_);
v_r_3157_ = lean_box(v_res_3156_);
return v_r_3157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3158_, lean_object* v_m_3159_, lean_object* v_a_3160_, lean_object* v_b_3161_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(v_m_3159_, v_a_3160_, v_b_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3163_, v___y_3164_, v___y_3170_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(v_mvarId_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v_mvarId_3175_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3187_, v___y_3188_, v___y_3194_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(v_mvarId_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v_mvarId_3199_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3211_, lean_object* v_x_3212_, size_t v_x_3213_, size_t v_x_3214_, lean_object* v_x_3215_, lean_object* v_x_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_3212_, v_x_3213_, v_x_3214_, v_x_3215_, v_x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
size_t v_x_85056__boxed_3224_; size_t v_x_85057__boxed_3225_; lean_object* v_res_3226_; 
v_x_85056__boxed_3224_ = lean_unbox_usize(v_x_3220_);
lean_dec(v_x_3220_);
v_x_85057__boxed_3225_ = lean_unbox_usize(v_x_3221_);
lean_dec(v_x_3221_);
v_res_3226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(v_00_u03b2_3218_, v_x_3219_, v_x_85056__boxed_3224_, v_x_85057__boxed_3225_, v_x_3222_, v_x_3223_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(lean_object* v_ref_3227_, lean_object* v_msgData_3228_, uint8_t v_severity_3229_, uint8_t v_isSilent_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_3227_, v_msgData_3228_, v_severity_3229_, v_isSilent_3230_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3241_, lean_object* v_msgData_3242_, lean_object* v_severity_3243_, lean_object* v_isSilent_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
uint8_t v_severity_boxed_3254_; uint8_t v_isSilent_boxed_3255_; lean_object* v_res_3256_; 
v_severity_boxed_3254_ = lean_unbox(v_severity_3243_);
v_isSilent_boxed_3255_ = lean_unbox(v_isSilent_3244_);
v_res_3256_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(v_ref_3241_, v_msgData_3242_, v_severity_boxed_3254_, v_isSilent_boxed_3255_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v_ref_3241_);
return v_res_3256_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3257_, lean_object* v_a_3258_, lean_object* v_x_3259_){
_start:
{
uint8_t v___x_3260_; 
v___x_3260_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3258_, v_x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3261_, lean_object* v_a_3262_, lean_object* v_x_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3261_, v_a_3262_, v_x_3263_);
lean_dec(v_x_3263_);
lean_dec_ref(v_a_3262_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3266_, lean_object* v_data_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3269_, lean_object* v_n_3270_, lean_object* v_k_3271_, lean_object* v_v_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3270_, v_k_3271_, v_v_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3274_, size_t v_depth_3275_, lean_object* v_keys_3276_, lean_object* v_vals_3277_, lean_object* v_heq_3278_, lean_object* v_i_3279_, lean_object* v_entries_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3275_, v_keys_3276_, v_vals_3277_, v_i_3279_, v_entries_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3282_, lean_object* v_depth_3283_, lean_object* v_keys_3284_, lean_object* v_vals_3285_, lean_object* v_heq_3286_, lean_object* v_i_3287_, lean_object* v_entries_3288_){
_start:
{
size_t v_depth_boxed_3289_; lean_object* v_res_3290_; 
v_depth_boxed_3289_ = lean_unbox_usize(v_depth_3283_);
lean_dec(v_depth_3283_);
v_res_3290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3282_, v_depth_boxed_3289_, v_keys_3284_, v_vals_3285_, v_heq_3286_, v_i_3287_, v_entries_3288_);
lean_dec_ref(v_vals_3285_);
lean_dec_ref(v_keys_3284_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3291_, lean_object* v_i_3292_, lean_object* v_source_3293_, lean_object* v_target_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3292_, v_source_3293_, v_target_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3297_, v_x_3298_, v_x_3299_, v_x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3303_, v_x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3315_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3316_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
v___x_3317_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3318_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3319_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3315_, v___x_3316_, v___x_3317_, v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3349_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3350_ = l_Lean_addBuiltinDeclarationRanges(v___x_3348_, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3352_;
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
