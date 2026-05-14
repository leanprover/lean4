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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
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
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unnecessarySimpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(182, 23, 154, 96, 189, 166, 9, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "enable the 'unnecessary simpa' linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalSimpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 230, 37, 137, 25, 71, 189, 138)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 111, 162, 89, 60, 103, 42, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(90) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_47_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_48_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v___x_46_, v___x_47_, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
return v_res_50_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object* v_o_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = l_linter_unnecessarySimpa;
v___x_53_ = l_Lean_Linter_getLinterValue(v___x_52_, v_o_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object* v_o_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_o_54_);
lean_dec_ref(v_o_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___closed__0);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg___boxed(lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object* v_00_u03b1_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___boxed(lean_object* v_00_u03b1_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(v_00_u03b1_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0(lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; 
lean_inc(v___y_91_);
lean_inc_ref(v___y_90_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
v___x_97_ = lean_apply_9(v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, lean_box(0));
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0___boxed(lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0(v_x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(lean_object* v_mvarId_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; 
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_120_, 0, v_x_110_);
lean_closure_set(v___f_120_, 1, v___y_111_);
lean_closure_set(v___f_120_, 2, v___y_112_);
lean_closure_set(v___f_120_, 3, v___y_113_);
lean_closure_set(v___f_120_, 4, v___y_114_);
v___x_121_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_109_, v___f_120_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
if (lean_obj_tag(v___x_121_) == 0)
{
return v___x_121_;
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg___boxed(lean_object* v_mvarId_130_, lean_object* v_x_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_mvarId_130_, v_x_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(lean_object* v_00_u03b1_142_, lean_object* v_mvarId_143_, lean_object* v_x_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_mvarId_143_, v_x_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___boxed(lean_object* v_00_u03b1_155_, lean_object* v_mvarId_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(v_00_u03b1_155_, v_mvarId_156_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_167_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_unsigned_to_nat(32u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_unsigned_to_nat(32u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__0);
v___x_176_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_172_);
lean_ctor_set(v___x_176_, 3, v___x_172_);
lean_ctor_set_usize(v___x_176_, 4, v___x_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_infoState_180_; lean_object* v_trees_181_; lean_object* v___x_182_; lean_object* v_infoState_183_; lean_object* v_env_184_; lean_object* v_nextMacroScope_185_; lean_object* v_ngen_186_; lean_object* v_auxDeclNGen_187_; lean_object* v_traceState_188_; lean_object* v_cache_189_; lean_object* v_messages_190_; lean_object* v_snapshotTasks_191_; lean_object* v_newDecls_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_213_; 
v___x_179_ = lean_st_ref_get(v___y_177_);
v_infoState_180_ = lean_ctor_get(v___x_179_, 7);
lean_inc_ref(v_infoState_180_);
lean_dec(v___x_179_);
v_trees_181_ = lean_ctor_get(v_infoState_180_, 2);
lean_inc_ref(v_trees_181_);
lean_dec_ref(v_infoState_180_);
v___x_182_ = lean_st_ref_take(v___y_177_);
v_infoState_183_ = lean_ctor_get(v___x_182_, 7);
v_env_184_ = lean_ctor_get(v___x_182_, 0);
v_nextMacroScope_185_ = lean_ctor_get(v___x_182_, 1);
v_ngen_186_ = lean_ctor_get(v___x_182_, 2);
v_auxDeclNGen_187_ = lean_ctor_get(v___x_182_, 3);
v_traceState_188_ = lean_ctor_get(v___x_182_, 4);
v_cache_189_ = lean_ctor_get(v___x_182_, 5);
v_messages_190_ = lean_ctor_get(v___x_182_, 6);
v_snapshotTasks_191_ = lean_ctor_get(v___x_182_, 8);
v_newDecls_192_ = lean_ctor_get(v___x_182_, 9);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_213_ == 0)
{
v___x_194_ = v___x_182_;
v_isShared_195_ = v_isSharedCheck_213_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_newDecls_192_);
lean_inc(v_snapshotTasks_191_);
lean_inc(v_infoState_183_);
lean_inc(v_messages_190_);
lean_inc(v_cache_189_);
lean_inc(v_traceState_188_);
lean_inc(v_auxDeclNGen_187_);
lean_inc(v_ngen_186_);
lean_inc(v_nextMacroScope_185_);
lean_inc(v_env_184_);
lean_dec(v___x_182_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_213_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
uint8_t v_enabled_196_; lean_object* v_assignment_197_; lean_object* v_lazyAssignment_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_211_; 
v_enabled_196_ = lean_ctor_get_uint8(v_infoState_183_, sizeof(void*)*3);
v_assignment_197_ = lean_ctor_get(v_infoState_183_, 0);
v_lazyAssignment_198_ = lean_ctor_get(v_infoState_183_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_infoState_183_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_infoState_183_, 2);
lean_dec(v_unused_212_);
v___x_200_ = v_infoState_183_;
v_isShared_201_ = v_isSharedCheck_211_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_lazyAssignment_198_);
lean_inc(v_assignment_197_);
lean_dec(v_infoState_183_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_211_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 2, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_assignment_197_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_lazyAssignment_198_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___x_202_);
lean_ctor_set_uint8(v_reuseFailAlloc_210_, sizeof(void*)*3, v_enabled_196_);
v___x_204_ = v_reuseFailAlloc_210_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_206_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 7, v___x_204_);
v___x_206_ = v___x_194_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_env_184_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_nextMacroScope_185_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_ngen_186_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_auxDeclNGen_187_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_traceState_188_);
lean_ctor_set(v_reuseFailAlloc_209_, 5, v_cache_189_);
lean_ctor_set(v_reuseFailAlloc_209_, 6, v_messages_190_);
lean_ctor_set(v_reuseFailAlloc_209_, 7, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_209_, 8, v_snapshotTasks_191_);
lean_ctor_set(v_reuseFailAlloc_209_, 9, v_newDecls_192_);
v___x_206_ = v_reuseFailAlloc_209_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_st_ref_set(v___y_177_, v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_trees_181_);
return v___x_208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___boxed(lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_214_);
lean_dec(v___y_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7(lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___boxed(lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7(v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___f_248_; lean_object* v___x_66584__overap_249_; lean_object* v___x_250_; 
v___f_248_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___closed__0));
v___x_66584__overap_249_ = lean_panic_fn_borrowed(v___f_248_, v_msg_238_);
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
lean_inc(v___y_244_);
lean_inc_ref(v___y_243_);
lean_inc(v___y_242_);
lean_inc_ref(v___y_241_);
lean_inc(v___y_240_);
lean_inc_ref(v___y_239_);
v___x_250_ = lean_apply_9(v___x_66584__overap_249_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, lean_box(0));
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___boxed(lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v_msg_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(lean_object* v_opts_262_, lean_object* v_opt_263_){
_start:
{
lean_object* v_name_264_; lean_object* v_defValue_265_; lean_object* v_map_266_; lean_object* v___x_267_; 
v_name_264_ = lean_ctor_get(v_opt_263_, 0);
v_defValue_265_ = lean_ctor_get(v_opt_263_, 1);
v_map_266_ = lean_ctor_get(v_opts_262_, 0);
v___x_267_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_266_, v_name_264_);
if (lean_obj_tag(v___x_267_) == 0)
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_defValue_265_);
return v___x_268_;
}
else
{
lean_object* v_val_269_; 
v_val_269_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_val_269_);
lean_dec_ref(v___x_267_);
if (lean_obj_tag(v_val_269_) == 1)
{
uint8_t v_v_270_; 
v_v_270_ = lean_ctor_get_uint8(v_val_269_, 0);
lean_dec_ref(v_val_269_);
return v_v_270_;
}
else
{
uint8_t v___x_271_; 
lean_dec(v_val_269_);
v___x_271_ = lean_unbox(v_defValue_265_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10___boxed(lean_object* v_opts_272_, lean_object* v_opt_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_opts_272_, v_opt_273_);
lean_dec_ref(v_opt_273_);
lean_dec_ref(v_opts_272_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_ref_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_ref_285_ = lean_ctor_get(v___y_282_, 5);
v___x_286_ = 0;
v___x_287_ = l_Lean_SourceInfo_fromRef(v_ref_285_, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object* v_a_299_, lean_object* v_trees_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
v___x_310_ = lean_apply_9(v_a_299_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, lean_box(0));
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v_a_311_);
lean_ctor_set(v___x_315_, 1, v_trees_300_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_trees_300_);
v_a_320_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_310_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_310_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object* v_a_328_, lean_object* v_trees_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(v_a_328_, v_trees_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object* v_a_346_, lean_object* v_a_347_, uint8_t v___x_348_, uint8_t v___x_349_, uint8_t v___x_350_, lean_object* v_a_351_, lean_object* v_mvarCounter_352_, lean_object* v___x_353_, lean_object* v___x_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
lean_inc(v_a_346_);
v___x_364_ = l_Lean_MVarId_getType(v_a_346_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_n(v_a_365_, 2);
lean_dec_ref(v___x_364_);
v___x_366_ = lean_mk_syntax_ident(v_a_347_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v_a_365_);
v___x_368_ = l_Lean_Elab_Term_elabTerm(v___x_366_, v___x_367_, v___x_348_, v___x_348_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___x_403_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref(v___x_368_);
v___x_403_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_349_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_480_; 
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_481_);
v___x_405_ = v___x_403_;
v_isShared_406_ = v_isSharedCheck_480_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_403_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_480_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; 
lean_inc(v___y_362_);
lean_inc_ref(v___y_361_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v_a_369_);
v___x_407_ = lean_infer_type(v_a_369_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; uint8_t v_a_410_; lean_object* v___x_420_; uint8_t v_foApprox_421_; uint8_t v_ctxApprox_422_; uint8_t v_quasiPatternApprox_423_; uint8_t v_constApprox_424_; uint8_t v_isDefEqStuckEx_425_; uint8_t v_unificationHints_426_; uint8_t v_proofIrrelevance_427_; uint8_t v_offsetCnstrs_428_; uint8_t v_transparency_429_; uint8_t v_etaStruct_430_; uint8_t v_univApprox_431_; uint8_t v_iota_432_; uint8_t v_beta_433_; uint8_t v_proj_434_; uint8_t v_zeta_435_; uint8_t v_zetaDelta_436_; uint8_t v_zetaUnused_437_; uint8_t v_zetaHave_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_471_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v___x_407_);
v___x_420_ = l_Lean_Meta_Context_config(v___y_359_);
v_foApprox_421_ = lean_ctor_get_uint8(v___x_420_, 0);
v_ctxApprox_422_ = lean_ctor_get_uint8(v___x_420_, 1);
v_quasiPatternApprox_423_ = lean_ctor_get_uint8(v___x_420_, 2);
v_constApprox_424_ = lean_ctor_get_uint8(v___x_420_, 3);
v_isDefEqStuckEx_425_ = lean_ctor_get_uint8(v___x_420_, 4);
v_unificationHints_426_ = lean_ctor_get_uint8(v___x_420_, 5);
v_proofIrrelevance_427_ = lean_ctor_get_uint8(v___x_420_, 6);
v_offsetCnstrs_428_ = lean_ctor_get_uint8(v___x_420_, 8);
v_transparency_429_ = lean_ctor_get_uint8(v___x_420_, 9);
v_etaStruct_430_ = lean_ctor_get_uint8(v___x_420_, 10);
v_univApprox_431_ = lean_ctor_get_uint8(v___x_420_, 11);
v_iota_432_ = lean_ctor_get_uint8(v___x_420_, 12);
v_beta_433_ = lean_ctor_get_uint8(v___x_420_, 13);
v_proj_434_ = lean_ctor_get_uint8(v___x_420_, 14);
v_zeta_435_ = lean_ctor_get_uint8(v___x_420_, 15);
v_zetaDelta_436_ = lean_ctor_get_uint8(v___x_420_, 16);
v_zetaUnused_437_ = lean_ctor_get_uint8(v___x_420_, 17);
v_zetaHave_438_ = lean_ctor_get_uint8(v___x_420_, 18);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_471_ == 0)
{
v___x_440_ = v___x_420_;
v_isShared_441_ = v_isSharedCheck_471_;
goto v_resetjp_439_;
}
else
{
lean_dec(v___x_420_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_471_;
goto v_resetjp_439_;
}
v___jp_409_:
{
if (v_a_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_411_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1);
lean_inc_ref(v_a_351_);
v___x_412_ = l_Lean_indentExpr(v_a_351_);
v___x_413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_415_);
v___x_417_ = v___x_405_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_419_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; 
lean_inc(v_a_369_);
v___x_418_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_417_, v_a_365_, v_a_408_, v_a_369_, v___x_354_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec_ref(v___x_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_dec_ref(v___x_418_);
v___y_371_ = v___y_355_;
v___y_372_ = v___y_356_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
v___y_378_ = v___y_362_;
goto v___jp_370_;
}
else
{
lean_dec(v_a_369_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_346_);
return v___x_418_;
}
}
}
else
{
lean_dec(v_a_408_);
lean_del_object(v___x_405_);
lean_dec(v_a_365_);
lean_dec(v___x_354_);
v___y_371_ = v___y_355_;
v___y_372_ = v___y_356_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
v___y_378_ = v___y_362_;
goto v___jp_370_;
}
}
v_resetjp_439_:
{
uint8_t v_trackZetaDelta_442_; lean_object* v_zetaDeltaSet_443_; lean_object* v_lctx_444_; lean_object* v_localInstances_445_; lean_object* v_defEqCtx_x3f_446_; lean_object* v_synthPendingDepth_447_; lean_object* v_canUnfold_x3f_448_; uint8_t v_univApprox_449_; uint8_t v_inTypeClassResolution_450_; uint8_t v_cacheInferType_451_; lean_object* v___x_453_; 
v_trackZetaDelta_442_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*7);
v_zetaDeltaSet_443_ = lean_ctor_get(v___y_359_, 1);
v_lctx_444_ = lean_ctor_get(v___y_359_, 2);
v_localInstances_445_ = lean_ctor_get(v___y_359_, 3);
v_defEqCtx_x3f_446_ = lean_ctor_get(v___y_359_, 4);
v_synthPendingDepth_447_ = lean_ctor_get(v___y_359_, 5);
v_canUnfold_x3f_448_ = lean_ctor_get(v___y_359_, 6);
v_univApprox_449_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_450_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*7 + 2);
v_cacheInferType_451_ = lean_ctor_get_uint8(v___y_359_, sizeof(void*)*7 + 3);
if (v_isShared_441_ == 0)
{
v___x_453_ = v___x_440_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 0, v_foApprox_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 1, v_ctxApprox_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 2, v_quasiPatternApprox_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 3, v_constApprox_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 4, v_isDefEqStuckEx_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 5, v_unificationHints_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 6, v_proofIrrelevance_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 8, v_offsetCnstrs_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 9, v_transparency_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 10, v_etaStruct_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 11, v_univApprox_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 12, v_iota_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 13, v_beta_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 14, v_proj_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 15, v_zeta_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 16, v_zetaDelta_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 17, v_zetaUnused_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_470_, 18, v_zetaHave_438_);
v___x_453_ = v_reuseFailAlloc_470_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
uint64_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_ctor_set_uint8(v___x_453_, 7, v___x_350_);
v___x_454_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set_uint64(v___x_455_, sizeof(void*)*1, v___x_454_);
lean_inc(v_canUnfold_x3f_448_);
lean_inc(v_synthPendingDepth_447_);
lean_inc(v_defEqCtx_x3f_446_);
lean_inc_ref(v_localInstances_445_);
lean_inc_ref(v_lctx_444_);
lean_inc(v_zetaDeltaSet_443_);
v___x_456_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v_zetaDeltaSet_443_);
lean_ctor_set(v___x_456_, 2, v_lctx_444_);
lean_ctor_set(v___x_456_, 3, v_localInstances_445_);
lean_ctor_set(v___x_456_, 4, v_defEqCtx_x3f_446_);
lean_ctor_set(v___x_456_, 5, v_synthPendingDepth_447_);
lean_ctor_set(v___x_456_, 6, v_canUnfold_x3f_448_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*7, v_trackZetaDelta_442_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*7 + 1, v_univApprox_449_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*7 + 2, v_inTypeClassResolution_450_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*7 + 3, v_cacheInferType_451_);
lean_inc(v_a_408_);
lean_inc(v_a_365_);
v___x_457_ = l_Lean_Meta_isExprDefEq(v_a_365_, v_a_408_, v___x_456_, v___y_360_, v___y_361_, v___y_362_);
lean_dec_ref(v___x_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; uint8_t v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
v_a_410_ = v___x_459_;
goto v___jp_409_;
}
else
{
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_460_; uint8_t v___x_461_; 
v_a_460_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v___x_457_);
v___x_461_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
v_a_410_ = v___x_461_;
goto v___jp_409_;
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_a_408_);
lean_del_object(v___x_405_);
lean_dec(v_a_369_);
lean_dec(v_a_365_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_346_);
v_a_462_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_457_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_457_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_405_);
lean_dec(v_a_369_);
lean_dec(v_a_365_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_346_);
v_a_472_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_407_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_407_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
else
{
lean_dec(v_a_369_);
lean_dec(v_a_365_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_346_);
return v___x_403_;
}
v___jp_370_:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_getMVars(v_a_351_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref(v___x_379_);
v___x_381_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_380_, v_mvarCounter_352_, v___y_376_);
lean_dec(v_a_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref(v___x_381_);
v___x_383_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_382_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v_a_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_384_; 
lean_dec_ref(v___x_383_);
v___x_384_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_346_, v___y_372_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec_ref(v___x_384_);
v___x_385_ = l_Lean_Name_mkStr1(v___x_353_);
v___x_386_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_385_, v_a_369_, v___x_349_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v___x_386_;
}
else
{
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v_a_369_);
lean_dec_ref(v___x_353_);
return v___x_384_;
}
}
else
{
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v_a_369_);
lean_dec_ref(v___x_353_);
lean_dec(v_a_346_);
return v___x_383_;
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v_a_369_);
lean_dec_ref(v___x_353_);
lean_dec(v_a_346_);
v_a_387_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_381_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_381_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v_a_369_);
lean_dec_ref(v___x_353_);
lean_dec(v_a_346_);
v_a_395_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_379_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_379_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_a_365_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_346_);
v_a_482_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_368_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_368_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
lean_dec(v_a_346_);
v_a_490_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_364_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_364_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object** _args){
lean_object* v_a_498_ = _args[0];
lean_object* v_a_499_ = _args[1];
lean_object* v___x_500_ = _args[2];
lean_object* v___x_501_ = _args[3];
lean_object* v___x_502_ = _args[4];
lean_object* v_a_503_ = _args[5];
lean_object* v_mvarCounter_504_ = _args[6];
lean_object* v___x_505_ = _args[7];
lean_object* v___x_506_ = _args[8];
lean_object* v___y_507_ = _args[9];
lean_object* v___y_508_ = _args[10];
lean_object* v___y_509_ = _args[11];
lean_object* v___y_510_ = _args[12];
lean_object* v___y_511_ = _args[13];
lean_object* v___y_512_ = _args[14];
lean_object* v___y_513_ = _args[15];
lean_object* v___y_514_ = _args[16];
lean_object* v___y_515_ = _args[17];
_start:
{
uint8_t v___x_78909__boxed_516_; uint8_t v___x_78910__boxed_517_; uint8_t v___x_78911__boxed_518_; lean_object* v_res_519_; 
v___x_78909__boxed_516_ = lean_unbox(v___x_500_);
v___x_78910__boxed_517_ = lean_unbox(v___x_501_);
v___x_78911__boxed_518_ = lean_unbox(v___x_502_);
v_res_519_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(v_a_498_, v_a_499_, v___x_78909__boxed_516_, v___x_78910__boxed_517_, v___x_78911__boxed_518_, v_a_503_, v_mvarCounter_504_, v___x_505_, v___x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v_mvarCounter_504_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object* v_a_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; lean_object* v_infoState_531_; lean_object* v_env_532_; lean_object* v_nextMacroScope_533_; lean_object* v_ngen_534_; lean_object* v_auxDeclNGen_535_; lean_object* v_traceState_536_; lean_object* v_cache_537_; lean_object* v_messages_538_; lean_object* v_snapshotTasks_539_; lean_object* v_newDecls_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_561_; 
v___x_530_ = lean_st_ref_take(v___y_528_);
v_infoState_531_ = lean_ctor_get(v___x_530_, 7);
v_env_532_ = lean_ctor_get(v___x_530_, 0);
v_nextMacroScope_533_ = lean_ctor_get(v___x_530_, 1);
v_ngen_534_ = lean_ctor_get(v___x_530_, 2);
v_auxDeclNGen_535_ = lean_ctor_get(v___x_530_, 3);
v_traceState_536_ = lean_ctor_get(v___x_530_, 4);
v_cache_537_ = lean_ctor_get(v___x_530_, 5);
v_messages_538_ = lean_ctor_get(v___x_530_, 6);
v_snapshotTasks_539_ = lean_ctor_get(v___x_530_, 8);
v_newDecls_540_ = lean_ctor_get(v___x_530_, 9);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_561_ == 0)
{
v___x_542_ = v___x_530_;
v_isShared_543_ = v_isSharedCheck_561_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_newDecls_540_);
lean_inc(v_snapshotTasks_539_);
lean_inc(v_infoState_531_);
lean_inc(v_messages_538_);
lean_inc(v_cache_537_);
lean_inc(v_traceState_536_);
lean_inc(v_auxDeclNGen_535_);
lean_inc(v_ngen_534_);
lean_inc(v_nextMacroScope_533_);
lean_inc(v_env_532_);
lean_dec(v___x_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_561_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
uint8_t v_enabled_544_; lean_object* v_assignment_545_; lean_object* v_lazyAssignment_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_559_; 
v_enabled_544_ = lean_ctor_get_uint8(v_infoState_531_, sizeof(void*)*3);
v_assignment_545_ = lean_ctor_get(v_infoState_531_, 0);
v_lazyAssignment_546_ = lean_ctor_get(v_infoState_531_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_infoState_531_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_infoState_531_, 2);
lean_dec(v_unused_560_);
v___x_548_ = v_infoState_531_;
v_isShared_549_ = v_isSharedCheck_559_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_lazyAssignment_546_);
lean_inc(v_assignment_545_);
lean_dec(v_infoState_531_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_559_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v_a_520_);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_assignment_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_lazyAssignment_546_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_a_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_558_, sizeof(void*)*3, v_enabled_544_);
v___x_551_ = v_reuseFailAlloc_558_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 7, v___x_551_);
v___x_553_ = v___x_542_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_env_532_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_nextMacroScope_533_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_ngen_534_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_auxDeclNGen_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_traceState_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v_cache_537_);
lean_ctor_set(v_reuseFailAlloc_557_, 6, v_messages_538_);
lean_ctor_set(v_reuseFailAlloc_557_, 7, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_557_, 8, v_snapshotTasks_539_);
lean_ctor_set(v_reuseFailAlloc_557_, 9, v_newDecls_540_);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_st_ref_set(v___y_528_, v___x_553_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object* v_a_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(v_a_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(lean_object* v_msgData_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v_env_580_; lean_object* v___x_581_; lean_object* v_mctx_582_; lean_object* v_lctx_583_; lean_object* v_options_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_579_ = lean_st_ref_get(v___y_577_);
v_env_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_env_580_);
lean_dec(v___x_579_);
v___x_581_ = lean_st_ref_get(v___y_575_);
v_mctx_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_mctx_582_);
lean_dec(v___x_581_);
v_lctx_583_ = lean_ctor_get(v___y_574_, 2);
v_options_584_ = lean_ctor_get(v___y_576_, 2);
lean_inc_ref(v_options_584_);
lean_inc_ref(v_lctx_583_);
v___x_585_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_585_, 0, v_env_580_);
lean_ctor_set(v___x_585_, 1, v_mctx_582_);
lean_ctor_set(v___x_585_, 2, v_lctx_583_);
lean_ctor_set(v___x_585_, 3, v_options_584_);
v___x_586_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_msgData_573_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10___boxed(lean_object* v_msgData_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v_msgData_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_ref_601_; lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
v_ref_601_ = lean_ctor_get(v___y_598_, 5);
v___x_602_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_611_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
lean_inc(v_ref_601_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v_ref_601_);
lean_ctor_set(v___x_607_, 1, v_a_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 1);
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg___boxed(lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v_msg_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(lean_object* v_mvarId_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; lean_object* v_mctx_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_623_ = lean_st_ref_get(v___y_621_);
v_mctx_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_ref(v_mctx_624_);
lean_dec(v___x_623_);
v___x_625_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_624_, v_mvarId_619_);
lean_dec_ref(v_mctx_624_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___y_620_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object* v_mvarId_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec(v_mvarId_629_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_mvarId_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; lean_object* v_mctx_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = lean_st_ref_get(v___y_636_);
v_mctx_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc_ref(v_mctx_639_);
lean_dec(v___x_638_);
v___x_640_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_639_, v_mvarId_634_);
lean_dec_ref(v_mctx_639_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___y_635_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_mvarId_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec(v_mvarId_644_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
return v_x_649_;
}
else
{
lean_object* v_key_651_; lean_object* v_value_652_; lean_object* v_tail_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_676_; 
v_key_651_ = lean_ctor_get(v_x_650_, 0);
v_value_652_ = lean_ctor_get(v_x_650_, 1);
v_tail_653_ = lean_ctor_get(v_x_650_, 2);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_676_ == 0)
{
v___x_655_ = v_x_650_;
v_isShared_656_ = v_isSharedCheck_676_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_tail_653_);
lean_inc(v_value_652_);
lean_inc(v_key_651_);
lean_dec(v_x_650_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_676_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v_fold_661_; uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_657_ = lean_array_get_size(v_x_649_);
v___x_658_ = l_Lean_Expr_hash(v_key_651_);
v___x_659_ = 32ULL;
v___x_660_ = lean_uint64_shift_right(v___x_658_, v___x_659_);
v_fold_661_ = lean_uint64_xor(v___x_658_, v___x_660_);
v___x_662_ = 16ULL;
v___x_663_ = lean_uint64_shift_right(v_fold_661_, v___x_662_);
v___x_664_ = lean_uint64_xor(v_fold_661_, v___x_663_);
v___x_665_ = lean_uint64_to_usize(v___x_664_);
v___x_666_ = lean_usize_of_nat(v___x_657_);
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_sub(v___x_666_, v___x_667_);
v___x_669_ = lean_usize_land(v___x_665_, v___x_668_);
v___x_670_ = lean_array_uget_borrowed(v_x_649_, v___x_669_);
lean_inc(v___x_670_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 2, v___x_670_);
v___x_672_ = v___x_655_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_key_651_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_value_652_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v___x_670_);
v___x_672_ = v_reuseFailAlloc_675_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; 
v___x_673_ = lean_array_uset(v_x_649_, v___x_669_, v___x_672_);
v_x_649_ = v___x_673_;
v_x_650_ = v_tail_653_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object* v_i_677_, lean_object* v_source_678_, lean_object* v_target_679_){
_start:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = lean_array_get_size(v_source_678_);
v___x_681_ = lean_nat_dec_lt(v_i_677_, v___x_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v_source_678_);
lean_dec(v_i_677_);
return v_target_679_;
}
else
{
lean_object* v_es_682_; lean_object* v___x_683_; lean_object* v_source_684_; lean_object* v_target_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_es_682_ = lean_array_fget(v_source_678_, v_i_677_);
v___x_683_ = lean_box(0);
v_source_684_ = lean_array_fset(v_source_678_, v_i_677_, v___x_683_);
v_target_685_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_679_, v_es_682_);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_add(v_i_677_, v___x_686_);
lean_dec(v_i_677_);
v_i_677_ = v___x_687_;
v_source_678_ = v_source_684_;
v_target_679_ = v_target_685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_data_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_nbuckets_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_690_ = lean_array_get_size(v_data_689_);
v___x_691_ = lean_unsigned_to_nat(2u);
v_nbuckets_692_ = lean_nat_mul(v___x_690_, v___x_691_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_box(0);
v___x_695_ = lean_mk_array(v_nbuckets_692_, v___x_694_);
v___x_696_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_693_, v_data_689_, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_a_697_, lean_object* v_x_698_){
_start:
{
if (lean_obj_tag(v_x_698_) == 0)
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
else
{
lean_object* v_key_700_; lean_object* v_tail_701_; uint8_t v___x_702_; 
v_key_700_ = lean_ctor_get(v_x_698_, 0);
v_tail_701_ = lean_ctor_get(v_x_698_, 2);
v___x_702_ = lean_expr_eqv(v_key_700_, v_a_697_);
if (v___x_702_ == 0)
{
v_x_698_ = v_tail_701_;
goto _start;
}
else
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_a_704_, lean_object* v_x_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_704_, v_x_705_);
lean_dec(v_x_705_);
lean_dec_ref(v_a_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(lean_object* v_m_708_, lean_object* v_a_709_, lean_object* v_b_710_){
_start:
{
lean_object* v_size_711_; lean_object* v_buckets_712_; lean_object* v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v_fold_717_; uint64_t v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; size_t v___x_721_; size_t v___x_722_; size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v_bkt_726_; uint8_t v___x_727_; 
v_size_711_ = lean_ctor_get(v_m_708_, 0);
v_buckets_712_ = lean_ctor_get(v_m_708_, 1);
v___x_713_ = lean_array_get_size(v_buckets_712_);
v___x_714_ = l_Lean_Expr_hash(v_a_709_);
v___x_715_ = 32ULL;
v___x_716_ = lean_uint64_shift_right(v___x_714_, v___x_715_);
v_fold_717_ = lean_uint64_xor(v___x_714_, v___x_716_);
v___x_718_ = 16ULL;
v___x_719_ = lean_uint64_shift_right(v_fold_717_, v___x_718_);
v___x_720_ = lean_uint64_xor(v_fold_717_, v___x_719_);
v___x_721_ = lean_uint64_to_usize(v___x_720_);
v___x_722_ = lean_usize_of_nat(v___x_713_);
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_sub(v___x_722_, v___x_723_);
v___x_725_ = lean_usize_land(v___x_721_, v___x_724_);
v_bkt_726_ = lean_array_uget_borrowed(v_buckets_712_, v___x_725_);
v___x_727_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_709_, v_bkt_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_748_; 
lean_inc_ref(v_buckets_712_);
lean_inc(v_size_711_);
v_isSharedCheck_748_ = !lean_is_exclusive(v_m_708_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_749_ = lean_ctor_get(v_m_708_, 1);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_m_708_, 0);
lean_dec(v_unused_750_);
v___x_729_ = v_m_708_;
v_isShared_730_ = v_isSharedCheck_748_;
goto v_resetjp_728_;
}
else
{
lean_dec(v_m_708_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_748_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v_size_x27_732_; lean_object* v___x_733_; lean_object* v_buckets_x27_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_731_ = lean_unsigned_to_nat(1u);
v_size_x27_732_ = lean_nat_add(v_size_711_, v___x_731_);
lean_dec(v_size_711_);
lean_inc(v_bkt_726_);
v___x_733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_733_, 0, v_a_709_);
lean_ctor_set(v___x_733_, 1, v_b_710_);
lean_ctor_set(v___x_733_, 2, v_bkt_726_);
v_buckets_x27_734_ = lean_array_uset(v_buckets_712_, v___x_725_, v___x_733_);
v___x_735_ = lean_unsigned_to_nat(4u);
v___x_736_ = lean_nat_mul(v_size_x27_732_, v___x_735_);
v___x_737_ = lean_unsigned_to_nat(3u);
v___x_738_ = lean_nat_div(v___x_736_, v___x_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_array_get_size(v_buckets_x27_734_);
v___x_740_ = lean_nat_dec_le(v___x_738_, v___x_739_);
lean_dec(v___x_738_);
if (v___x_740_ == 0)
{
lean_object* v_val_741_; lean_object* v___x_743_; 
v_val_741_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_734_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_val_741_);
lean_ctor_set(v___x_729_, 0, v_size_x27_732_);
v___x_743_ = v___x_729_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_size_x27_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_val_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v___x_746_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_buckets_x27_734_);
lean_ctor_set(v___x_729_, 0, v_size_x27_732_);
v___x_746_ = v___x_729_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_size_x27_732_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_buckets_x27_734_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_dec(v_b_710_);
lean_dec_ref(v_a_709_);
return v_m_708_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(lean_object* v_m_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_buckets_753_; lean_object* v___x_754_; uint64_t v___x_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v_fold_758_; uint64_t v___x_759_; uint64_t v___x_760_; uint64_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_buckets_753_ = lean_ctor_get(v_m_751_, 1);
v___x_754_ = lean_array_get_size(v_buckets_753_);
v___x_755_ = l_Lean_Expr_hash(v_a_752_);
v___x_756_ = 32ULL;
v___x_757_ = lean_uint64_shift_right(v___x_755_, v___x_756_);
v_fold_758_ = lean_uint64_xor(v___x_755_, v___x_757_);
v___x_759_ = 16ULL;
v___x_760_ = lean_uint64_shift_right(v_fold_758_, v___x_759_);
v___x_761_ = lean_uint64_xor(v_fold_758_, v___x_760_);
v___x_762_ = lean_uint64_to_usize(v___x_761_);
v___x_763_ = lean_usize_of_nat(v___x_754_);
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_sub(v___x_763_, v___x_764_);
v___x_766_ = lean_usize_land(v___x_762_, v___x_765_);
v___x_767_ = lean_array_uget_borrowed(v_buckets_753_, v___x_766_);
v___x_768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_752_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_769_, lean_object* v_a_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_m_769_, v_a_770_);
lean_dec_ref(v_a_770_);
lean_dec_ref(v_m_769_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object* v_mvarId_777_, lean_object* v_e_778_, lean_object* v_a_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_d_790_; lean_object* v_b_791_; lean_object* v___y_792_; uint8_t v___x_798_; 
v___x_798_ = l_Lean_Expr_hasExprMVar(v_e_778_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v_e_778_);
v___x_799_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v_a_779_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_a_779_, v_e_778_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
lean_inc_ref(v_e_778_);
v___x_804_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(v_a_779_, v_e_778_, v___x_803_);
switch(lean_obj_tag(v_e_778_))
{
case 11:
{
lean_object* v_struct_805_; 
v_struct_805_ = lean_ctor_get(v_e_778_, 2);
lean_inc_ref(v_struct_805_);
lean_dec_ref(v_e_778_);
v_e_778_ = v_struct_805_;
v_a_779_ = v___x_804_;
goto _start;
}
case 7:
{
lean_object* v_binderType_807_; lean_object* v_body_808_; 
v_binderType_807_ = lean_ctor_get(v_e_778_, 1);
lean_inc_ref(v_binderType_807_);
v_body_808_ = lean_ctor_get(v_e_778_, 2);
lean_inc_ref(v_body_808_);
lean_dec_ref(v_e_778_);
v_d_790_ = v_binderType_807_;
v_b_791_ = v_body_808_;
v___y_792_ = v___x_804_;
goto v___jp_789_;
}
case 6:
{
lean_object* v_binderType_809_; lean_object* v_body_810_; 
v_binderType_809_ = lean_ctor_get(v_e_778_, 1);
lean_inc_ref(v_binderType_809_);
v_body_810_ = lean_ctor_get(v_e_778_, 2);
lean_inc_ref(v_body_810_);
lean_dec_ref(v_e_778_);
v_d_790_ = v_binderType_809_;
v_b_791_ = v_body_810_;
v___y_792_ = v___x_804_;
goto v___jp_789_;
}
case 8:
{
lean_object* v_type_811_; lean_object* v_value_812_; lean_object* v_body_813_; lean_object* v___x_814_; 
v_type_811_ = lean_ctor_get(v_e_778_, 1);
lean_inc_ref(v_type_811_);
v_value_812_ = lean_ctor_get(v_e_778_, 2);
lean_inc_ref(v_value_812_);
v_body_813_ = lean_ctor_get(v_e_778_, 3);
lean_inc_ref(v_body_813_);
lean_dec_ref(v_e_778_);
v___x_814_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_777_, v_type_811_, v___x_804_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v_fst_816_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
v_fst_816_ = lean_ctor_get(v_a_815_, 0);
if (lean_obj_tag(v_fst_816_) == 0)
{
lean_dec(v_a_815_);
lean_dec_ref(v_body_813_);
lean_dec_ref(v_value_812_);
return v___x_814_;
}
else
{
lean_object* v_snd_817_; lean_object* v___x_818_; 
lean_dec_ref(v___x_814_);
v_snd_817_ = lean_ctor_get(v_a_815_, 1);
lean_inc(v_snd_817_);
lean_dec(v_a_815_);
v___x_818_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_777_, v_value_812_, v_snd_817_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_fst_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
v_fst_820_ = lean_ctor_get(v_a_819_, 0);
if (lean_obj_tag(v_fst_820_) == 0)
{
lean_dec(v_a_819_);
lean_dec_ref(v_body_813_);
return v___x_818_;
}
else
{
lean_object* v_snd_821_; 
lean_dec_ref(v___x_818_);
v_snd_821_ = lean_ctor_get(v_a_819_, 1);
lean_inc(v_snd_821_);
lean_dec(v_a_819_);
v_e_778_ = v_body_813_;
v_a_779_ = v_snd_821_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_813_);
return v___x_818_;
}
}
}
else
{
lean_dec_ref(v_body_813_);
lean_dec_ref(v_value_812_);
return v___x_814_;
}
}
case 10:
{
lean_object* v_expr_823_; 
v_expr_823_ = lean_ctor_get(v_e_778_, 1);
lean_inc_ref(v_expr_823_);
lean_dec_ref(v_e_778_);
v_e_778_ = v_expr_823_;
v_a_779_ = v___x_804_;
goto _start;
}
case 5:
{
lean_object* v_fn_825_; lean_object* v_arg_826_; lean_object* v___x_827_; 
v_fn_825_ = lean_ctor_get(v_e_778_, 0);
lean_inc_ref(v_fn_825_);
v_arg_826_ = lean_ctor_get(v_e_778_, 1);
lean_inc_ref(v_arg_826_);
lean_dec_ref(v_e_778_);
v___x_827_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_777_, v_fn_825_, v___x_804_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v_fst_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
v_fst_829_ = lean_ctor_get(v_a_828_, 0);
if (lean_obj_tag(v_fst_829_) == 0)
{
lean_dec(v_a_828_);
lean_dec_ref(v_arg_826_);
return v___x_827_;
}
else
{
lean_object* v_snd_830_; 
lean_dec_ref(v___x_827_);
v_snd_830_ = lean_ctor_get(v_a_828_, 1);
lean_inc(v_snd_830_);
lean_dec(v_a_828_);
v_e_778_ = v_arg_826_;
v_a_779_ = v_snd_830_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_826_);
return v___x_827_;
}
}
case 2:
{
lean_object* v_mvarId_832_; lean_object* v___x_833_; 
v_mvarId_832_ = lean_ctor_get(v_e_778_, 0);
lean_inc(v_mvarId_832_);
lean_dec_ref(v_e_778_);
v___x_833_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(v_mvarId_777_, v_mvarId_832_, v___x_804_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_833_;
}
default: 
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v_e_778_);
v___x_834_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_804_);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref(v_e_778_);
v___x_837_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_a_779_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
v___jp_789_:
{
lean_object* v___x_793_; 
v___x_793_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_777_, v_d_790_, v___y_792_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v_fst_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
v_fst_795_ = lean_ctor_get(v_a_794_, 0);
if (lean_obj_tag(v_fst_795_) == 0)
{
lean_dec(v_a_794_);
lean_dec_ref(v_b_791_);
return v___x_793_;
}
else
{
lean_object* v_snd_796_; 
lean_dec_ref(v___x_793_);
v_snd_796_ = lean_ctor_get(v_a_794_, 1);
lean_inc(v_snd_796_);
lean_dec(v_a_794_);
v_e_778_ = v_b_791_;
v_a_779_ = v_snd_796_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_791_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(lean_object* v_mvarId_840_, lean_object* v_mvarId_x27_841_, lean_object* v_a_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_instBEqMVarId_beq(v_mvarId_840_, v_mvarId_x27_841_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_841_, v_a_842_, v___y_848_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_937_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_937_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_937_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_937_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_fst_858_; 
v_fst_858_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_fst_858_);
if (lean_obj_tag(v_fst_858_) == 0)
{
lean_object* v_snd_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_mvarId_x27_841_);
v_snd_859_ = lean_ctor_get(v_a_854_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_a_854_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v_a_854_, 0);
lean_dec(v_unused_878_);
v___x_861_ = v_a_854_;
v_isShared_862_ = v_isSharedCheck_877_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_snd_859_);
lean_dec(v_a_854_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_877_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_876_; 
v_a_863_ = lean_ctor_get(v_fst_858_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v_fst_858_);
if (v_isSharedCheck_876_ == 0)
{
v___x_865_ = v_fst_858_;
v_isShared_866_ = v_isSharedCheck_876_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v_fst_858_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_876_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_875_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_868_);
v___x_870_ = v___x_861_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_snd_859_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_870_);
v___x_872_ = v___x_856_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
else
{
lean_object* v_a_879_; 
lean_del_object(v___x_856_);
v_a_879_ = lean_ctor_get(v_fst_858_, 0);
lean_inc(v_a_879_);
lean_dec_ref(v_fst_858_);
if (lean_obj_tag(v_a_879_) == 0)
{
lean_object* v_snd_880_; lean_object* v___x_881_; 
v_snd_880_ = lean_ctor_get(v_a_854_, 1);
lean_inc(v_snd_880_);
lean_dec(v_a_854_);
v___x_881_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_841_, v_snd_880_, v___y_848_);
lean_dec(v_mvarId_x27_841_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_925_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_925_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_925_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_925_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_fst_886_; 
v_fst_886_ = lean_ctor_get(v_a_882_, 0);
lean_inc(v_fst_886_);
if (lean_obj_tag(v_fst_886_) == 0)
{
lean_object* v_snd_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_905_; 
v_snd_887_ = lean_ctor_get(v_a_882_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v_a_882_, 0);
lean_dec(v_unused_906_);
v___x_889_ = v_a_882_;
v_isShared_890_ = v_isSharedCheck_905_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snd_887_);
lean_dec(v_a_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_905_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_904_; 
v_a_891_ = lean_ctor_get(v_fst_886_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v_fst_886_);
if (v_isSharedCheck_904_ == 0)
{
v___x_893_ = v_fst_886_;
v_isShared_894_ = v_isSharedCheck_904_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v_fst_886_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_904_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_903_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_896_);
v___x_898_ = v___x_889_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_snd_887_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_898_);
v___x_900_ = v___x_884_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
else
{
lean_object* v_a_907_; 
v_a_907_ = lean_ctor_get(v_fst_886_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v_fst_886_);
if (lean_obj_tag(v_a_907_) == 0)
{
lean_object* v_snd_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_919_; 
v_snd_908_ = lean_ctor_get(v_a_882_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_a_882_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v_a_882_, 0);
lean_dec(v_unused_920_);
v___x_910_ = v_a_882_;
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_snd_908_);
lean_dec(v_a_882_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_908_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_914_);
v___x_916_ = v___x_884_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_val_921_; lean_object* v_snd_922_; lean_object* v_mvarIdPending_923_; 
lean_del_object(v___x_884_);
v_val_921_ = lean_ctor_get(v_a_907_, 0);
lean_inc(v_val_921_);
lean_dec_ref(v_a_907_);
v_snd_922_ = lean_ctor_get(v_a_882_, 1);
lean_inc(v_snd_922_);
lean_dec(v_a_882_);
v_mvarIdPending_923_ = lean_ctor_get(v_val_921_, 1);
lean_inc(v_mvarIdPending_923_);
lean_dec(v_val_921_);
v_mvarId_x27_841_ = v_mvarIdPending_923_;
v_a_842_ = v_snd_922_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_881_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_881_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
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
else
{
lean_object* v_snd_934_; lean_object* v_val_935_; lean_object* v___x_936_; 
lean_dec(v_mvarId_x27_841_);
v_snd_934_ = lean_ctor_get(v_a_854_, 1);
lean_inc(v_snd_934_);
lean_dec(v_a_854_);
v_val_935_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_val_935_);
lean_dec_ref(v_a_879_);
v___x_936_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_840_, v_val_935_, v_snd_934_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
return v___x_936_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_mvarId_x27_841_);
v_a_938_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_853_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_853_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v_mvarId_x27_841_);
v___x_946_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__1));
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_842_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_949_, lean_object* v_mvarId_x27_950_, lean_object* v_a_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(v_mvarId_949_, v_mvarId_x27_950_, v_a_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v_mvarId_949_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object* v_mvarId_962_, lean_object* v_e_963_, lean_object* v_a_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_962_, v_e_963_, v_a_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v_mvarId_962_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
v___x_976_ = lean_unsigned_to_nat(16u);
v___x_977_ = lean_mk_array(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object* v_mvarId_981_, lean_object* v_e_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = l_Lean_Expr_hasExprMVar(v_e_982_);
if (v___x_992_ == 0)
{
uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec_ref(v_e_982_);
v___x_993_ = 1;
v___x_994_ = lean_box(v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1);
v___x_997_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_981_, v_e_982_, v___x_996_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1012_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1012_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1012_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_fst_1002_; 
v_fst_1002_ = lean_ctor_get(v_a_998_, 0);
lean_inc(v_fst_1002_);
lean_dec(v_a_998_);
if (lean_obj_tag(v_fst_1002_) == 0)
{
uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
lean_dec_ref(v_fst_1002_);
v___x_1003_ = 0;
v___x_1004_ = lean_box(v___x_1003_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1004_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_dec_ref(v_fst_1002_);
v___x_1008_ = lean_box(v___x_992_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1008_);
v___x_1010_ = v___x_1000_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_997_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_997_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object* v_mvarId_1021_, lean_object* v_e_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(v_mvarId_1021_, v_e_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v_mvarId_1021_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v_ks_1037_; lean_object* v_vs_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1062_; 
v_ks_1037_ = lean_ctor_get(v_x_1033_, 0);
v_vs_1038_ = lean_ctor_get(v_x_1033_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_1033_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1040_ = v_x_1033_;
v_isShared_1041_ = v_isSharedCheck_1062_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_vs_1038_);
lean_inc(v_ks_1037_);
lean_dec(v_x_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1062_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_array_get_size(v_ks_1037_);
v___x_1043_ = lean_nat_dec_lt(v_x_1034_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_dec(v_x_1034_);
v___x_1044_ = lean_array_push(v_ks_1037_, v_x_1035_);
v___x_1045_ = lean_array_push(v_vs_1038_, v_x_1036_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1045_);
lean_ctor_set(v___x_1040_, 0, v___x_1044_);
v___x_1047_ = v___x_1040_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
else
{
lean_object* v_k_x27_1049_; uint8_t v___x_1050_; 
v_k_x27_1049_ = lean_array_fget_borrowed(v_ks_1037_, v_x_1034_);
v___x_1050_ = l_Lean_instBEqMVarId_beq(v_x_1035_, v_k_x27_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1052_; 
if (v_isShared_1041_ == 0)
{
v___x_1052_ = v___x_1040_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_ks_1037_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_vs_1038_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_unsigned_to_nat(1u);
v___x_1054_ = lean_nat_add(v_x_1034_, v___x_1053_);
lean_dec(v_x_1034_);
v_x_1033_ = v___x_1052_;
v_x_1034_ = v___x_1054_;
goto _start;
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = lean_array_fset(v_ks_1037_, v_x_1034_, v_x_1035_);
v___x_1058_ = lean_array_fset(v_vs_1038_, v_x_1034_, v_x_1036_);
lean_dec(v_x_1034_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1058_);
lean_ctor_set(v___x_1040_, 0, v___x_1057_);
v___x_1060_ = v___x_1040_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1058_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1063_, lean_object* v_k_1064_, lean_object* v_v_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1063_, v___x_1066_, v_k_1064_, v_v_1065_);
return v___x_1067_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; 
v___x_1068_ = ((size_t)5ULL);
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_shift_left(v___x_1069_, v___x_1068_);
return v___x_1070_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; 
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1073_ = lean_usize_sub(v___x_1072_, v___x_1071_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(lean_object* v_x_1075_, size_t v_x_1076_, size_t v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v_es_1080_; size_t v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v_j_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_es_1080_ = lean_ctor_get(v_x_1075_, 0);
v___x_1081_ = ((size_t)5ULL);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1);
v___x_1084_ = lean_usize_land(v_x_1076_, v___x_1083_);
v_j_1085_ = lean_usize_to_nat(v___x_1084_);
v___x_1086_ = lean_array_get_size(v_es_1080_);
v___x_1087_ = lean_nat_dec_lt(v_j_1085_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_dec(v_j_1085_);
lean_dec(v_x_1079_);
lean_dec(v_x_1078_);
return v_x_1075_;
}
else
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1124_; 
lean_inc_ref(v_es_1080_);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_x_1075_, 0);
lean_dec(v_unused_1125_);
v___x_1089_ = v_x_1075_;
v_isShared_1090_ = v_isSharedCheck_1124_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v_x_1075_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1124_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_v_1091_; lean_object* v___x_1092_; lean_object* v_xs_x27_1093_; lean_object* v___y_1095_; 
v_v_1091_ = lean_array_fget(v_es_1080_, v_j_1085_);
v___x_1092_ = lean_box(0);
v_xs_x27_1093_ = lean_array_fset(v_es_1080_, v_j_1085_, v___x_1092_);
switch(lean_obj_tag(v_v_1091_))
{
case 0:
{
lean_object* v_key_1100_; lean_object* v_val_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1111_; 
v_key_1100_ = lean_ctor_get(v_v_1091_, 0);
v_val_1101_ = lean_ctor_get(v_v_1091_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_v_1091_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1103_ = v_v_1091_;
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_val_1101_);
lean_inc(v_key_1100_);
lean_dec(v_v_1091_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1111_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_instBEqMVarId_beq(v_x_1078_, v_key_1100_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_del_object(v___x_1103_);
v___x_1106_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1100_, v_val_1101_, v_x_1078_, v_x_1079_);
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
v___y_1095_ = v___x_1107_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_val_1101_);
lean_dec(v_key_1100_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 1, v_x_1079_);
lean_ctor_set(v___x_1103_, 0, v_x_1078_);
v___x_1109_ = v___x_1103_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_x_1078_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_x_1079_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
v___y_1095_ = v___x_1109_;
goto v___jp_1094_;
}
}
}
}
case 1:
{
lean_object* v_node_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1122_; 
v_node_1112_ = lean_ctor_get(v_v_1091_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_v_1091_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1114_ = v_v_1091_;
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_node_1112_);
lean_dec(v_v_1091_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1122_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1116_ = lean_usize_shift_right(v_x_1076_, v___x_1081_);
v___x_1117_ = lean_usize_add(v_x_1077_, v___x_1082_);
v___x_1118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_node_1112_, v___x_1116_, v___x_1117_, v_x_1078_, v_x_1079_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1118_);
v___x_1120_ = v___x_1114_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
v___y_1095_ = v___x_1120_;
goto v___jp_1094_;
}
}
}
default: 
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_x_1078_);
lean_ctor_set(v___x_1123_, 1, v_x_1079_);
v___y_1095_ = v___x_1123_;
goto v___jp_1094_;
}
}
v___jp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_array_fset(v_xs_x27_1093_, v_j_1085_, v___y_1095_);
lean_dec(v_j_1085_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1096_);
v___x_1098_ = v___x_1089_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_object* v_ks_1126_; lean_object* v_vs_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1147_; 
v_ks_1126_ = lean_ctor_get(v_x_1075_, 0);
v_vs_1127_ = lean_ctor_get(v_x_1075_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1129_ = v_x_1075_;
v_isShared_1130_ = v_isSharedCheck_1147_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_vs_1127_);
lean_inc(v_ks_1126_);
lean_dec(v_x_1075_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1147_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_ks_1126_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_vs_1127_);
v___x_1132_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v_newNode_1133_; uint8_t v___y_1135_; size_t v___x_1141_; uint8_t v___x_1142_; 
v_newNode_1133_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1132_, v_x_1078_, v_x_1079_);
v___x_1141_ = ((size_t)7ULL);
v___x_1142_ = lean_usize_dec_le(v___x_1141_, v_x_1077_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1143_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1133_);
v___x_1144_ = lean_unsigned_to_nat(4u);
v___x_1145_ = lean_nat_dec_lt(v___x_1143_, v___x_1144_);
lean_dec(v___x_1143_);
v___y_1135_ = v___x_1145_;
goto v___jp_1134_;
}
else
{
v___y_1135_ = v___x_1142_;
goto v___jp_1134_;
}
v___jp_1134_:
{
if (v___y_1135_ == 0)
{
lean_object* v_ks_1136_; lean_object* v_vs_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_ks_1136_ = lean_ctor_get(v_newNode_1133_, 0);
lean_inc_ref(v_ks_1136_);
v_vs_1137_ = lean_ctor_get(v_newNode_1133_, 1);
lean_inc_ref(v_vs_1137_);
lean_dec_ref(v_newNode_1133_);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2);
v___x_1140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1077_, v_ks_1136_, v_vs_1137_, v___x_1138_, v___x_1139_);
lean_dec_ref(v_vs_1137_);
lean_dec_ref(v_ks_1136_);
return v___x_1140_;
}
else
{
return v_newNode_1133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1148_, lean_object* v_keys_1149_, lean_object* v_vals_1150_, lean_object* v_i_1151_, lean_object* v_entries_1152_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_array_get_size(v_keys_1149_);
v___x_1154_ = lean_nat_dec_lt(v_i_1151_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec(v_i_1151_);
return v_entries_1152_;
}
else
{
lean_object* v_k_1155_; lean_object* v_v_1156_; uint64_t v___x_1157_; size_t v_h_1158_; size_t v___x_1159_; lean_object* v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v_h_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_k_1155_ = lean_array_fget_borrowed(v_keys_1149_, v_i_1151_);
v_v_1156_ = lean_array_fget_borrowed(v_vals_1150_, v_i_1151_);
v___x_1157_ = l_Lean_instHashableMVarId_hash(v_k_1155_);
v_h_1158_ = lean_uint64_to_usize(v___x_1157_);
v___x_1159_ = ((size_t)5ULL);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_sub(v_depth_1148_, v___x_1161_);
v___x_1163_ = lean_usize_mul(v___x_1159_, v___x_1162_);
v_h_1164_ = lean_usize_shift_right(v_h_1158_, v___x_1163_);
v___x_1165_ = lean_nat_add(v_i_1151_, v___x_1160_);
lean_dec(v_i_1151_);
lean_inc(v_v_1156_);
lean_inc(v_k_1155_);
v___x_1166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_entries_1152_, v_h_1164_, v_depth_1148_, v_k_1155_, v_v_1156_);
v_i_1151_ = v___x_1165_;
v_entries_1152_ = v___x_1166_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1168_, lean_object* v_keys_1169_, lean_object* v_vals_1170_, lean_object* v_i_1171_, lean_object* v_entries_1172_){
_start:
{
size_t v_depth_boxed_1173_; lean_object* v_res_1174_; 
v_depth_boxed_1173_ = lean_unbox_usize(v_depth_1168_);
lean_dec(v_depth_1168_);
v_res_1174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1173_, v_keys_1169_, v_vals_1170_, v_i_1171_, v_entries_1172_);
lean_dec_ref(v_vals_1170_);
lean_dec_ref(v_keys_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_){
_start:
{
size_t v_x_80131__boxed_1180_; size_t v_x_80132__boxed_1181_; lean_object* v_res_1182_; 
v_x_80131__boxed_1180_ = lean_unbox_usize(v_x_1176_);
lean_dec(v_x_1176_);
v_x_80132__boxed_1181_ = lean_unbox_usize(v_x_1177_);
lean_dec(v_x_1177_);
v_res_1182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_1175_, v_x_80131__boxed_1180_, v_x_80132__boxed_1181_, v_x_1178_, v_x_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(lean_object* v_x_1183_, lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
uint64_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1186_ = l_Lean_instHashableMVarId_hash(v_x_1184_);
v___x_1187_ = lean_uint64_to_usize(v___x_1186_);
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_1183_, v___x_1187_, v___x_1188_, v_x_1184_, v_x_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(lean_object* v_mvarId_1190_, lean_object* v_val_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; lean_object* v_mctx_1195_; lean_object* v_cache_1196_; lean_object* v_zetaDeltaFVarIds_1197_; lean_object* v_postponed_1198_; lean_object* v_diag_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1227_; 
v___x_1194_ = lean_st_ref_take(v___y_1192_);
v_mctx_1195_ = lean_ctor_get(v___x_1194_, 0);
v_cache_1196_ = lean_ctor_get(v___x_1194_, 1);
v_zetaDeltaFVarIds_1197_ = lean_ctor_get(v___x_1194_, 2);
v_postponed_1198_ = lean_ctor_get(v___x_1194_, 3);
v_diag_1199_ = lean_ctor_get(v___x_1194_, 4);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1201_ = v___x_1194_;
v_isShared_1202_ = v_isSharedCheck_1227_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_diag_1199_);
lean_inc(v_postponed_1198_);
lean_inc(v_zetaDeltaFVarIds_1197_);
lean_inc(v_cache_1196_);
lean_inc(v_mctx_1195_);
lean_dec(v___x_1194_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1227_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_depth_1203_; lean_object* v_levelAssignDepth_1204_; lean_object* v_lmvarCounter_1205_; lean_object* v_mvarCounter_1206_; lean_object* v_lDecls_1207_; lean_object* v_decls_1208_; lean_object* v_userNames_1209_; lean_object* v_lAssignment_1210_; lean_object* v_eAssignment_1211_; lean_object* v_dAssignment_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1226_; 
v_depth_1203_ = lean_ctor_get(v_mctx_1195_, 0);
v_levelAssignDepth_1204_ = lean_ctor_get(v_mctx_1195_, 1);
v_lmvarCounter_1205_ = lean_ctor_get(v_mctx_1195_, 2);
v_mvarCounter_1206_ = lean_ctor_get(v_mctx_1195_, 3);
v_lDecls_1207_ = lean_ctor_get(v_mctx_1195_, 4);
v_decls_1208_ = lean_ctor_get(v_mctx_1195_, 5);
v_userNames_1209_ = lean_ctor_get(v_mctx_1195_, 6);
v_lAssignment_1210_ = lean_ctor_get(v_mctx_1195_, 7);
v_eAssignment_1211_ = lean_ctor_get(v_mctx_1195_, 8);
v_dAssignment_1212_ = lean_ctor_get(v_mctx_1195_, 9);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_mctx_1195_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1214_ = v_mctx_1195_;
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_dAssignment_1212_);
lean_inc(v_eAssignment_1211_);
lean_inc(v_lAssignment_1210_);
lean_inc(v_userNames_1209_);
lean_inc(v_decls_1208_);
lean_inc(v_lDecls_1207_);
lean_inc(v_mvarCounter_1206_);
lean_inc(v_lmvarCounter_1205_);
lean_inc(v_levelAssignDepth_1204_);
lean_inc(v_depth_1203_);
lean_dec(v_mctx_1195_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1226_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_eAssignment_1211_, v_mvarId_1190_, v_val_1191_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 8, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_depth_1203_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_levelAssignDepth_1204_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_lmvarCounter_1205_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_mvarCounter_1206_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_lDecls_1207_);
lean_ctor_set(v_reuseFailAlloc_1225_, 5, v_decls_1208_);
lean_ctor_set(v_reuseFailAlloc_1225_, 6, v_userNames_1209_);
lean_ctor_set(v_reuseFailAlloc_1225_, 7, v_lAssignment_1210_);
lean_ctor_set(v_reuseFailAlloc_1225_, 8, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1225_, 9, v_dAssignment_1212_);
v___x_1218_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1218_);
v___x_1220_ = v___x_1201_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_cache_1196_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_zetaDeltaFVarIds_1197_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_postponed_1198_);
lean_ctor_set(v_reuseFailAlloc_1224_, 4, v_diag_1199_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_st_ref_set(v___y_1192_, v___x_1220_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg___boxed(lean_object* v_mvarId_1228_, lean_object* v_val_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_1228_, v_val_1229_, v___y_1230_);
lean_dec(v___y_1230_);
return v_res_1232_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1241_, uint8_t v_suppressElabErrors_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1243_) == 1)
{
lean_object* v_pre_1244_; 
v_pre_1244_ = lean_ctor_get(v_x_1243_, 0);
switch(lean_obj_tag(v_pre_1244_))
{
case 1:
{
lean_object* v_pre_1245_; 
v_pre_1245_ = lean_ctor_get(v_pre_1244_, 0);
switch(lean_obj_tag(v_pre_1245_))
{
case 0:
{
lean_object* v_str_1246_; lean_object* v_str_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_str_1246_ = lean_ctor_get(v_x_1243_, 1);
v_str_1247_ = lean_ctor_get(v_pre_1244_, 1);
v___x_1248_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1249_ = lean_string_dec_eq(v_str_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1251_ = lean_string_dec_eq(v_str_1247_, v___x_1250_);
if (v___x_1251_ == 0)
{
return v___y_1241_;
}
else
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1253_ = lean_string_dec_eq(v_str_1246_, v___x_1252_);
if (v___x_1253_ == 0)
{
return v___y_1241_;
}
else
{
return v_suppressElabErrors_1242_;
}
}
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1255_ = lean_string_dec_eq(v_str_1246_, v___x_1254_);
if (v___x_1255_ == 0)
{
return v___y_1241_;
}
else
{
return v_suppressElabErrors_1242_;
}
}
}
case 1:
{
lean_object* v_pre_1256_; 
v_pre_1256_ = lean_ctor_get(v_pre_1245_, 0);
if (lean_obj_tag(v_pre_1256_) == 0)
{
lean_object* v_str_1257_; lean_object* v_str_1258_; lean_object* v_str_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_str_1257_ = lean_ctor_get(v_x_1243_, 1);
v_str_1258_ = lean_ctor_get(v_pre_1244_, 1);
v_str_1259_ = lean_ctor_get(v_pre_1245_, 1);
v___x_1260_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1261_ = lean_string_dec_eq(v_str_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
return v___y_1241_;
}
else
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1263_ = lean_string_dec_eq(v_str_1258_, v___x_1262_);
if (v___x_1263_ == 0)
{
return v___y_1241_;
}
else
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1265_ = lean_string_dec_eq(v_str_1257_, v___x_1264_);
if (v___x_1265_ == 0)
{
return v___y_1241_;
}
else
{
return v_suppressElabErrors_1242_;
}
}
}
}
else
{
return v___y_1241_;
}
}
default: 
{
return v___y_1241_;
}
}
}
case 0:
{
lean_object* v_str_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_str_1266_ = lean_ctor_get(v_x_1243_, 1);
v___x_1267_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1268_ = lean_string_dec_eq(v_str_1266_, v___x_1267_);
if (v___x_1268_ == 0)
{
return v___y_1241_;
}
else
{
return v_suppressElabErrors_1242_;
}
}
default: 
{
return v___y_1241_;
}
}
}
else
{
return v___y_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1269_, lean_object* v_suppressElabErrors_1270_, lean_object* v_x_1271_){
_start:
{
uint8_t v___y_80366__boxed_1272_; uint8_t v_suppressElabErrors_boxed_1273_; uint8_t v_res_1274_; lean_object* v_r_1275_; 
v___y_80366__boxed_1272_ = lean_unbox(v___y_1269_);
v_suppressElabErrors_boxed_1273_ = lean_unbox(v_suppressElabErrors_1270_);
v_res_1274_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(v___y_80366__boxed_1272_, v_suppressElabErrors_boxed_1273_, v_x_1271_);
lean_dec(v_x_1271_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1277_, lean_object* v_msgData_1278_, uint8_t v_severity_1279_, uint8_t v_isSilent_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; uint8_t v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1324_; lean_object* v___y_1325_; uint8_t v___y_1326_; lean_object* v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1329_; uint8_t v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1349_; uint8_t v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; uint8_t v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; uint8_t v___x_1371_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; uint8_t v___y_1379_; uint8_t v___y_1381_; uint8_t v___x_1396_; 
v___x_1371_ = 2;
v___x_1396_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1279_, v___x_1371_);
if (v___x_1396_ == 0)
{
v___y_1381_ = v___x_1396_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1397_; 
lean_inc_ref(v_msgData_1278_);
v___x_1397_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1278_);
v___y_1381_ = v___x_1397_;
goto v___jp_1380_;
}
v___jp_1286_:
{
lean_object* v___x_1296_; lean_object* v_currNamespace_1297_; lean_object* v_openDecls_1298_; lean_object* v_env_1299_; lean_object* v_nextMacroScope_1300_; lean_object* v_ngen_1301_; lean_object* v_auxDeclNGen_1302_; lean_object* v_traceState_1303_; lean_object* v_cache_1304_; lean_object* v_messages_1305_; lean_object* v_infoState_1306_; lean_object* v_snapshotTasks_1307_; lean_object* v_newDecls_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1322_; 
v___x_1296_ = lean_st_ref_take(v___y_1295_);
v_currNamespace_1297_ = lean_ctor_get(v___y_1294_, 6);
v_openDecls_1298_ = lean_ctor_get(v___y_1294_, 7);
v_env_1299_ = lean_ctor_get(v___x_1296_, 0);
v_nextMacroScope_1300_ = lean_ctor_get(v___x_1296_, 1);
v_ngen_1301_ = lean_ctor_get(v___x_1296_, 2);
v_auxDeclNGen_1302_ = lean_ctor_get(v___x_1296_, 3);
v_traceState_1303_ = lean_ctor_get(v___x_1296_, 4);
v_cache_1304_ = lean_ctor_get(v___x_1296_, 5);
v_messages_1305_ = lean_ctor_get(v___x_1296_, 6);
v_infoState_1306_ = lean_ctor_get(v___x_1296_, 7);
v_snapshotTasks_1307_ = lean_ctor_get(v___x_1296_, 8);
v_newDecls_1308_ = lean_ctor_get(v___x_1296_, 9);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1310_ = v___x_1296_;
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_newDecls_1308_);
lean_inc(v_snapshotTasks_1307_);
lean_inc(v_infoState_1306_);
lean_inc(v_messages_1305_);
lean_inc(v_cache_1304_);
lean_inc(v_traceState_1303_);
lean_inc(v_auxDeclNGen_1302_);
lean_inc(v_ngen_1301_);
lean_inc(v_nextMacroScope_1300_);
lean_inc(v_env_1299_);
lean_dec(v___x_1296_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_inc(v_openDecls_1298_);
lean_inc(v_currNamespace_1297_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v_currNamespace_1297_);
lean_ctor_set(v___x_1312_, 1, v_openDecls_1298_);
v___x_1313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___y_1292_);
lean_inc_ref(v___y_1289_);
lean_inc_ref(v___y_1291_);
v___x_1314_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1314_, 0, v___y_1291_);
lean_ctor_set(v___x_1314_, 1, v___y_1290_);
lean_ctor_set(v___x_1314_, 2, v___y_1288_);
lean_ctor_set(v___x_1314_, 3, v___y_1289_);
lean_ctor_set(v___x_1314_, 4, v___x_1313_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5, v___y_1293_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5 + 1, v___y_1287_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*5 + 2, v_isSilent_1280_);
v___x_1315_ = l_Lean_MessageLog_add(v___x_1314_, v_messages_1305_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 6, v___x_1315_);
v___x_1317_ = v___x_1310_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_env_1299_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1300_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1301_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1302_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_traceState_1303_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_cache_1304_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_infoState_1306_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_snapshotTasks_1307_);
lean_ctor_set(v_reuseFailAlloc_1321_, 9, v_newDecls_1308_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_st_ref_set(v___y_1295_, v___x_1317_);
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
v___x_1332_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1278_);
v___x_1333_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v___x_1332_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
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
lean_inc_ref_n(v___y_1327_, 2);
v___x_1338_ = l_Lean_FileMap_toPosition(v___y_1327_, v___y_1325_);
lean_dec(v___y_1325_);
v___x_1339_ = l_Lean_FileMap_toPosition(v___y_1327_, v___y_1331_);
lean_dec(v___y_1331_);
v___x_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
v___x_1341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1328_ == 0)
{
lean_del_object(v___x_1336_);
lean_dec_ref(v___y_1324_);
v___y_1287_ = v___y_1326_;
v___y_1288_ = v___x_1340_;
v___y_1289_ = v___x_1341_;
v___y_1290_ = v___x_1338_;
v___y_1291_ = v___y_1329_;
v___y_1292_ = v_a_1334_;
v___y_1293_ = v___y_1330_;
v___y_1294_ = v___y_1283_;
v___y_1295_ = v___y_1284_;
goto v___jp_1286_;
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
v___y_1287_ = v___y_1326_;
v___y_1288_ = v___x_1340_;
v___y_1289_ = v___x_1341_;
v___y_1290_ = v___x_1338_;
v___y_1291_ = v___y_1329_;
v___y_1292_ = v_a_1334_;
v___y_1293_ = v___y_1330_;
v___y_1294_ = v___y_1283_;
v___y_1295_ = v___y_1284_;
goto v___jp_1286_;
}
}
}
}
v___jp_1348_:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Syntax_getTailPos_x3f(v___y_1355_, v___y_1354_);
lean_dec(v___y_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_inc(v___y_1356_);
v___y_1324_ = v___y_1349_;
v___y_1325_ = v___y_1356_;
v___y_1326_ = v___y_1350_;
v___y_1327_ = v___y_1351_;
v___y_1328_ = v___y_1353_;
v___y_1329_ = v___y_1352_;
v___y_1330_ = v___y_1354_;
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
v___y_1325_ = v___y_1356_;
v___y_1326_ = v___y_1350_;
v___y_1327_ = v___y_1351_;
v___y_1328_ = v___y_1353_;
v___y_1329_ = v___y_1352_;
v___y_1330_ = v___y_1354_;
v___y_1331_ = v_val_1358_;
goto v___jp_1323_;
}
}
v___jp_1359_:
{
lean_object* v_ref_1367_; lean_object* v___x_1368_; 
v_ref_1367_ = l_Lean_replaceRef(v_ref_1277_, v___y_1365_);
v___x_1368_ = l_Lean_Syntax_getPos_x3f(v_ref_1367_, v___y_1364_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___y_1349_ = v___y_1360_;
v___y_1350_ = v___y_1366_;
v___y_1351_ = v___y_1361_;
v___y_1352_ = v___y_1363_;
v___y_1353_ = v___y_1362_;
v___y_1354_ = v___y_1364_;
v___y_1355_ = v_ref_1367_;
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
v___y_1350_ = v___y_1366_;
v___y_1351_ = v___y_1361_;
v___y_1352_ = v___y_1363_;
v___y_1353_ = v___y_1362_;
v___y_1354_ = v___y_1364_;
v___y_1355_ = v_ref_1367_;
v___y_1356_ = v_val_1370_;
goto v___jp_1348_;
}
}
v___jp_1372_:
{
if (v___y_1379_ == 0)
{
v___y_1360_ = v___y_1373_;
v___y_1361_ = v___y_1374_;
v___y_1362_ = v___y_1376_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1378_;
v___y_1365_ = v___y_1377_;
v___y_1366_ = v_severity_1279_;
goto v___jp_1359_;
}
else
{
v___y_1360_ = v___y_1373_;
v___y_1361_ = v___y_1374_;
v___y_1362_ = v___y_1376_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1378_;
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
v_fileName_1382_ = lean_ctor_get(v___y_1283_, 0);
v_fileMap_1383_ = lean_ctor_get(v___y_1283_, 1);
v_options_1384_ = lean_ctor_get(v___y_1283_, 2);
v_ref_1385_ = lean_ctor_get(v___y_1283_, 5);
v_suppressElabErrors_1386_ = lean_ctor_get_uint8(v___y_1283_, sizeof(void*)*14 + 1);
v___x_1387_ = lean_box(v___y_1381_);
v___x_1388_ = lean_box(v_suppressElabErrors_1386_);
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1389_, 0, v___x_1387_);
lean_closure_set(v___f_1389_, 1, v___x_1388_);
v___x_1390_ = 1;
v___x_1391_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1279_, v___x_1390_);
if (v___x_1391_ == 0)
{
v___y_1373_ = v___f_1389_;
v___y_1374_ = v_fileMap_1383_;
v___y_1375_ = v_fileName_1382_;
v___y_1376_ = v_suppressElabErrors_1386_;
v___y_1377_ = v_ref_1385_;
v___y_1378_ = v___y_1381_;
v___y_1379_ = v___x_1391_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = l_Lean_warningAsError;
v___x_1393_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_1384_, v___x_1392_);
v___y_1373_ = v___f_1389_;
v___y_1374_ = v_fileMap_1383_;
v___y_1375_ = v_fileName_1382_;
v___y_1376_ = v_suppressElabErrors_1386_;
v___y_1377_ = v_ref_1385_;
v___y_1378_ = v___y_1381_;
v___y_1379_ = v___x_1393_;
goto v___jp_1372_;
}
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_dec_ref(v_msgData_1278_);
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
lean_dec_ref(v___y_1404_);
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
lean_dec_ref(v___y_1432_);
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
lean_dec_ref(v___y_1480_);
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
v_asyncMode_1491_ = lean_ctor_get(v_toEnvExtension_1490_, 2);
v___x_1492_ = lean_box(1);
v___x_1493_ = lean_box(0);
v_linterSets_1494_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1492_, v___x_1489_, v_env_1488_, v_asyncMode_1491_, v___x_1493_);
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
lean_dec_ref(v___y_1518_);
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
lean_inc_ref(v___y_1530_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc(v___y_1527_);
lean_inc_ref(v___y_1526_);
lean_inc(v___y_1525_);
lean_inc_ref(v___y_1524_);
v___x_1537_ = lean_apply_10(v_mkInfoTree_1523_, v_trees_1536_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1577_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1577_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1577_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v_infoState_1543_; lean_object* v_env_1544_; lean_object* v_nextMacroScope_1545_; lean_object* v_ngen_1546_; lean_object* v_auxDeclNGen_1547_; lean_object* v_traceState_1548_; lean_object* v_cache_1549_; lean_object* v_messages_1550_; lean_object* v_snapshotTasks_1551_; lean_object* v_newDecls_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1576_; 
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
v_newDecls_1552_ = lean_ctor_get(v___x_1542_, 9);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1554_ = v___x_1542_;
v_isShared_1555_ = v_isSharedCheck_1576_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_newDecls_1552_);
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
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1576_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
uint8_t v_enabled_1556_; lean_object* v_assignment_1557_; lean_object* v_lazyAssignment_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1574_; 
v_enabled_1556_ = lean_ctor_get_uint8(v_infoState_1543_, sizeof(void*)*3);
v_assignment_1557_ = lean_ctor_get(v_infoState_1543_, 0);
v_lazyAssignment_1558_ = lean_ctor_get(v_infoState_1543_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_infoState_1543_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; 
v_unused_1575_ = lean_ctor_get(v_infoState_1543_, 2);
lean_dec(v_unused_1575_);
v___x_1560_ = v_infoState_1543_;
v_isShared_1561_ = v_isSharedCheck_1574_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_lazyAssignment_1558_);
lean_inc(v_assignment_1557_);
lean_dec(v_infoState_1543_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1574_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = l_Lean_PersistentArray_push___redArg(v_a_1531_, v_a_1538_);
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
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_env_1544_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_nextMacroScope_1545_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_ngen_1546_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_auxDeclNGen_1547_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_traceState_1548_);
lean_ctor_set(v_reuseFailAlloc_1572_, 5, v_cache_1549_);
lean_ctor_set(v_reuseFailAlloc_1572_, 6, v_messages_1550_);
lean_ctor_set(v_reuseFailAlloc_1572_, 7, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1572_, 8, v_snapshotTasks_1551_);
lean_ctor_set(v_reuseFailAlloc_1572_, 9, v_newDecls_1552_);
v___x_1566_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = lean_st_ref_set(v___y_1522_, v___x_1566_);
v___x_1568_ = lean_box(0);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1568_);
v___x_1570_ = v___x_1540_;
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
lean_dec_ref(v_a_1531_);
v_a_1578_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1537_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1537_);
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
v___y_1781_ = v___x_1907_;
v___y_1782_ = v_mvarCounter_1931_;
v___y_1783_ = v_a_1909_;
v___y_1784_ = v___x_1907_;
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
v___x_1746_ = l_Lean_Core_mkFreshUserName(v___y_1743_, v___y_1737_, v___y_1739_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_n(v_a_1747_, 2);
lean_dec_ref(v___x_1746_);
v___x_1748_ = l_Lean_MVarId_rename(v___y_1741_, v___y_1745_, v_a_1747_, v___y_1736_, v___y_1735_, v___y_1737_, v___y_1739_);
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
lean_closure_set(v___f_1753_, 6, v___y_1732_);
lean_closure_set(v___f_1753_, 7, v___x_1699_);
lean_closure_set(v___f_1753_, 8, v___y_1731_);
v___x_1754_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_a_1749_, v___f_1753_, v___y_1740_, v___y_1738_, v___y_1742_, v___y_1734_, v___y_1736_, v___y_1735_, v___y_1737_, v___y_1739_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_dec_ref(v___x_1754_);
v___y_1717_ = v___y_1733_;
v___y_1718_ = v___y_1744_;
v___y_1719_ = v___y_1735_;
goto v___jp_1716_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v___y_1744_);
lean_dec_ref(v___y_1733_);
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
lean_dec_ref(v___y_1744_);
lean_dec_ref(v___y_1733_);
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
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1733_);
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
lean_inc_ref(v___y_1783_);
v___x_1801_ = l_Lean_MVarId_note(v___x_1799_, v___x_1800_, v___y_1783_, v___y_1784_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
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
lean_dec_ref(v___y_1783_);
v___y_1717_ = v_snd_1813_;
v___y_1718_ = v_a_1798_;
v___y_1719_ = v___y_1790_;
goto v___jp_1716_;
}
else
{
if (lean_obj_tag(v___y_1783_) == 1)
{
lean_object* v_fvarId_1820_; lean_object* v_lctx_1821_; lean_object* v___x_1822_; 
v_fvarId_1820_ = lean_ctor_get(v___y_1783_, 0);
v_lctx_1821_ = lean_ctor_get(v___y_1789_, 2);
lean_inc(v_fvarId_1820_);
lean_inc_ref(v_lctx_1821_);
v___x_1822_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1821_, v_fvarId_1820_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_dec_ref(v___y_1783_);
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
lean_dec_ref(v___y_1783_);
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
v___x_1826_ = l_Lean_MessageData_ofExpr(v___y_1783_);
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
lean_dec_ref(v___y_1783_);
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
lean_dec_ref(v___y_1783_);
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
v___y_1733_ = v_snd_1849_;
v___y_1734_ = v___y_1788_;
v___y_1735_ = v___y_1790_;
v___y_1736_ = v___y_1789_;
v___y_1737_ = v___y_1791_;
v___y_1738_ = v___y_1786_;
v___y_1739_ = v___y_1792_;
v___y_1740_ = v___y_1785_;
v___y_1741_ = v_snd_1851_;
v___y_1742_ = v___y_1787_;
v___y_1743_ = v___x_1800_;
v___y_1744_ = v_a_1798_;
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
v___y_1733_ = v_snd_1849_;
v___y_1734_ = v___y_1788_;
v___y_1735_ = v___y_1790_;
v___y_1736_ = v___y_1789_;
v___y_1737_ = v___y_1791_;
v___y_1738_ = v___y_1786_;
v___y_1739_ = v___y_1792_;
v___y_1740_ = v___y_1785_;
v___y_1741_ = v_snd_1851_;
v___y_1742_ = v___y_1787_;
v___y_1743_ = v___x_1800_;
v___y_1744_ = v_a_1798_;
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
lean_dec_ref(v___y_1783_);
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
lean_dec_ref(v___y_1783_);
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
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
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
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
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
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
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
uint8_t v___x_81079__boxed_2047_; uint8_t v___x_81080__boxed_2048_; uint8_t v___x_81081__boxed_2049_; lean_object* v_res_2050_; 
v___x_81079__boxed_2047_ = lean_unbox(v___x_2027_);
v___x_81080__boxed_2048_ = lean_unbox(v___x_2028_);
v___x_81081__boxed_2049_ = lean_unbox(v___x_2029_);
v_res_2050_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(v_usingArg_2025_, v_snd_2026_, v___x_81079__boxed_2047_, v___x_81080__boxed_2048_, v___x_81081__boxed_2049_, v___x_2030_, v___x_2031_, v___x_2032_, v_simprocs_2033_, v_discharge_x3f_2034_, v_snd_2035_, v___x_2036_, v___f_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
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
uint8_t v___x_81801__boxed_2215_; uint8_t v___x_81802__boxed_2216_; uint8_t v___x_81803__boxed_2217_; lean_object* v_res_2218_; 
v___x_81801__boxed_2215_ = lean_unbox(v___x_2198_);
v___x_81802__boxed_2216_ = lean_unbox(v___x_2200_);
v___x_81803__boxed_2217_ = lean_unbox(v___x_2201_);
v_res_2218_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(v___x_2192_, v_tk_2193_, v___x_2194_, v___x_2195_, v___x_2196_, v_simprocs_2197_, v___x_81801__boxed_2215_, v_usingArg_2199_, v___x_81802__boxed_2216_, v___x_81803__boxed_2217_, v___x_2202_, v___x_2203_, v_usingTk_x3f_2204_, v_discharge_x3f_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
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
lean_object* v___y_2279_; lean_object* v___y_2283_; lean_object* v_stx_2284_; lean_object* v___y_2285_; lean_object* v_ref_2286_; lean_object* v___y_2287_; lean_object* v___y_2306_; lean_object* v_stx_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v_options_2311_; lean_object* v_ref_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2483_; uint8_t v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2533_; lean_object* v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v_args_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v_only_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; uint8_t v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; uint8_t v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; uint8_t v___y_2684_; lean_object* v___y_2686_; uint8_t v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2762_; 
v_options_2311_ = lean_ctor_get(v___y_2275_, 2);
v_ref_2312_ = lean_ctor_get(v___y_2275_, 5);
v___x_2313_ = 0;
v___x_2314_ = l_Lean_SourceInfo_fromRef(v_ref_2312_, v___x_2313_);
v___x_2315_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3));
lean_inc_ref(v___x_2248_);
lean_inc_ref(v___x_2247_);
lean_inc_ref(v___x_2246_);
v___x_2316_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2315_);
lean_inc(v___x_2314_);
v___x_2317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2315_);
v___x_2318_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5));
v___x_2319_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6);
if (lean_obj_tag(v___y_2268_) == 0)
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2762_ = v___x_2771_;
goto v___jp_2761_;
}
else
{
lean_object* v_val_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_val_2772_ = lean_ctor_get(v___y_2268_, 0);
lean_inc(v_val_2772_);
lean_dec_ref(v___y_2268_);
v___x_2773_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2774_ = lean_array_push(v___x_2773_, v_val_2772_);
v___y_2762_ = v___x_2774_;
goto v___jp_2761_;
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
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
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
v___x_2295_ = l_Lean_MessageData_nil;
v___x_2296_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2245_, v___x_2291_, v___x_2292_, v___x_2293_, v___x_2290_, v___x_2294_, v___x_2295_, v___y_2285_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2285_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_dec_ref(v___x_2296_);
v___y_2279_ = v___y_2283_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec_ref(v___y_2283_);
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
v___jp_2305_:
{
lean_object* v_ref_2310_; 
v_ref_2310_ = lean_ctor_get(v___y_2308_, 5);
lean_inc(v_ref_2310_);
v___y_2283_ = v___y_2306_;
v_stx_2284_ = v_stx_2307_;
v___y_2285_ = v___y_2308_;
v_ref_2286_ = v_ref_2310_;
v___y_2287_ = v___y_2309_;
goto v___jp_2282_;
}
v___jp_2320_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2332_ = l_Array_append___redArg(v___x_2319_, v___y_2331_);
lean_dec_ref(v___y_2331_);
lean_inc_n(v___y_2328_, 2);
v___x_2333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2333_, 0, v___y_2328_);
lean_ctor_set(v___x_2333_, 1, v___x_2318_);
lean_ctor_set(v___x_2333_, 2, v___x_2332_);
v___x_2334_ = l_Lean_Syntax_node5(v___y_2328_, v___x_2249_, v___y_2324_, v___y_2329_, v___y_2323_, v___y_2330_, v___x_2333_);
lean_inc(v___y_2326_);
v___x_2335_ = l_Lean_Syntax_node4(v___y_2328_, v___x_2252_, v___y_2327_, v___y_2326_, v___y_2326_, v___x_2334_);
v___y_2306_ = v___y_2322_;
v_stx_2307_ = v___x_2335_;
v___y_2308_ = v___y_2321_;
v___y_2309_ = v___y_2325_;
goto v___jp_2305_;
}
v___jp_2336_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = l_Array_append___redArg(v___x_2319_, v___y_2347_);
lean_dec_ref(v___y_2347_);
lean_inc(v___y_2345_);
v___x_2349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2349_, 0, v___y_2345_);
lean_ctor_set(v___x_2349_, 1, v___x_2318_);
lean_ctor_set(v___x_2349_, 2, v___x_2348_);
if (lean_obj_tag(v___y_2337_) == 1)
{
lean_object* v_val_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v___x_2250_);
v_val_2350_ = lean_ctor_get(v___y_2337_, 0);
lean_inc(v_val_2350_);
lean_dec_ref(v___y_2337_);
v___x_2351_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2345_);
v___x_2352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2345_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = l_Array_mkArray2___redArg(v___x_2352_, v_val_2350_);
v___y_2321_ = v___y_2338_;
v___y_2322_ = v___y_2339_;
v___y_2323_ = v___y_2340_;
v___y_2324_ = v___y_2341_;
v___y_2325_ = v___y_2343_;
v___y_2326_ = v___y_2342_;
v___y_2327_ = v___y_2344_;
v___y_2328_ = v___y_2345_;
v___y_2329_ = v___y_2346_;
v___y_2330_ = v___x_2349_;
v___y_2331_ = v___x_2353_;
goto v___jp_2320_;
}
else
{
lean_object* v___x_2354_; 
lean_dec(v___y_2337_);
v___x_2354_ = lean_mk_empty_array_with_capacity(v___x_2250_);
lean_dec(v___x_2250_);
v___y_2321_ = v___y_2338_;
v___y_2322_ = v___y_2339_;
v___y_2323_ = v___y_2340_;
v___y_2324_ = v___y_2341_;
v___y_2325_ = v___y_2343_;
v___y_2326_ = v___y_2342_;
v___y_2327_ = v___y_2344_;
v___y_2328_ = v___y_2345_;
v___y_2329_ = v___y_2346_;
v___y_2330_ = v___x_2349_;
v___y_2331_ = v___x_2354_;
goto v___jp_2320_;
}
}
v___jp_2355_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = l_Array_append___redArg(v___x_2319_, v___y_2366_);
lean_dec_ref(v___y_2366_);
lean_inc(v___y_2364_);
v___x_2368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2368_, 0, v___y_2364_);
lean_ctor_set(v___x_2368_, 1, v___x_2318_);
lean_ctor_set(v___x_2368_, 2, v___x_2367_);
if (lean_obj_tag(v___y_2359_) == 1)
{
lean_object* v_val_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_val_2369_ = lean_ctor_get(v___y_2359_, 0);
lean_inc(v_val_2369_);
lean_dec_ref(v___y_2359_);
v___x_2370_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2371_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2370_);
v___x_2372_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___y_2364_, 4);
v___x_2373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___y_2364_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = l_Array_append___redArg(v___x_2319_, v_val_2369_);
lean_dec(v_val_2369_);
v___x_2375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2375_, 0, v___y_2364_);
lean_ctor_set(v___x_2375_, 1, v___x_2318_);
lean_ctor_set(v___x_2375_, 2, v___x_2374_);
v___x_2376_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2377_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___y_2364_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = l_Lean_Syntax_node3(v___y_2364_, v___x_2371_, v___x_2373_, v___x_2375_, v___x_2377_);
v___x_2379_ = l_Array_mkArray1___redArg(v___x_2378_);
v___y_2337_ = v___y_2356_;
v___y_2338_ = v___y_2357_;
v___y_2339_ = v___y_2358_;
v___y_2340_ = v___x_2368_;
v___y_2341_ = v___y_2360_;
v___y_2342_ = v___y_2362_;
v___y_2343_ = v___y_2361_;
v___y_2344_ = v___y_2363_;
v___y_2345_ = v___y_2364_;
v___y_2346_ = v___y_2365_;
v___y_2347_ = v___x_2379_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2380_; 
lean_dec(v___y_2359_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2380_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2337_ = v___y_2356_;
v___y_2338_ = v___y_2357_;
v___y_2339_ = v___y_2358_;
v___y_2340_ = v___x_2368_;
v___y_2341_ = v___y_2360_;
v___y_2342_ = v___y_2362_;
v___y_2343_ = v___y_2361_;
v___y_2344_ = v___y_2363_;
v___y_2345_ = v___y_2364_;
v___y_2346_ = v___y_2365_;
v___y_2347_ = v___x_2380_;
goto v___jp_2336_;
}
}
v___jp_2381_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = l_Array_append___redArg(v___x_2319_, v___y_2392_);
lean_dec_ref(v___y_2392_);
lean_inc(v___y_2391_);
v___x_2394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2391_);
lean_ctor_set(v___x_2394_, 1, v___x_2318_);
lean_ctor_set(v___x_2394_, 2, v___x_2393_);
if (lean_obj_tag(v___y_2384_) == 1)
{
lean_object* v_val_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_val_2395_ = lean_ctor_get(v___y_2384_, 0);
lean_inc(v_val_2395_);
lean_dec_ref(v___y_2384_);
v___x_2396_ = l_Lean_SourceInfo_fromRef(v_val_2395_, v___x_2251_);
lean_dec(v_val_2395_);
v___x_2397_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = l_Array_mkArray1___redArg(v___x_2398_);
v___y_2356_ = v___y_2382_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2385_;
v___y_2359_ = v___y_2387_;
v___y_2360_ = v___y_2386_;
v___y_2361_ = v___y_2389_;
v___y_2362_ = v___y_2388_;
v___y_2363_ = v___y_2390_;
v___y_2364_ = v___y_2391_;
v___y_2365_ = v___x_2394_;
v___y_2366_ = v___x_2399_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2400_; 
lean_dec(v___y_2384_);
v___x_2400_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2356_ = v___y_2382_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2385_;
v___y_2359_ = v___y_2387_;
v___y_2360_ = v___y_2386_;
v___y_2361_ = v___y_2389_;
v___y_2362_ = v___y_2388_;
v___y_2363_ = v___y_2390_;
v___y_2364_ = v___y_2391_;
v___y_2365_ = v___x_2394_;
v___y_2366_ = v___x_2400_;
goto v___jp_2355_;
}
}
v___jp_2401_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2413_ = l_Array_append___redArg(v___x_2319_, v___y_2412_);
lean_dec_ref(v___y_2412_);
lean_inc_n(v___y_2410_, 2);
v___x_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2414_, 0, v___y_2410_);
lean_ctor_set(v___x_2414_, 1, v___x_2318_);
lean_ctor_set(v___x_2414_, 2, v___x_2413_);
v___x_2415_ = l_Lean_Syntax_node5(v___y_2410_, v___x_2249_, v___y_2408_, v___y_2407_, v___y_2411_, v___y_2402_, v___x_2414_);
v___x_2416_ = l_Lean_Syntax_node2(v___y_2410_, v___y_2406_, v___y_2405_, v___x_2415_);
v___y_2306_ = v___y_2404_;
v_stx_2307_ = v___x_2416_;
v___y_2308_ = v___y_2403_;
v___y_2309_ = v___y_2409_;
goto v___jp_2305_;
}
v___jp_2417_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = l_Array_append___redArg(v___x_2319_, v___y_2428_);
lean_dec_ref(v___y_2428_);
lean_inc(v___y_2426_);
v___x_2430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2430_, 0, v___y_2426_);
lean_ctor_set(v___x_2430_, 1, v___x_2318_);
lean_ctor_set(v___x_2430_, 2, v___x_2429_);
if (lean_obj_tag(v___y_2418_) == 1)
{
lean_object* v_val_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec(v___x_2250_);
v_val_2431_ = lean_ctor_get(v___y_2418_, 0);
lean_inc(v_val_2431_);
lean_dec_ref(v___y_2418_);
v___x_2432_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2426_);
v___x_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___y_2426_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = l_Array_mkArray2___redArg(v___x_2433_, v_val_2431_);
v___y_2402_ = v___x_2430_;
v___y_2403_ = v___y_2419_;
v___y_2404_ = v___y_2420_;
v___y_2405_ = v___y_2421_;
v___y_2406_ = v___y_2422_;
v___y_2407_ = v___y_2424_;
v___y_2408_ = v___y_2423_;
v___y_2409_ = v___y_2425_;
v___y_2410_ = v___y_2426_;
v___y_2411_ = v___y_2427_;
v___y_2412_ = v___x_2434_;
goto v___jp_2401_;
}
else
{
lean_object* v___x_2435_; 
lean_dec(v___y_2418_);
v___x_2435_ = lean_mk_empty_array_with_capacity(v___x_2250_);
lean_dec(v___x_2250_);
v___y_2402_ = v___x_2430_;
v___y_2403_ = v___y_2419_;
v___y_2404_ = v___y_2420_;
v___y_2405_ = v___y_2421_;
v___y_2406_ = v___y_2422_;
v___y_2407_ = v___y_2424_;
v___y_2408_ = v___y_2423_;
v___y_2409_ = v___y_2425_;
v___y_2410_ = v___y_2426_;
v___y_2411_ = v___y_2427_;
v___y_2412_ = v___x_2435_;
goto v___jp_2401_;
}
}
v___jp_2436_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = l_Array_append___redArg(v___x_2319_, v___y_2447_);
lean_dec_ref(v___y_2447_);
lean_inc(v___y_2446_);
v___x_2449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2449_, 0, v___y_2446_);
lean_ctor_set(v___x_2449_, 1, v___x_2318_);
lean_ctor_set(v___x_2449_, 2, v___x_2448_);
if (lean_obj_tag(v___y_2442_) == 1)
{
lean_object* v_val_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_val_2450_ = lean_ctor_get(v___y_2442_, 0);
lean_inc(v_val_2450_);
lean_dec_ref(v___y_2442_);
v___x_2451_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2452_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2451_);
v___x_2453_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___y_2446_, 4);
v___x_2454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2446_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l_Array_append___redArg(v___x_2319_, v_val_2450_);
lean_dec(v_val_2450_);
v___x_2456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2456_, 0, v___y_2446_);
lean_ctor_set(v___x_2456_, 1, v___x_2318_);
lean_ctor_set(v___x_2456_, 2, v___x_2455_);
v___x_2457_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___y_2446_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = l_Lean_Syntax_node3(v___y_2446_, v___x_2452_, v___x_2454_, v___x_2456_, v___x_2458_);
v___x_2460_ = l_Array_mkArray1___redArg(v___x_2459_);
v___y_2418_ = v___y_2437_;
v___y_2419_ = v___y_2438_;
v___y_2420_ = v___y_2439_;
v___y_2421_ = v___y_2440_;
v___y_2422_ = v___y_2441_;
v___y_2423_ = v___y_2444_;
v___y_2424_ = v___y_2443_;
v___y_2425_ = v___y_2445_;
v___y_2426_ = v___y_2446_;
v___y_2427_ = v___x_2449_;
v___y_2428_ = v___x_2460_;
goto v___jp_2417_;
}
else
{
lean_object* v___x_2461_; 
lean_dec(v___y_2442_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2461_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2418_ = v___y_2437_;
v___y_2419_ = v___y_2438_;
v___y_2420_ = v___y_2439_;
v___y_2421_ = v___y_2440_;
v___y_2422_ = v___y_2441_;
v___y_2423_ = v___y_2444_;
v___y_2424_ = v___y_2443_;
v___y_2425_ = v___y_2445_;
v___y_2426_ = v___y_2446_;
v___y_2427_ = v___x_2449_;
v___y_2428_ = v___x_2461_;
goto v___jp_2417_;
}
}
v___jp_2462_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = l_Array_append___redArg(v___x_2319_, v___y_2473_);
lean_dec_ref(v___y_2473_);
lean_inc(v___y_2472_);
v___x_2475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2475_, 0, v___y_2472_);
lean_ctor_set(v___x_2475_, 1, v___x_2318_);
lean_ctor_set(v___x_2475_, 2, v___x_2474_);
if (lean_obj_tag(v___y_2465_) == 1)
{
lean_object* v_val_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_val_2476_ = lean_ctor_get(v___y_2465_, 0);
lean_inc(v_val_2476_);
lean_dec_ref(v___y_2465_);
v___x_2477_ = l_Lean_SourceInfo_fromRef(v_val_2476_, v___x_2251_);
lean_dec(v_val_2476_);
v___x_2478_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Array_mkArray1___redArg(v___x_2479_);
v___y_2437_ = v___y_2463_;
v___y_2438_ = v___y_2464_;
v___y_2439_ = v___y_2466_;
v___y_2440_ = v___y_2467_;
v___y_2441_ = v___y_2468_;
v___y_2442_ = v___y_2470_;
v___y_2443_ = v___x_2475_;
v___y_2444_ = v___y_2469_;
v___y_2445_ = v___y_2471_;
v___y_2446_ = v___y_2472_;
v___y_2447_ = v___x_2480_;
goto v___jp_2436_;
}
else
{
lean_object* v___x_2481_; 
lean_dec(v___y_2465_);
v___x_2481_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2437_ = v___y_2463_;
v___y_2438_ = v___y_2464_;
v___y_2439_ = v___y_2466_;
v___y_2440_ = v___y_2467_;
v___y_2441_ = v___y_2468_;
v___y_2442_ = v___y_2470_;
v___y_2443_ = v___x_2475_;
v___y_2444_ = v___y_2469_;
v___y_2445_ = v___y_2471_;
v___y_2446_ = v___y_2472_;
v___y_2447_ = v___x_2481_;
goto v___jp_2436_;
}
}
v___jp_2482_:
{
if (v___y_2484_ == 0)
{
lean_object* v___x_2498_; 
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2485_);
v___x_2498_ = lean_apply_9(v___f_2253_, v___y_2489_, v___y_2494_, v___y_2496_, v___y_2495_, v___y_2492_, v___y_2486_, v___y_2485_, v___y_2493_, lean_box(0));
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc_n(v_a_2499_, 3);
lean_dec_ref(v___x_2498_);
v___x_2500_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2499_);
lean_ctor_set(v___x_2500_, 1, v___x_2254_);
v___x_2501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2318_);
lean_ctor_set(v___x_2501_, 2, v___x_2319_);
if (lean_obj_tag(v___y_2497_) == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2382_ = v___y_2483_;
v___y_2383_ = v___y_2485_;
v___y_2384_ = v___y_2487_;
v___y_2385_ = v___y_2488_;
v___y_2386_ = v___y_2491_;
v___y_2387_ = v___y_2490_;
v___y_2388_ = v___x_2501_;
v___y_2389_ = v___y_2493_;
v___y_2390_ = v___x_2500_;
v___y_2391_ = v_a_2499_;
v___y_2392_ = v___x_2502_;
goto v___jp_2381_;
}
else
{
lean_object* v_val_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_val_2503_ = lean_ctor_get(v___y_2497_, 0);
lean_inc(v_val_2503_);
lean_dec_ref(v___y_2497_);
v___x_2504_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2505_ = lean_array_push(v___x_2504_, v_val_2503_);
v___y_2382_ = v___y_2483_;
v___y_2383_ = v___y_2485_;
v___y_2384_ = v___y_2487_;
v___y_2385_ = v___y_2488_;
v___y_2386_ = v___y_2491_;
v___y_2387_ = v___y_2490_;
v___y_2388_ = v___x_2501_;
v___y_2389_ = v___y_2493_;
v___y_2390_ = v___x_2500_;
v___y_2391_ = v_a_2499_;
v___y_2392_ = v___x_2505_;
goto v___jp_2381_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v___y_2497_);
lean_dec(v___y_2493_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2483_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v_a_2506_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2498_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2498_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v___x_2514_; 
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2252_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2485_);
v___x_2514_ = lean_apply_9(v___f_2253_, v___y_2489_, v___y_2494_, v___y_2496_, v___y_2495_, v___y_2492_, v___y_2486_, v___y_2485_, v___y_2493_, lean_box(0));
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc_n(v_a_2515_, 2);
lean_dec_ref(v___x_2514_);
v___x_2516_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12));
lean_inc_ref(v___x_2248_);
lean_inc_ref(v___x_2247_);
lean_inc_ref(v___x_2246_);
v___x_2517_ = l_Lean_Name_mkStr4(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2516_);
v___x_2518_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13));
v___x_2519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2519_, 0, v_a_2515_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
if (lean_obj_tag(v___y_2497_) == 0)
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2485_;
v___y_2465_ = v___y_2487_;
v___y_2466_ = v___y_2488_;
v___y_2467_ = v___x_2519_;
v___y_2468_ = v___x_2517_;
v___y_2469_ = v___y_2491_;
v___y_2470_ = v___y_2490_;
v___y_2471_ = v___y_2493_;
v___y_2472_ = v_a_2515_;
v___y_2473_ = v___x_2520_;
goto v___jp_2462_;
}
else
{
lean_object* v_val_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_val_2521_ = lean_ctor_get(v___y_2497_, 0);
lean_inc(v_val_2521_);
lean_dec_ref(v___y_2497_);
v___x_2522_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2523_ = lean_array_push(v___x_2522_, v_val_2521_);
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2485_;
v___y_2465_ = v___y_2487_;
v___y_2466_ = v___y_2488_;
v___y_2467_ = v___x_2519_;
v___y_2468_ = v___x_2517_;
v___y_2469_ = v___y_2491_;
v___y_2470_ = v___y_2490_;
v___y_2471_ = v___y_2493_;
v___y_2472_ = v_a_2515_;
v___y_2473_ = v___x_2523_;
goto v___jp_2462_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v___y_2497_);
lean_dec(v___y_2493_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2483_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
lean_dec(v_tk_2245_);
v_a_2524_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2514_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2514_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
v___jp_2532_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2549_ = lean_unsigned_to_nat(5u);
v___x_2550_ = l_Lean_Syntax_getArg(v___y_2539_, v___x_2549_);
lean_dec(v___y_2539_);
v___x_2551_ = l_Lean_Syntax_matchesNull(v___x_2550_, v___x_2250_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_args_2540_);
lean_dec(v___y_2538_);
lean_dec(v___y_2536_);
lean_dec(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2552_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2553_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2552_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref(v___x_2553_);
v___y_2306_ = v___y_2537_;
v_stx_2307_ = v_a_2554_;
v___y_2308_ = v___y_2547_;
v___y_2309_ = v___y_2548_;
goto v___jp_2305_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec_ref(v___y_2537_);
lean_dec(v_tk_2245_);
v_a_2555_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2553_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2553_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Syntax_getOptional_x3f(v___y_2533_);
lean_dec(v___y_2533_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_box(0);
v___y_2483_ = v___y_2534_;
v___y_2484_ = v___y_2535_;
v___y_2485_ = v___y_2547_;
v___y_2486_ = v___y_2546_;
v___y_2487_ = v___y_2536_;
v___y_2488_ = v___y_2537_;
v___y_2489_ = v___y_2541_;
v___y_2490_ = v_args_2540_;
v___y_2491_ = v___y_2538_;
v___y_2492_ = v___y_2545_;
v___y_2493_ = v___y_2548_;
v___y_2494_ = v___y_2542_;
v___y_2495_ = v___y_2544_;
v___y_2496_ = v___y_2543_;
v___y_2497_ = v___x_2564_;
goto v___jp_2482_;
}
else
{
lean_object* v_val_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_val_2565_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2563_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_val_2565_);
lean_dec(v___x_2563_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_val_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
v___y_2483_ = v___y_2534_;
v___y_2484_ = v___y_2535_;
v___y_2485_ = v___y_2547_;
v___y_2486_ = v___y_2546_;
v___y_2487_ = v___y_2536_;
v___y_2488_ = v___y_2537_;
v___y_2489_ = v___y_2541_;
v___y_2490_ = v_args_2540_;
v___y_2491_ = v___y_2538_;
v___y_2492_ = v___y_2545_;
v___y_2493_ = v___y_2548_;
v___y_2494_ = v___y_2542_;
v___y_2495_ = v___y_2544_;
v___y_2496_ = v___y_2543_;
v___y_2497_ = v___x_2570_;
goto v___jp_2482_;
}
}
}
}
}
v___jp_2573_:
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = l_Lean_Syntax_getArg(v___y_2579_, v___x_2255_);
v___x_2590_ = l_Lean_Syntax_isNone(v___x_2589_);
if (v___x_2590_ == 0)
{
uint8_t v___x_2591_; 
lean_inc(v___x_2589_);
v___x_2591_ = l_Lean_Syntax_matchesNull(v___x_2589_, v___x_2256_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
lean_dec(v___x_2589_);
lean_dec(v_only_2580_);
lean_dec(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec(v___y_2575_);
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
v___x_2592_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2593_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2592_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v___y_2306_ = v___y_2577_;
v_stx_2307_ = v_a_2594_;
v___y_2308_ = v___y_2587_;
v___y_2309_ = v___y_2588_;
goto v___jp_2305_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec_ref(v___y_2577_);
lean_dec(v_tk_2245_);
v_a_2595_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2593_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2593_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = l_Lean_Syntax_getArg(v___x_2589_, v___x_2257_);
lean_dec(v___x_2257_);
lean_dec(v___x_2589_);
v___x_2604_ = l_Lean_Syntax_getArgs(v___x_2603_);
lean_dec(v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
v___y_2533_ = v___y_2575_;
v___y_2534_ = v___y_2574_;
v___y_2535_ = v___y_2576_;
v___y_2536_ = v_only_2580_;
v___y_2537_ = v___y_2577_;
v___y_2538_ = v___y_2578_;
v___y_2539_ = v___y_2579_;
v_args_2540_ = v___x_2605_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2584_;
v___y_2545_ = v___y_2585_;
v___y_2546_ = v___y_2586_;
v___y_2547_ = v___y_2587_;
v___y_2548_ = v___y_2588_;
goto v___jp_2532_;
}
}
else
{
lean_object* v___x_2606_; 
lean_dec(v___x_2589_);
lean_dec(v___x_2257_);
v___x_2606_ = lean_box(0);
v___y_2533_ = v___y_2575_;
v___y_2534_ = v___y_2574_;
v___y_2535_ = v___y_2576_;
v___y_2536_ = v_only_2580_;
v___y_2537_ = v___y_2577_;
v___y_2538_ = v___y_2578_;
v___y_2539_ = v___y_2579_;
v_args_2540_ = v___x_2606_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
v___y_2544_ = v___y_2584_;
v___y_2545_ = v___y_2585_;
v___y_2546_ = v___y_2586_;
v___y_2547_ = v___y_2587_;
v___y_2548_ = v___y_2588_;
goto v___jp_2532_;
}
}
v___jp_2607_:
{
lean_object* v_usedTheorems_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_usedTheorems_2612_ = lean_ctor_get(v___y_2609_, 0);
v___x_2613_ = l_Lean_Syntax_unsetTrailing(v___y_2610_);
v___x_2614_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2613_, v_usedTheorems_2612_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; uint8_t v___x_2616_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc_n(v_a_2615_, 2);
lean_dec_ref(v___x_2614_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v_a_2615_, v___x_2316_);
lean_dec(v___x_2316_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_inc(v_ref_2312_);
lean_dec(v_a_2615_);
lean_dec(v___y_2611_);
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
v___x_2617_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2618_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2617_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref(v___x_2618_);
v___y_2283_ = v___y_2609_;
v_stx_2284_ = v_a_2619_;
v___y_2285_ = v___y_2275_;
v_ref_2286_ = v_ref_2312_;
v___y_2287_ = v___y_2276_;
goto v___jp_2282_;
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v___y_2609_);
lean_dec(v_ref_2312_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_tk_2245_);
v_a_2620_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2618_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2618_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
else
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = l_Lean_Syntax_getArg(v_a_2615_, v___x_2257_);
lean_inc(v___x_2628_);
v___x_2629_ = l_Lean_Syntax_isOfKind(v___x_2628_, v___x_2258_);
if (v___x_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_inc(v_ref_2312_);
lean_dec(v___x_2628_);
lean_dec(v_a_2615_);
lean_dec(v___y_2611_);
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
v___x_2630_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2631_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2630_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref(v___x_2631_);
v___y_2283_ = v___y_2609_;
v_stx_2284_ = v_a_2632_;
v___y_2285_ = v___y_2275_;
v_ref_2286_ = v_ref_2312_;
v___y_2287_ = v___y_2276_;
goto v___jp_2282_;
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v___y_2609_);
lean_dec(v_ref_2312_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_tk_2245_);
v_a_2633_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2631_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2631_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2641_ = l_Lean_Syntax_getArg(v_a_2615_, v___x_2259_);
lean_dec(v___x_2259_);
v___x_2642_ = l_Lean_Syntax_getArg(v_a_2615_, v___x_2256_);
v___x_2643_ = l_Lean_Syntax_isNone(v___x_2642_);
if (v___x_2643_ == 0)
{
uint8_t v___x_2644_; 
lean_inc(v___x_2642_);
v___x_2644_ = l_Lean_Syntax_matchesNull(v___x_2642_, v___x_2257_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_inc(v_ref_2312_);
lean_dec(v___x_2642_);
lean_dec(v___x_2641_);
lean_dec(v___x_2628_);
lean_dec(v_a_2615_);
lean_dec(v___y_2611_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec_ref(v___f_2253_);
lean_dec(v___x_2252_);
lean_dec(v___x_2250_);
lean_dec(v___x_2249_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v___x_2247_);
lean_dec_ref(v___x_2246_);
v___x_2645_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2646_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2645_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref(v___x_2646_);
v___y_2283_ = v___y_2609_;
v_stx_2284_ = v_a_2647_;
v___y_2285_ = v___y_2275_;
v_ref_2286_ = v_ref_2312_;
v___y_2287_ = v___y_2276_;
goto v___jp_2282_;
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec_ref(v___y_2609_);
lean_dec(v_ref_2312_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_tk_2245_);
v_a_2648_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2646_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2646_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = l_Lean_Syntax_getArg(v___x_2642_, v___x_2250_);
lean_dec(v___x_2642_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
v___y_2574_ = v___y_2611_;
v___y_2575_ = v___x_2641_;
v___y_2576_ = v___y_2608_;
v___y_2577_ = v___y_2609_;
v___y_2578_ = v___x_2628_;
v___y_2579_ = v_a_2615_;
v_only_2580_ = v___x_2657_;
v___y_2581_ = v___y_2269_;
v___y_2582_ = v___y_2270_;
v___y_2583_ = v___y_2271_;
v___y_2584_ = v___y_2272_;
v___y_2585_ = v___y_2273_;
v___y_2586_ = v___y_2274_;
v___y_2587_ = v___y_2275_;
v___y_2588_ = v___y_2276_;
goto v___jp_2573_;
}
}
else
{
lean_object* v___x_2658_; 
lean_dec(v___x_2642_);
v___x_2658_ = lean_box(0);
v___y_2574_ = v___y_2611_;
v___y_2575_ = v___x_2641_;
v___y_2576_ = v___y_2608_;
v___y_2577_ = v___y_2609_;
v___y_2578_ = v___x_2628_;
v___y_2579_ = v_a_2615_;
v_only_2580_ = v___x_2658_;
v___y_2581_ = v___y_2269_;
v___y_2582_ = v___y_2270_;
v___y_2583_ = v___y_2271_;
v___y_2584_ = v___y_2272_;
v___y_2585_ = v___y_2273_;
v___y_2586_ = v___y_2274_;
v___y_2587_ = v___y_2275_;
v___y_2588_ = v___y_2276_;
goto v___jp_2573_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2609_);
lean_dec(v___x_2316_);
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
v_a_2659_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2614_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2614_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
v___jp_2667_:
{
if (lean_obj_tag(v_usingArg_2260_) == 0)
{
v___y_2608_ = v___y_2668_;
v___y_2609_ = v___y_2669_;
v___y_2610_ = v___y_2670_;
v___y_2611_ = v_usingArg_2260_;
goto v___jp_2607_;
}
else
{
lean_object* v_val_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2679_; 
v_val_2671_ = lean_ctor_get(v_usingArg_2260_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_usingArg_2260_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2673_ = v_usingArg_2260_;
v_isShared_2674_ = v_isSharedCheck_2679_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_val_2671_);
lean_dec(v_usingArg_2260_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2679_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2675_ = l_Lean_Syntax_unsetTrailing(v_val_2671_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 0, v___x_2675_);
v___x_2677_ = v___x_2673_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
v___y_2608_ = v___y_2668_;
v___y_2609_ = v___y_2669_;
v___y_2610_ = v___y_2670_;
v___y_2611_ = v___x_2677_;
goto v___jp_2607_;
}
}
}
}
v___jp_2680_:
{
if (v___y_2684_ == 0)
{
lean_dec(v___y_2683_);
lean_dec(v___x_2316_);
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
v___y_2279_ = v___y_2682_;
goto v___jp_2278_;
}
else
{
v___y_2668_ = v___y_2681_;
v___y_2669_ = v___y_2682_;
v___y_2670_ = v___y_2683_;
goto v___jp_2667_;
}
}
v___jp_2685_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; 
v___x_2691_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_2690_, v___x_2313_);
v___x_2692_ = lean_box(v___x_2251_);
v___x_2693_ = lean_box(v___x_2313_);
v___x_2694_ = lean_box(v___x_2262_);
lean_inc(v___x_2257_);
lean_inc_ref(v___x_2254_);
lean_inc(v_usingArg_2260_);
lean_inc(v___x_2250_);
lean_inc(v_tk_2245_);
lean_inc(v___x_2259_);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 23, 13);
lean_closure_set(v___f_2695_, 0, v___x_2259_);
lean_closure_set(v___f_2695_, 1, v_tk_2245_);
lean_closure_set(v___f_2695_, 2, v___x_2318_);
lean_closure_set(v___f_2695_, 3, v___x_2250_);
lean_closure_set(v___f_2695_, 4, v___x_2691_);
lean_closure_set(v___f_2695_, 5, v___y_2686_);
lean_closure_set(v___f_2695_, 6, v___x_2692_);
lean_closure_set(v___f_2695_, 7, v_usingArg_2260_);
lean_closure_set(v___f_2695_, 8, v___x_2693_);
lean_closure_set(v___f_2695_, 9, v___x_2694_);
lean_closure_set(v___f_2695_, 10, v___x_2254_);
lean_closure_set(v___f_2695_, 11, v___x_2257_);
lean_closure_set(v___f_2695_, 12, v_usingTk_x3f_2263_);
v___x_2696_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_2688_, v___f_2695_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2688_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_2699_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_2311_, v___x_2698_);
if (v___x_2699_ == 0)
{
if (lean_obj_tag(v_squeeze_2264_) == 0)
{
v___y_2681_ = v___y_2687_;
v___y_2682_ = v_a_2697_;
v___y_2683_ = v___y_2689_;
v___y_2684_ = v___x_2699_;
goto v___jp_2680_;
}
else
{
v___y_2681_ = v___y_2687_;
v___y_2682_ = v_a_2697_;
v___y_2683_ = v___y_2689_;
v___y_2684_ = v___x_2262_;
goto v___jp_2680_;
}
}
else
{
v___y_2668_ = v___y_2687_;
v___y_2669_ = v_a_2697_;
v___y_2670_ = v___y_2689_;
goto v___jp_2667_;
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v___y_2689_);
lean_dec(v___x_2316_);
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
v_a_2700_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2696_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2696_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
v___jp_2708_:
{
v___y_2686_ = v___y_2709_;
v___y_2687_ = v___x_2313_;
v___y_2688_ = v___y_2711_;
v___y_2689_ = v___y_2712_;
v___y_2690_ = v___y_2710_;
goto v___jp_2685_;
}
v___jp_2713_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2717_ = l_Array_append___redArg(v___x_2319_, v___y_2716_);
lean_dec_ref(v___y_2716_);
lean_inc_n(v___x_2314_, 2);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2314_);
lean_ctor_set(v___x_2718_, 1, v___x_2318_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2314_);
lean_ctor_set(v___x_2719_, 1, v___x_2318_);
lean_ctor_set(v___x_2719_, 2, v___x_2319_);
lean_inc(v___x_2316_);
v___x_2720_ = l_Lean_Syntax_node6(v___x_2314_, v___x_2316_, v___x_2317_, v___x_2261_, v___y_2714_, v___y_2715_, v___x_2718_, v___x_2719_);
v___x_2721_ = 0;
v___x_2722_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18));
v___x_2723_ = lean_box(v___x_2313_);
v___x_2724_ = lean_box(v___x_2721_);
v___x_2725_ = lean_box(v___x_2313_);
lean_inc(v___x_2720_);
v___x_2726_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_2726_, 0, v___x_2720_);
lean_closure_set(v___x_2726_, 1, v___x_2723_);
lean_closure_set(v___x_2726_, 2, v___x_2724_);
lean_closure_set(v___x_2726_, 3, v___x_2725_);
lean_closure_set(v___x_2726_, 4, v___x_2722_);
v___x_2727_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2726_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref(v___x_2727_);
if (lean_obj_tag(v_unfold_2265_) == 0)
{
lean_object* v_ctx_2729_; lean_object* v_simprocs_2730_; lean_object* v_dischargeWrapper_2731_; 
v_ctx_2729_ = lean_ctor_get(v_a_2728_, 0);
lean_inc_ref(v_ctx_2729_);
v_simprocs_2730_ = lean_ctor_get(v_a_2728_, 1);
lean_inc_ref(v_simprocs_2730_);
v_dischargeWrapper_2731_ = lean_ctor_get(v_a_2728_, 2);
lean_inc(v_dischargeWrapper_2731_);
lean_dec(v_a_2728_);
v___y_2709_ = v_simprocs_2730_;
v___y_2710_ = v_ctx_2729_;
v___y_2711_ = v_dischargeWrapper_2731_;
v___y_2712_ = v___x_2720_;
goto v___jp_2708_;
}
else
{
if (v___x_2262_ == 0)
{
lean_object* v_ctx_2732_; lean_object* v_simprocs_2733_; lean_object* v_dischargeWrapper_2734_; 
v_ctx_2732_ = lean_ctor_get(v_a_2728_, 0);
lean_inc_ref(v_ctx_2732_);
v_simprocs_2733_ = lean_ctor_get(v_a_2728_, 1);
lean_inc_ref(v_simprocs_2733_);
v_dischargeWrapper_2734_ = lean_ctor_get(v_a_2728_, 2);
lean_inc(v_dischargeWrapper_2734_);
lean_dec(v_a_2728_);
v___y_2709_ = v_simprocs_2733_;
v___y_2710_ = v_ctx_2732_;
v___y_2711_ = v_dischargeWrapper_2734_;
v___y_2712_ = v___x_2720_;
goto v___jp_2708_;
}
else
{
lean_object* v_ctx_2735_; lean_object* v_simprocs_2736_; lean_object* v_dischargeWrapper_2737_; lean_object* v___x_2738_; 
v_ctx_2735_ = lean_ctor_get(v_a_2728_, 0);
lean_inc_ref(v_ctx_2735_);
v_simprocs_2736_ = lean_ctor_get(v_a_2728_, 1);
lean_inc_ref(v_simprocs_2736_);
v_dischargeWrapper_2737_ = lean_ctor_get(v_a_2728_, 2);
lean_inc(v_dischargeWrapper_2737_);
lean_dec(v_a_2728_);
v___x_2738_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2735_);
v___y_2686_ = v_simprocs_2736_;
v___y_2687_ = v___x_2262_;
v___y_2688_ = v_dischargeWrapper_2737_;
v___y_2689_ = v___x_2720_;
v___y_2690_ = v___x_2738_;
goto v___jp_2685_;
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v___x_2720_);
lean_dec(v___x_2316_);
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
v_a_2739_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2727_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2727_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
v___jp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = l_Array_append___redArg(v___x_2319_, v___y_2749_);
lean_dec_ref(v___y_2749_);
lean_inc(v___x_2314_);
v___x_2751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2314_);
lean_ctor_set(v___x_2751_, 1, v___x_2318_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
if (lean_obj_tag(v_args_2266_) == 1)
{
lean_object* v_val_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_val_2752_ = lean_ctor_get(v_args_2266_, 0);
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___x_2314_, 3);
v___x_2754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2314_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Array_append___redArg(v___x_2319_, v_val_2752_);
v___x_2756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2314_);
lean_ctor_set(v___x_2756_, 1, v___x_2318_);
lean_ctor_set(v___x_2756_, 2, v___x_2755_);
v___x_2757_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2314_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = l_Array_mkArray3___redArg(v___x_2754_, v___x_2756_, v___x_2758_);
v___y_2714_ = v___y_2748_;
v___y_2715_ = v___x_2751_;
v___y_2716_ = v___x_2759_;
goto v___jp_2713_;
}
else
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2714_ = v___y_2748_;
v___y_2715_ = v___x_2751_;
v___y_2716_ = v___x_2760_;
goto v___jp_2713_;
}
}
v___jp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = l_Array_append___redArg(v___x_2319_, v___y_2762_);
lean_dec_ref(v___y_2762_);
lean_inc(v___x_2314_);
v___x_2764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2314_);
lean_ctor_set(v___x_2764_, 1, v___x_2318_);
lean_ctor_set(v___x_2764_, 2, v___x_2763_);
if (lean_obj_tag(v_only_2267_) == 1)
{
lean_object* v_val_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_val_2765_ = lean_ctor_get(v_only_2267_, 0);
v___x_2766_ = l_Lean_SourceInfo_fromRef(v_val_2765_, v___x_2251_);
v___x_2767_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_Array_mkArray1___redArg(v___x_2768_);
v___y_2748_ = v___x_2764_;
v___y_2749_ = v___x_2769_;
goto v___jp_2747_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___y_2748_ = v___x_2764_;
v___y_2749_ = v___x_2770_;
goto v___jp_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object** _args){
lean_object* v_tk_2775_ = _args[0];
lean_object* v___x_2776_ = _args[1];
lean_object* v___x_2777_ = _args[2];
lean_object* v___x_2778_ = _args[3];
lean_object* v___x_2779_ = _args[4];
lean_object* v___x_2780_ = _args[5];
lean_object* v___x_2781_ = _args[6];
lean_object* v___x_2782_ = _args[7];
lean_object* v___f_2783_ = _args[8];
lean_object* v___x_2784_ = _args[9];
lean_object* v___x_2785_ = _args[10];
lean_object* v___x_2786_ = _args[11];
lean_object* v___x_2787_ = _args[12];
lean_object* v___x_2788_ = _args[13];
lean_object* v___x_2789_ = _args[14];
lean_object* v_usingArg_2790_ = _args[15];
lean_object* v___x_2791_ = _args[16];
lean_object* v___x_2792_ = _args[17];
lean_object* v_usingTk_x3f_2793_ = _args[18];
lean_object* v_squeeze_2794_ = _args[19];
lean_object* v_unfold_2795_ = _args[20];
lean_object* v_args_2796_ = _args[21];
lean_object* v_only_2797_ = _args[22];
lean_object* v___y_2798_ = _args[23];
lean_object* v___y_2799_ = _args[24];
lean_object* v___y_2800_ = _args[25];
lean_object* v___y_2801_ = _args[26];
lean_object* v___y_2802_ = _args[27];
lean_object* v___y_2803_ = _args[28];
lean_object* v___y_2804_ = _args[29];
lean_object* v___y_2805_ = _args[30];
lean_object* v___y_2806_ = _args[31];
lean_object* v___y_2807_ = _args[32];
_start:
{
uint8_t v___x_82185__boxed_2808_; uint8_t v___x_82195__boxed_2809_; lean_object* v_res_2810_; 
v___x_82185__boxed_2808_ = lean_unbox(v___x_2781_);
v___x_82195__boxed_2809_ = lean_unbox(v___x_2792_);
v_res_2810_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(v_tk_2775_, v___x_2776_, v___x_2777_, v___x_2778_, v___x_2779_, v___x_2780_, v___x_82185__boxed_2808_, v___x_2782_, v___f_2783_, v___x_2784_, v___x_2785_, v___x_2786_, v___x_2787_, v___x_2788_, v___x_2789_, v_usingArg_2790_, v___x_2791_, v___x_82195__boxed_2809_, v_usingTk_x3f_2793_, v_squeeze_2794_, v_unfold_2795_, v_args_2796_, v_only_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v_only_2797_);
lean_dec(v_args_2796_);
lean_dec(v_unfold_2795_);
lean_dec(v_squeeze_2794_);
lean_dec(v___x_2788_);
lean_dec(v___x_2786_);
lean_dec(v___x_2785_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_stx_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2847_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0));
v___x_2848_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1));
v___x_2849_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_2850_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2));
v___x_2851_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
lean_inc(v_stx_2837_);
v___x_2852_ = l_Lean_Syntax_isOfKind(v_stx_2837_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_dec(v_stx_2837_);
v___x_2853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2853_;
}
else
{
lean_object* v___f_2854_; lean_object* v___x_2855_; lean_object* v_tk_2856_; lean_object* v___x_2857_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; uint8_t v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; uint8_t v___y_2906_; lean_object* v_usingTk_x3f_2907_; lean_object* v_usingArg_2908_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; uint8_t v___y_2939_; lean_object* v_args_2940_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; uint8_t v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v_only_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v_unfold_2996_; lean_object* v_squeeze_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___f_2854_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4));
v___x_2855_ = lean_unsigned_to_nat(0u);
v_tk_2856_ = l_Lean_Syntax_getArg(v_stx_2837_, v___x_2855_);
v___x_2857_ = lean_unsigned_to_nat(1u);
v___x_3032_ = l_Lean_Syntax_getArg(v_stx_2837_, v___x_2857_);
v___x_3033_ = l_Lean_Syntax_isNone(v___x_3032_);
if (v___x_3033_ == 0)
{
uint8_t v___x_3034_; 
lean_inc(v___x_3032_);
v___x_3034_ = l_Lean_Syntax_matchesNull(v___x_3032_, v___x_2857_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
lean_dec(v___x_3032_);
lean_dec(v_tk_2856_);
lean_dec(v_stx_2837_);
v___x_3035_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3035_;
}
else
{
lean_object* v_squeeze_3036_; lean_object* v___x_3037_; 
v_squeeze_3036_ = l_Lean_Syntax_getArg(v___x_3032_, v___x_2855_);
lean_dec(v___x_3032_);
v___x_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3037_, 0, v_squeeze_3036_);
v_squeeze_3015_ = v___x_3037_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
v___y_3019_ = v_a_2841_;
v___y_3020_ = v_a_2842_;
v___y_3021_ = v_a_2843_;
v___y_3022_ = v_a_2844_;
v___y_3023_ = v_a_2845_;
goto v___jp_3014_;
}
}
else
{
lean_object* v___x_3038_; 
lean_dec(v___x_3032_);
v___x_3038_ = lean_box(0);
v_squeeze_3015_ = v___x_3038_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
v___y_3019_ = v_a_2841_;
v___y_3020_ = v_a_2842_;
v___y_3021_ = v_a_2843_;
v___y_3022_ = v_a_2844_;
v___y_3023_ = v_a_2845_;
goto v___jp_3014_;
}
v___jp_2858_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2881_ = lean_box(v___x_2852_);
v___x_2882_ = lean_box(v___y_2879_);
lean_inc(v___y_2874_);
lean_inc(v___y_2866_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 33, 24);
lean_closure_set(v___f_2883_, 0, v_tk_2856_);
lean_closure_set(v___f_2883_, 1, v___x_2847_);
lean_closure_set(v___f_2883_, 2, v___x_2848_);
lean_closure_set(v___f_2883_, 3, v___x_2849_);
lean_closure_set(v___f_2883_, 4, v___y_2866_);
lean_closure_set(v___f_2883_, 5, v___x_2855_);
lean_closure_set(v___f_2883_, 6, v___x_2881_);
lean_closure_set(v___f_2883_, 7, v___x_2851_);
lean_closure_set(v___f_2883_, 8, v___f_2854_);
lean_closure_set(v___f_2883_, 9, v___x_2850_);
lean_closure_set(v___f_2883_, 10, v___y_2870_);
lean_closure_set(v___f_2883_, 11, v___y_2877_);
lean_closure_set(v___f_2883_, 12, v___x_2857_);
lean_closure_set(v___f_2883_, 13, v___y_2874_);
lean_closure_set(v___f_2883_, 14, v___y_2869_);
lean_closure_set(v___f_2883_, 15, v___y_2878_);
lean_closure_set(v___f_2883_, 16, v___y_2876_);
lean_closure_set(v___f_2883_, 17, v___x_2882_);
lean_closure_set(v___f_2883_, 18, v___y_2860_);
lean_closure_set(v___f_2883_, 19, v___y_2872_);
lean_closure_set(v___f_2883_, 20, v___y_2864_);
lean_closure_set(v___f_2883_, 21, v___y_2873_);
lean_closure_set(v___f_2883_, 22, v___y_2867_);
lean_closure_set(v___f_2883_, 23, v___y_2880_);
v___x_2884_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2884_, 0, v___f_2883_);
v___x_2885_ = l_Lean_Elab_Tactic_focus___redArg(v___x_2884_, v___y_2865_, v___y_2868_, v___y_2863_, v___y_2859_, v___y_2862_, v___y_2875_, v___y_2871_, v___y_2861_);
return v___x_2885_;
}
v___jp_2886_:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_Syntax_getOptional_x3f(v___y_2888_);
lean_dec(v___y_2888_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_box(0);
v___y_2859_ = v___y_2887_;
v___y_2860_ = v_usingTk_x3f_2907_;
v___y_2861_ = v___y_2889_;
v___y_2862_ = v___y_2890_;
v___y_2863_ = v___y_2891_;
v___y_2864_ = v___y_2892_;
v___y_2865_ = v___y_2893_;
v___y_2866_ = v___y_2894_;
v___y_2867_ = v___y_2895_;
v___y_2868_ = v___y_2896_;
v___y_2869_ = v___y_2897_;
v___y_2870_ = v___y_2898_;
v___y_2871_ = v___y_2899_;
v___y_2872_ = v___y_2900_;
v___y_2873_ = v___y_2901_;
v___y_2874_ = v___y_2902_;
v___y_2875_ = v___y_2903_;
v___y_2876_ = v___y_2904_;
v___y_2877_ = v___y_2905_;
v___y_2878_ = v_usingArg_2908_;
v___y_2879_ = v___y_2906_;
v___y_2880_ = v___x_2910_;
goto v___jp_2858_;
}
else
{
lean_object* v_val_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v_val_2911_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2909_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_val_2911_);
lean_dec(v___x_2909_);
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
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_val_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
v___y_2859_ = v___y_2887_;
v___y_2860_ = v_usingTk_x3f_2907_;
v___y_2861_ = v___y_2889_;
v___y_2862_ = v___y_2890_;
v___y_2863_ = v___y_2891_;
v___y_2864_ = v___y_2892_;
v___y_2865_ = v___y_2893_;
v___y_2866_ = v___y_2894_;
v___y_2867_ = v___y_2895_;
v___y_2868_ = v___y_2896_;
v___y_2869_ = v___y_2897_;
v___y_2870_ = v___y_2898_;
v___y_2871_ = v___y_2899_;
v___y_2872_ = v___y_2900_;
v___y_2873_ = v___y_2901_;
v___y_2874_ = v___y_2902_;
v___y_2875_ = v___y_2903_;
v___y_2876_ = v___y_2904_;
v___y_2877_ = v___y_2905_;
v___y_2878_ = v_usingArg_2908_;
v___y_2879_ = v___y_2906_;
v___y_2880_ = v___x_2916_;
goto v___jp_2858_;
}
}
}
}
v___jp_2919_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2941_ = lean_unsigned_to_nat(4u);
v___x_2942_ = l_Lean_Syntax_getArg(v___y_2932_, v___x_2941_);
lean_dec(v___y_2932_);
v___x_2943_ = l_Lean_Syntax_isNone(v___x_2942_);
if (v___x_2943_ == 0)
{
uint8_t v___x_2944_; 
lean_inc(v___x_2942_);
v___x_2944_ = l_Lean_Syntax_matchesNull(v___x_2942_, v___y_2935_);
lean_dec(v___y_2935_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; 
lean_dec(v___x_2942_);
lean_dec(v_args_2940_);
lean_dec(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2933_);
lean_dec(v___y_2930_);
lean_dec(v___y_2928_);
lean_dec(v___y_2925_);
lean_dec(v___y_2921_);
lean_dec(v_tk_2856_);
v___x_2945_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2945_;
}
else
{
lean_object* v_usingTk_x3f_2946_; lean_object* v_usingArg_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_usingTk_x3f_2946_ = l_Lean_Syntax_getArg(v___x_2942_, v___x_2855_);
v_usingArg_2947_ = l_Lean_Syntax_getArg(v___x_2942_, v___x_2857_);
lean_dec(v___x_2942_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_usingTk_x3f_2946_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_usingArg_2947_);
v___y_2887_ = v___y_2920_;
v___y_2888_ = v___y_2921_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___y_2925_;
v___y_2893_ = v___y_2926_;
v___y_2894_ = v___y_2927_;
v___y_2895_ = v___y_2928_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v___x_2941_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v_args_2940_;
v___y_2902_ = v___y_2934_;
v___y_2903_ = v___y_2936_;
v___y_2904_ = v___y_2937_;
v___y_2905_ = v___y_2938_;
v___y_2906_ = v___y_2939_;
v_usingTk_x3f_2907_ = v___x_2948_;
v_usingArg_2908_ = v___x_2949_;
goto v___jp_2886_;
}
}
else
{
lean_object* v___x_2950_; 
lean_dec(v___x_2942_);
lean_dec(v___y_2935_);
v___x_2950_ = lean_box(0);
v___y_2887_ = v___y_2920_;
v___y_2888_ = v___y_2921_;
v___y_2889_ = v___y_2922_;
v___y_2890_ = v___y_2923_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___y_2925_;
v___y_2893_ = v___y_2926_;
v___y_2894_ = v___y_2927_;
v___y_2895_ = v___y_2928_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v___x_2941_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v_args_2940_;
v___y_2902_ = v___y_2934_;
v___y_2903_ = v___y_2936_;
v___y_2904_ = v___y_2937_;
v___y_2905_ = v___y_2938_;
v___y_2906_ = v___y_2939_;
v_usingTk_x3f_2907_ = v___x_2950_;
v_usingArg_2908_ = v___x_2950_;
goto v___jp_2886_;
}
}
v___jp_2951_:
{
lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2973_ = l_Lean_Syntax_getArg(v___y_2963_, v___y_2961_);
lean_dec(v___y_2961_);
v___x_2974_ = l_Lean_Syntax_isNone(v___x_2973_);
if (v___x_2974_ == 0)
{
uint8_t v___x_2975_; 
lean_inc(v___x_2973_);
v___x_2975_ = l_Lean_Syntax_matchesNull(v___x_2973_, v___x_2857_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_dec(v___x_2973_);
lean_dec(v_only_2964_);
lean_dec(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2960_);
lean_dec(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec(v_tk_2856_);
v___x_2976_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2977_ = l_Lean_Syntax_getArg(v___x_2973_, v___x_2855_);
lean_dec(v___x_2973_);
v___x_2978_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5));
lean_inc(v___x_2977_);
v___x_2979_ = l_Lean_Syntax_isOfKind(v___x_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v___x_2977_);
lean_dec(v_only_2964_);
lean_dec(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2960_);
lean_dec(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec(v_tk_2856_);
v___x_2980_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v_args_2982_; lean_object* v___x_2983_; 
v___x_2981_ = l_Lean_Syntax_getArg(v___x_2977_, v___x_2857_);
lean_dec(v___x_2977_);
v_args_2982_ = l_Lean_Syntax_getArgs(v___x_2981_);
lean_dec(v___x_2981_);
v___x_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_args_2982_);
v___y_2920_ = v___y_2968_;
v___y_2921_ = v___y_2960_;
v___y_2922_ = v___y_2972_;
v___y_2923_ = v___y_2969_;
v___y_2924_ = v___y_2967_;
v___y_2925_ = v___y_2954_;
v___y_2926_ = v___y_2965_;
v___y_2927_ = v___y_2955_;
v___y_2928_ = v_only_2964_;
v___y_2929_ = v___y_2966_;
v___y_2930_ = v___y_2958_;
v___y_2931_ = v___y_2971_;
v___y_2932_ = v___y_2963_;
v___y_2933_ = v___y_2952_;
v___y_2934_ = v___y_2953_;
v___y_2935_ = v___y_2962_;
v___y_2936_ = v___y_2970_;
v___y_2937_ = v___y_2956_;
v___y_2938_ = v___y_2957_;
v___y_2939_ = v___y_2959_;
v_args_2940_ = v___x_2983_;
goto v___jp_2919_;
}
}
}
else
{
lean_object* v___x_2984_; 
lean_dec(v___x_2973_);
v___x_2984_ = lean_box(0);
v___y_2920_ = v___y_2968_;
v___y_2921_ = v___y_2960_;
v___y_2922_ = v___y_2972_;
v___y_2923_ = v___y_2969_;
v___y_2924_ = v___y_2967_;
v___y_2925_ = v___y_2954_;
v___y_2926_ = v___y_2965_;
v___y_2927_ = v___y_2955_;
v___y_2928_ = v_only_2964_;
v___y_2929_ = v___y_2966_;
v___y_2930_ = v___y_2958_;
v___y_2931_ = v___y_2971_;
v___y_2932_ = v___y_2963_;
v___y_2933_ = v___y_2952_;
v___y_2934_ = v___y_2953_;
v___y_2935_ = v___y_2962_;
v___y_2936_ = v___y_2970_;
v___y_2937_ = v___y_2956_;
v___y_2938_ = v___y_2957_;
v___y_2939_ = v___y_2959_;
v_args_2940_ = v___x_2984_;
goto v___jp_2919_;
}
}
v___jp_2985_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2997_ = lean_unsigned_to_nat(3u);
v___x_2998_ = l_Lean_Syntax_getArg(v_stx_2837_, v___x_2997_);
lean_dec(v_stx_2837_);
v___x_2999_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7));
lean_inc(v___x_2998_);
v___x_3000_ = l_Lean_Syntax_isOfKind(v___x_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v___x_2998_);
lean_dec(v_unfold_2996_);
lean_dec(v___y_2995_);
lean_dec(v___y_2988_);
lean_dec(v_tk_2856_);
v___x_3001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = l_Lean_Syntax_getArg(v___x_2998_, v___x_2855_);
v___x_3003_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9));
lean_inc(v___x_3002_);
v___x_3004_ = l_Lean_Syntax_isOfKind(v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
lean_dec(v___x_3002_);
lean_dec(v___x_2998_);
lean_dec(v_unfold_2996_);
lean_dec(v___y_2995_);
lean_dec(v___y_2988_);
lean_dec(v_tk_2856_);
v___x_3005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = l_Lean_Syntax_getArg(v___x_2998_, v___x_2857_);
v___x_3007_ = l_Lean_Syntax_getArg(v___x_2998_, v___y_2995_);
v___x_3008_ = l_Lean_Syntax_isNone(v___x_3007_);
if (v___x_3008_ == 0)
{
uint8_t v___x_3009_; 
lean_inc(v___x_3007_);
v___x_3009_ = l_Lean_Syntax_matchesNull(v___x_3007_, v___x_2857_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
lean_dec(v___x_3007_);
lean_dec(v___x_3006_);
lean_dec(v___x_3002_);
lean_dec(v___x_2998_);
lean_dec(v_unfold_2996_);
lean_dec(v___y_2995_);
lean_dec(v___y_2988_);
lean_dec(v_tk_2856_);
v___x_3010_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3010_;
}
else
{
lean_object* v_only_3011_; lean_object* v___x_3012_; 
v_only_3011_ = l_Lean_Syntax_getArg(v___x_3007_, v___x_2855_);
lean_dec(v___x_3007_);
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_only_3011_);
lean_inc(v___y_2995_);
v___y_2952_ = v___y_2988_;
v___y_2953_ = v___x_3003_;
v___y_2954_ = v_unfold_2996_;
v___y_2955_ = v___x_2999_;
v___y_2956_ = v___x_3002_;
v___y_2957_ = v___x_2997_;
v___y_2958_ = v___y_2995_;
v___y_2959_ = v___x_3004_;
v___y_2960_ = v___x_3006_;
v___y_2961_ = v___x_2997_;
v___y_2962_ = v___y_2995_;
v___y_2963_ = v___x_2998_;
v_only_2964_ = v___x_3012_;
v___y_2965_ = v___y_2987_;
v___y_2966_ = v___y_2989_;
v___y_2967_ = v___y_2991_;
v___y_2968_ = v___y_2994_;
v___y_2969_ = v___y_2992_;
v___y_2970_ = v___y_2986_;
v___y_2971_ = v___y_2993_;
v___y_2972_ = v___y_2990_;
goto v___jp_2951_;
}
}
else
{
lean_object* v___x_3013_; 
lean_dec(v___x_3007_);
v___x_3013_ = lean_box(0);
lean_inc(v___y_2995_);
v___y_2952_ = v___y_2988_;
v___y_2953_ = v___x_3003_;
v___y_2954_ = v_unfold_2996_;
v___y_2955_ = v___x_2999_;
v___y_2956_ = v___x_3002_;
v___y_2957_ = v___x_2997_;
v___y_2958_ = v___y_2995_;
v___y_2959_ = v___x_3004_;
v___y_2960_ = v___x_3006_;
v___y_2961_ = v___x_2997_;
v___y_2962_ = v___y_2995_;
v___y_2963_ = v___x_2998_;
v_only_2964_ = v___x_3013_;
v___y_2965_ = v___y_2987_;
v___y_2966_ = v___y_2989_;
v___y_2967_ = v___y_2991_;
v___y_2968_ = v___y_2994_;
v___y_2969_ = v___y_2992_;
v___y_2970_ = v___y_2986_;
v___y_2971_ = v___y_2993_;
v___y_2972_ = v___y_2990_;
goto v___jp_2951_;
}
}
}
}
v___jp_3014_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3024_ = lean_unsigned_to_nat(2u);
v___x_3025_ = l_Lean_Syntax_getArg(v_stx_2837_, v___x_3024_);
v___x_3026_ = l_Lean_Syntax_isNone(v___x_3025_);
if (v___x_3026_ == 0)
{
uint8_t v___x_3027_; 
lean_inc(v___x_3025_);
v___x_3027_ = l_Lean_Syntax_matchesNull(v___x_3025_, v___x_2857_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; 
lean_dec(v___x_3025_);
lean_dec(v_squeeze_3015_);
lean_dec(v_tk_2856_);
lean_dec(v_stx_2837_);
v___x_3028_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3028_;
}
else
{
lean_object* v_unfold_3029_; lean_object* v___x_3030_; 
v_unfold_3029_ = l_Lean_Syntax_getArg(v___x_3025_, v___x_2855_);
lean_dec(v___x_3025_);
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_unfold_3029_);
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3016_;
v___y_2988_ = v_squeeze_3015_;
v___y_2989_ = v___y_3017_;
v___y_2990_ = v___y_3023_;
v___y_2991_ = v___y_3018_;
v___y_2992_ = v___y_3020_;
v___y_2993_ = v___y_3022_;
v___y_2994_ = v___y_3019_;
v___y_2995_ = v___x_3024_;
v_unfold_2996_ = v___x_3030_;
goto v___jp_2985_;
}
}
else
{
lean_object* v___x_3031_; 
lean_dec(v___x_3025_);
v___x_3031_ = lean_box(0);
v___y_2986_ = v___y_3021_;
v___y_2987_ = v___y_3016_;
v___y_2988_ = v_squeeze_3015_;
v___y_2989_ = v___y_3017_;
v___y_2990_ = v___y_3023_;
v___y_2991_ = v___y_3018_;
v___y_2992_ = v___y_3020_;
v___y_2993_ = v___y_3022_;
v___y_2994_ = v___y_3019_;
v___y_2995_ = v___x_3024_;
v_unfold_2996_ = v___x_3031_;
goto v___jp_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_stx_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_stx_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(lean_object* v_mvarId_3050_, lean_object* v_val_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_3050_, v_val_3051_, v___y_3057_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___boxed(lean_object* v_mvarId_3062_, lean_object* v_val_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(v_mvarId_3062_, v_val_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(lean_object* v_o_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_o_3074_, v___y_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___boxed(lean_object* v_o_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(v_o_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(lean_object* v_00_u03b1_3096_, lean_object* v_msg_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v_msg_3097_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___boxed(lean_object* v_00_u03b1_3108_, lean_object* v_msg_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(v_00_u03b1_3108_, v_msg_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(lean_object* v_00_u03b1_3120_, lean_object* v_x_3121_, lean_object* v_mkInfoTree_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v_x_3121_, v_mkInfoTree_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_x_3134_, lean_object* v_mkInfoTree_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(v_00_u03b1_3133_, v_x_3134_, v_mkInfoTree_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3(lean_object* v_00_u03b2_3146_, lean_object* v_x_3147_, lean_object* v_x_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_x_3147_, v_x_3148_, v_x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3151_, lean_object* v_m_3152_, lean_object* v_a_3153_){
_start:
{
uint8_t v___x_3154_; 
v___x_3154_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_m_3152_, v_a_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3155_, lean_object* v_m_3156_, lean_object* v_a_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(v_00_u03b2_3155_, v_m_3156_, v_a_3157_);
lean_dec_ref(v_a_3157_);
lean_dec_ref(v_m_3156_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3160_, lean_object* v_m_3161_, lean_object* v_a_3162_, lean_object* v_b_3163_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(v_m_3161_, v_a_3162_, v_b_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3165_, v___y_3166_, v___y_3172_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(v_mvarId_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_mvarId_3177_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3189_, v___y_3190_, v___y_3196_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(v_mvarId_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v_mvarId_3201_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3213_, lean_object* v_x_3214_, size_t v_x_3215_, size_t v_x_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_3214_, v_x_3215_, v_x_3216_, v_x_3217_, v_x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_, lean_object* v_x_3224_, lean_object* v_x_3225_){
_start:
{
size_t v_x_83977__boxed_3226_; size_t v_x_83978__boxed_3227_; lean_object* v_res_3228_; 
v_x_83977__boxed_3226_ = lean_unbox_usize(v_x_3222_);
lean_dec(v_x_3222_);
v_x_83978__boxed_3227_ = lean_unbox_usize(v_x_3223_);
lean_dec(v_x_3223_);
v_res_3228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(v_00_u03b2_3220_, v_x_3221_, v_x_83977__boxed_3226_, v_x_83978__boxed_3227_, v_x_3224_, v_x_3225_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(lean_object* v_ref_3229_, lean_object* v_msgData_3230_, uint8_t v_severity_3231_, uint8_t v_isSilent_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_3229_, v_msgData_3230_, v_severity_3231_, v_isSilent_3232_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3243_, lean_object* v_msgData_3244_, lean_object* v_severity_3245_, lean_object* v_isSilent_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v_severity_boxed_3256_; uint8_t v_isSilent_boxed_3257_; lean_object* v_res_3258_; 
v_severity_boxed_3256_ = lean_unbox(v_severity_3245_);
v_isSilent_boxed_3257_ = lean_unbox(v_isSilent_3246_);
v_res_3258_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(v_ref_3243_, v_msgData_3244_, v_severity_boxed_3256_, v_isSilent_boxed_3257_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v_ref_3243_);
return v_res_3258_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3259_, lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3263_, lean_object* v_a_3264_, lean_object* v_x_3265_){
_start:
{
uint8_t v_res_3266_; lean_object* v_r_3267_; 
v_res_3266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3263_, v_a_3264_, v_x_3265_);
lean_dec(v_x_3265_);
lean_dec_ref(v_a_3264_);
v_r_3267_ = lean_box(v_res_3266_);
return v_r_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3268_, lean_object* v_data_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3271_, lean_object* v_n_3272_, lean_object* v_k_3273_, lean_object* v_v_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3272_, v_k_3273_, v_v_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3276_, size_t v_depth_3277_, lean_object* v_keys_3278_, lean_object* v_vals_3279_, lean_object* v_heq_3280_, lean_object* v_i_3281_, lean_object* v_entries_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3277_, v_keys_3278_, v_vals_3279_, v_i_3281_, v_entries_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3284_, lean_object* v_depth_3285_, lean_object* v_keys_3286_, lean_object* v_vals_3287_, lean_object* v_heq_3288_, lean_object* v_i_3289_, lean_object* v_entries_3290_){
_start:
{
size_t v_depth_boxed_3291_; lean_object* v_res_3292_; 
v_depth_boxed_3291_ = lean_unbox_usize(v_depth_3285_);
lean_dec(v_depth_3285_);
v_res_3292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3284_, v_depth_boxed_3291_, v_keys_3286_, v_vals_3287_, v_heq_3288_, v_i_3289_, v_entries_3290_);
lean_dec_ref(v_vals_3287_);
lean_dec_ref(v_keys_3286_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3293_, lean_object* v_i_3294_, lean_object* v_source_3295_, lean_object* v_target_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3294_, v_source_3295_, v_target_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3299_, v_x_3300_, v_x_3301_, v_x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3305_, v_x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3317_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3318_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3320_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3321_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3317_, v___x_3318_, v___x_3319_, v___x_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3351_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3352_ = l_Lean_addBuiltinDeclarationRanges(v___x_3350_, v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3354_;
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
res = l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_linter_unnecessarySimpa = lean_io_result_get_value(res);
lean_mark_persistent(l_linter_unnecessarySimpa);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
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
