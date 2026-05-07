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
lean_object* v___x_179_; lean_object* v_infoState_180_; lean_object* v_trees_181_; lean_object* v___x_182_; lean_object* v_infoState_183_; lean_object* v_env_184_; lean_object* v_nextMacroScope_185_; lean_object* v_ngen_186_; lean_object* v_auxDeclNGen_187_; lean_object* v_traceState_188_; lean_object* v_cache_189_; lean_object* v_messages_190_; lean_object* v_snapshotTasks_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_212_; 
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
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_212_ == 0)
{
v___x_193_ = v___x_182_;
v_isShared_194_ = v_isSharedCheck_212_;
goto v_resetjp_192_;
}
else
{
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
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_212_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
uint8_t v_enabled_195_; lean_object* v_assignment_196_; lean_object* v_lazyAssignment_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_210_; 
v_enabled_195_ = lean_ctor_get_uint8(v_infoState_183_, sizeof(void*)*3);
v_assignment_196_ = lean_ctor_get(v_infoState_183_, 0);
v_lazyAssignment_197_ = lean_ctor_get(v_infoState_183_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_infoState_183_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v_infoState_183_, 2);
lean_dec(v_unused_211_);
v___x_199_ = v_infoState_183_;
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_lazyAssignment_197_);
lean_inc(v_assignment_196_);
lean_dec(v_infoState_183_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___closed__1);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 2, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_assignment_196_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_lazyAssignment_197_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___x_201_);
lean_ctor_set_uint8(v_reuseFailAlloc_209_, sizeof(void*)*3, v_enabled_195_);
v___x_203_ = v_reuseFailAlloc_209_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 7, v___x_203_);
v___x_205_ = v___x_193_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_env_184_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_nextMacroScope_185_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_ngen_186_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_auxDeclNGen_187_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_traceState_188_);
lean_ctor_set(v_reuseFailAlloc_208_, 5, v_cache_189_);
lean_ctor_set(v_reuseFailAlloc_208_, 6, v_messages_190_);
lean_ctor_set(v_reuseFailAlloc_208_, 7, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_208_, 8, v_snapshotTasks_191_);
v___x_205_ = v_reuseFailAlloc_208_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_st_ref_set(v___y_177_, v___x_205_);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v_trees_181_);
return v___x_207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg___boxed(lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_213_);
lean_dec(v___y_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7(lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___boxed(lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7(v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_66446__overap_248_; lean_object* v___x_249_; 
v___f_247_ = ((lean_object*)(l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___closed__0));
v___x_66446__overap_248_ = lean_panic_fn_borrowed(v___f_247_, v_msg_237_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
v___x_249_ = lean_apply_9(v___x_66446__overap_248_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, lean_box(0));
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9___boxed(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(lean_object* v_opts_261_, lean_object* v_opt_262_){
_start:
{
lean_object* v_name_263_; lean_object* v_defValue_264_; lean_object* v_map_265_; lean_object* v___x_266_; 
v_name_263_ = lean_ctor_get(v_opt_262_, 0);
v_defValue_264_ = lean_ctor_get(v_opt_262_, 1);
v_map_265_ = lean_ctor_get(v_opts_261_, 0);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_265_, v_name_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
uint8_t v___x_267_; 
v___x_267_ = lean_unbox(v_defValue_264_);
return v___x_267_;
}
else
{
lean_object* v_val_268_; 
v_val_268_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_val_268_);
lean_dec_ref(v___x_266_);
if (lean_obj_tag(v_val_268_) == 1)
{
uint8_t v_v_269_; 
v_v_269_ = lean_ctor_get_uint8(v_val_268_, 0);
lean_dec_ref(v_val_268_);
return v_v_269_;
}
else
{
uint8_t v___x_270_; 
lean_dec(v_val_268_);
v___x_270_ = lean_unbox(v_defValue_264_);
return v___x_270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10___boxed(lean_object* v_opts_271_, lean_object* v_opt_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_opts_271_, v_opt_272_);
lean_dec_ref(v_opt_272_);
lean_dec_ref(v_opts_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_ref_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_ref_284_ = lean_ctor_get(v___y_281_, 5);
v___x_285_ = 0;
v___x_286_ = l_Lean_SourceInfo_fromRef(v_ref_284_, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object* v_a_298_, lean_object* v_trees_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
v___x_309_ = lean_apply_9(v_a_298_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, lean_box(0));
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_318_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v_a_310_);
lean_ctor_set(v___x_314_, 1, v_trees_299_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_trees_299_);
v_a_319_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_309_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_309_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object* v_a_327_, lean_object* v_trees_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(v_a_327_, v_trees_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_338_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object* v_a_345_, lean_object* v_a_346_, uint8_t v___x_347_, uint8_t v___x_348_, uint8_t v___x_349_, lean_object* v_a_350_, lean_object* v_mvarCounter_351_, lean_object* v___x_352_, lean_object* v___x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
lean_inc(v_a_345_);
v___x_363_ = l_Lean_MVarId_getType(v_a_345_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_n(v_a_364_, 2);
lean_dec_ref(v___x_363_);
v___x_365_ = lean_mk_syntax_ident(v_a_346_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v_a_364_);
v___x_367_ = l_Lean_Elab_Term_elabTerm(v___x_365_, v___x_366_, v___x_347_, v___x_347_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___x_402_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref(v___x_367_);
v___x_402_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_348_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_479_; 
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_480_);
v___x_404_ = v___x_402_;
v_isShared_405_ = v_isSharedCheck_479_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_402_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_479_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; 
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
lean_inc(v___y_359_);
lean_inc_ref(v___y_358_);
lean_inc(v_a_368_);
v___x_406_ = lean_infer_type(v_a_368_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; uint8_t v_a_409_; lean_object* v___x_419_; uint8_t v_foApprox_420_; uint8_t v_ctxApprox_421_; uint8_t v_quasiPatternApprox_422_; uint8_t v_constApprox_423_; uint8_t v_isDefEqStuckEx_424_; uint8_t v_unificationHints_425_; uint8_t v_proofIrrelevance_426_; uint8_t v_offsetCnstrs_427_; uint8_t v_transparency_428_; uint8_t v_etaStruct_429_; uint8_t v_univApprox_430_; uint8_t v_iota_431_; uint8_t v_beta_432_; uint8_t v_proj_433_; uint8_t v_zeta_434_; uint8_t v_zetaDelta_435_; uint8_t v_zetaUnused_436_; uint8_t v_zetaHave_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_470_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref(v___x_406_);
v___x_419_ = l_Lean_Meta_Context_config(v___y_358_);
v_foApprox_420_ = lean_ctor_get_uint8(v___x_419_, 0);
v_ctxApprox_421_ = lean_ctor_get_uint8(v___x_419_, 1);
v_quasiPatternApprox_422_ = lean_ctor_get_uint8(v___x_419_, 2);
v_constApprox_423_ = lean_ctor_get_uint8(v___x_419_, 3);
v_isDefEqStuckEx_424_ = lean_ctor_get_uint8(v___x_419_, 4);
v_unificationHints_425_ = lean_ctor_get_uint8(v___x_419_, 5);
v_proofIrrelevance_426_ = lean_ctor_get_uint8(v___x_419_, 6);
v_offsetCnstrs_427_ = lean_ctor_get_uint8(v___x_419_, 8);
v_transparency_428_ = lean_ctor_get_uint8(v___x_419_, 9);
v_etaStruct_429_ = lean_ctor_get_uint8(v___x_419_, 10);
v_univApprox_430_ = lean_ctor_get_uint8(v___x_419_, 11);
v_iota_431_ = lean_ctor_get_uint8(v___x_419_, 12);
v_beta_432_ = lean_ctor_get_uint8(v___x_419_, 13);
v_proj_433_ = lean_ctor_get_uint8(v___x_419_, 14);
v_zeta_434_ = lean_ctor_get_uint8(v___x_419_, 15);
v_zetaDelta_435_ = lean_ctor_get_uint8(v___x_419_, 16);
v_zetaUnused_436_ = lean_ctor_get_uint8(v___x_419_, 17);
v_zetaHave_437_ = lean_ctor_get_uint8(v___x_419_, 18);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_470_ == 0)
{
v___x_439_ = v___x_419_;
v_isShared_440_ = v_isSharedCheck_470_;
goto v_resetjp_438_;
}
else
{
lean_dec(v___x_419_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_470_;
goto v_resetjp_438_;
}
v___jp_408_:
{
if (v_a_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_410_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1);
lean_inc_ref(v_a_350_);
v___x_411_ = l_Lean_indentExpr(v_a_350_);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__3);
v___x_414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_412_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_414_);
v___x_416_ = v___x_404_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_418_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; 
lean_inc(v_a_368_);
v___x_417_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_416_, v_a_364_, v_a_407_, v_a_368_, v___x_353_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec_ref(v___x_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_dec_ref(v___x_417_);
v___y_370_ = v___y_354_;
v___y_371_ = v___y_355_;
v___y_372_ = v___y_356_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
goto v___jp_369_;
}
else
{
lean_dec(v_a_368_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_345_);
return v___x_417_;
}
}
}
else
{
lean_dec(v_a_407_);
lean_del_object(v___x_404_);
lean_dec(v_a_364_);
lean_dec(v___x_353_);
v___y_370_ = v___y_354_;
v___y_371_ = v___y_355_;
v___y_372_ = v___y_356_;
v___y_373_ = v___y_357_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
goto v___jp_369_;
}
}
v_resetjp_438_:
{
uint8_t v_trackZetaDelta_441_; lean_object* v_zetaDeltaSet_442_; lean_object* v_lctx_443_; lean_object* v_localInstances_444_; lean_object* v_defEqCtx_x3f_445_; lean_object* v_synthPendingDepth_446_; lean_object* v_canUnfold_x3f_447_; uint8_t v_univApprox_448_; uint8_t v_inTypeClassResolution_449_; uint8_t v_cacheInferType_450_; lean_object* v___x_452_; 
v_trackZetaDelta_441_ = lean_ctor_get_uint8(v___y_358_, sizeof(void*)*7);
v_zetaDeltaSet_442_ = lean_ctor_get(v___y_358_, 1);
v_lctx_443_ = lean_ctor_get(v___y_358_, 2);
v_localInstances_444_ = lean_ctor_get(v___y_358_, 3);
v_defEqCtx_x3f_445_ = lean_ctor_get(v___y_358_, 4);
v_synthPendingDepth_446_ = lean_ctor_get(v___y_358_, 5);
v_canUnfold_x3f_447_ = lean_ctor_get(v___y_358_, 6);
v_univApprox_448_ = lean_ctor_get_uint8(v___y_358_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_449_ = lean_ctor_get_uint8(v___y_358_, sizeof(void*)*7 + 2);
v_cacheInferType_450_ = lean_ctor_get_uint8(v___y_358_, sizeof(void*)*7 + 3);
if (v_isShared_440_ == 0)
{
v___x_452_ = v___x_439_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 0, v_foApprox_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 1, v_ctxApprox_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 2, v_quasiPatternApprox_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 3, v_constApprox_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 4, v_isDefEqStuckEx_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 5, v_unificationHints_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 6, v_proofIrrelevance_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 8, v_offsetCnstrs_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 9, v_transparency_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 10, v_etaStruct_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 11, v_univApprox_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 12, v_iota_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 13, v_beta_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 14, v_proj_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 15, v_zeta_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 16, v_zetaDelta_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 17, v_zetaUnused_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_469_, 18, v_zetaHave_437_);
v___x_452_ = v_reuseFailAlloc_469_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
uint64_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_ctor_set_uint8(v___x_452_, 7, v___x_349_);
v___x_453_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set_uint64(v___x_454_, sizeof(void*)*1, v___x_453_);
lean_inc(v_canUnfold_x3f_447_);
lean_inc(v_synthPendingDepth_446_);
lean_inc(v_defEqCtx_x3f_445_);
lean_inc_ref(v_localInstances_444_);
lean_inc_ref(v_lctx_443_);
lean_inc(v_zetaDeltaSet_442_);
v___x_455_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_zetaDeltaSet_442_);
lean_ctor_set(v___x_455_, 2, v_lctx_443_);
lean_ctor_set(v___x_455_, 3, v_localInstances_444_);
lean_ctor_set(v___x_455_, 4, v_defEqCtx_x3f_445_);
lean_ctor_set(v___x_455_, 5, v_synthPendingDepth_446_);
lean_ctor_set(v___x_455_, 6, v_canUnfold_x3f_447_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*7, v_trackZetaDelta_441_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*7 + 1, v_univApprox_448_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*7 + 2, v_inTypeClassResolution_449_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*7 + 3, v_cacheInferType_450_);
lean_inc(v_a_407_);
lean_inc(v_a_364_);
v___x_456_ = l_Lean_Meta_isExprDefEq(v_a_364_, v_a_407_, v___x_455_, v___y_359_, v___y_360_, v___y_361_);
lean_dec_ref(v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; uint8_t v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___x_458_ = lean_unbox(v_a_457_);
lean_dec(v_a_457_);
v_a_409_ = v___x_458_;
goto v___jp_408_;
}
else
{
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_459_; uint8_t v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_456_);
v___x_460_ = lean_unbox(v_a_459_);
lean_dec(v_a_459_);
v_a_409_ = v___x_460_;
goto v___jp_408_;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_a_407_);
lean_del_object(v___x_404_);
lean_dec(v_a_368_);
lean_dec(v_a_364_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___x_353_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_345_);
v_a_461_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_456_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_456_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_404_);
lean_dec(v_a_368_);
lean_dec(v_a_364_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___x_353_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_345_);
v_a_471_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_406_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_406_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
else
{
lean_dec(v_a_368_);
lean_dec(v_a_364_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___x_353_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_345_);
return v___x_402_;
}
v___jp_369_:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_getMVars(v_a_350_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
v___x_380_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_379_, v_mvarCounter_351_, v___y_375_);
lean_dec(v_a_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref(v___x_380_);
v___x_382_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_381_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v_a_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v___x_382_);
v___x_383_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_345_, v___y_371_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v___x_383_);
v___x_384_ = l_Lean_Name_mkStr1(v___x_352_);
v___x_385_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_384_, v_a_368_, v___x_348_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v___x_385_;
}
else
{
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v_a_368_);
lean_dec_ref(v___x_352_);
return v___x_383_;
}
}
else
{
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v_a_368_);
lean_dec_ref(v___x_352_);
lean_dec(v_a_345_);
return v___x_382_;
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v_a_368_);
lean_dec_ref(v___x_352_);
lean_dec(v_a_345_);
v_a_386_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_380_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_380_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v_a_368_);
lean_dec_ref(v___x_352_);
lean_dec(v_a_345_);
v_a_394_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_378_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_378_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_a_364_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___x_353_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_345_);
v_a_481_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_367_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_367_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___x_353_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_346_);
lean_dec(v_a_345_);
v_a_489_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_363_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_363_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed(lean_object** _args){
lean_object* v_a_497_ = _args[0];
lean_object* v_a_498_ = _args[1];
lean_object* v___x_499_ = _args[2];
lean_object* v___x_500_ = _args[3];
lean_object* v___x_501_ = _args[4];
lean_object* v_a_502_ = _args[5];
lean_object* v_mvarCounter_503_ = _args[6];
lean_object* v___x_504_ = _args[7];
lean_object* v___x_505_ = _args[8];
lean_object* v___y_506_ = _args[9];
lean_object* v___y_507_ = _args[10];
lean_object* v___y_508_ = _args[11];
lean_object* v___y_509_ = _args[12];
lean_object* v___y_510_ = _args[13];
lean_object* v___y_511_ = _args[14];
lean_object* v___y_512_ = _args[15];
lean_object* v___y_513_ = _args[16];
lean_object* v___y_514_ = _args[17];
_start:
{
uint8_t v___x_78744__boxed_515_; uint8_t v___x_78745__boxed_516_; uint8_t v___x_78746__boxed_517_; lean_object* v_res_518_; 
v___x_78744__boxed_515_ = lean_unbox(v___x_499_);
v___x_78745__boxed_516_ = lean_unbox(v___x_500_);
v___x_78746__boxed_517_ = lean_unbox(v___x_501_);
v_res_518_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(v_a_497_, v_a_498_, v___x_78744__boxed_515_, v___x_78745__boxed_516_, v___x_78746__boxed_517_, v_a_502_, v_mvarCounter_503_, v___x_504_, v___x_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v_mvarCounter_503_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object* v_a_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_infoState_530_; lean_object* v_env_531_; lean_object* v_nextMacroScope_532_; lean_object* v_ngen_533_; lean_object* v_auxDeclNGen_534_; lean_object* v_traceState_535_; lean_object* v_cache_536_; lean_object* v_messages_537_; lean_object* v_snapshotTasks_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_559_; 
v___x_529_ = lean_st_ref_take(v___y_527_);
v_infoState_530_ = lean_ctor_get(v___x_529_, 7);
v_env_531_ = lean_ctor_get(v___x_529_, 0);
v_nextMacroScope_532_ = lean_ctor_get(v___x_529_, 1);
v_ngen_533_ = lean_ctor_get(v___x_529_, 2);
v_auxDeclNGen_534_ = lean_ctor_get(v___x_529_, 3);
v_traceState_535_ = lean_ctor_get(v___x_529_, 4);
v_cache_536_ = lean_ctor_get(v___x_529_, 5);
v_messages_537_ = lean_ctor_get(v___x_529_, 6);
v_snapshotTasks_538_ = lean_ctor_get(v___x_529_, 8);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_559_ == 0)
{
v___x_540_ = v___x_529_;
v_isShared_541_ = v_isSharedCheck_559_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snapshotTasks_538_);
lean_inc(v_infoState_530_);
lean_inc(v_messages_537_);
lean_inc(v_cache_536_);
lean_inc(v_traceState_535_);
lean_inc(v_auxDeclNGen_534_);
lean_inc(v_ngen_533_);
lean_inc(v_nextMacroScope_532_);
lean_inc(v_env_531_);
lean_dec(v___x_529_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_559_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint8_t v_enabled_542_; lean_object* v_assignment_543_; lean_object* v_lazyAssignment_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_557_; 
v_enabled_542_ = lean_ctor_get_uint8(v_infoState_530_, sizeof(void*)*3);
v_assignment_543_ = lean_ctor_get(v_infoState_530_, 0);
v_lazyAssignment_544_ = lean_ctor_get(v_infoState_530_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_infoState_530_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_infoState_530_, 2);
lean_dec(v_unused_558_);
v___x_546_ = v_infoState_530_;
v_isShared_547_ = v_isSharedCheck_557_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_lazyAssignment_544_);
lean_inc(v_assignment_543_);
lean_dec(v_infoState_530_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_557_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 2, v_a_519_);
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_assignment_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_lazyAssignment_544_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_a_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*3, v_enabled_542_);
v___x_549_ = v_reuseFailAlloc_556_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 7, v___x_549_);
v___x_551_ = v___x_540_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_env_531_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_nextMacroScope_532_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_ngen_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_auxDeclNGen_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_traceState_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v_cache_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_messages_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_snapshotTasks_538_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_st_ref_set(v___y_527_, v___x_551_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object* v_a_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(v_a_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(lean_object* v_msgData_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v_env_578_; lean_object* v___x_579_; lean_object* v_mctx_580_; lean_object* v_lctx_581_; lean_object* v_options_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_577_ = lean_st_ref_get(v___y_575_);
v_env_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_577_);
v___x_579_ = lean_st_ref_get(v___y_573_);
v_mctx_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_mctx_580_);
lean_dec(v___x_579_);
v_lctx_581_ = lean_ctor_get(v___y_572_, 2);
v_options_582_ = lean_ctor_get(v___y_574_, 2);
lean_inc_ref(v_options_582_);
lean_inc_ref(v_lctx_581_);
v___x_583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_583_, 0, v_env_578_);
lean_ctor_set(v___x_583_, 1, v_mctx_580_);
lean_ctor_set(v___x_583_, 2, v_lctx_581_);
lean_ctor_set(v___x_583_, 3, v_options_582_);
v___x_584_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_msgData_571_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10___boxed(lean_object* v_msgData_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v_msgData_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(lean_object* v_msg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_ref_599_; lean_object* v___x_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_ref_599_ = lean_ctor_get(v___y_596_, 5);
v___x_600_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v_msg_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
lean_inc(v_ref_599_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v_ref_599_);
lean_ctor_set(v___x_605_, 1, v_a_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set_tag(v___x_603_, 1);
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg___boxed(lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v_msg_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(lean_object* v_mvarId_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; lean_object* v_mctx_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_621_ = lean_st_ref_get(v___y_619_);
v_mctx_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref(v_mctx_622_);
lean_dec(v___x_621_);
v___x_623_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_622_, v_mvarId_617_);
lean_dec_ref(v_mctx_622_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___y_618_);
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object* v_mvarId_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec(v_mvarId_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_mvarId_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; lean_object* v_mctx_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_636_ = lean_st_ref_get(v___y_634_);
v_mctx_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_mctx_637_);
lean_dec(v___x_636_);
v___x_638_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_637_, v_mvarId_632_);
lean_dec_ref(v_mctx_637_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v___y_633_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_mvarId_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec(v_mvarId_642_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
return v_x_647_;
}
else
{
lean_object* v_key_649_; lean_object* v_value_650_; lean_object* v_tail_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_674_; 
v_key_649_ = lean_ctor_get(v_x_648_, 0);
v_value_650_ = lean_ctor_get(v_x_648_, 1);
v_tail_651_ = lean_ctor_get(v_x_648_, 2);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_674_ == 0)
{
v___x_653_ = v_x_648_;
v_isShared_654_ = v_isSharedCheck_674_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_tail_651_);
lean_inc(v_value_650_);
lean_inc(v_key_649_);
lean_dec(v_x_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_674_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v_fold_659_; uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_655_ = lean_array_get_size(v_x_647_);
v___x_656_ = l_Lean_Expr_hash(v_key_649_);
v___x_657_ = 32ULL;
v___x_658_ = lean_uint64_shift_right(v___x_656_, v___x_657_);
v_fold_659_ = lean_uint64_xor(v___x_656_, v___x_658_);
v___x_660_ = 16ULL;
v___x_661_ = lean_uint64_shift_right(v_fold_659_, v___x_660_);
v___x_662_ = lean_uint64_xor(v_fold_659_, v___x_661_);
v___x_663_ = lean_uint64_to_usize(v___x_662_);
v___x_664_ = lean_usize_of_nat(v___x_655_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_sub(v___x_664_, v___x_665_);
v___x_667_ = lean_usize_land(v___x_663_, v___x_666_);
v___x_668_ = lean_array_uget_borrowed(v_x_647_, v___x_667_);
lean_inc(v___x_668_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 2, v___x_668_);
v___x_670_ = v___x_653_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_key_649_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_value_650_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v___x_668_);
v___x_670_ = v_reuseFailAlloc_673_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_array_uset(v_x_647_, v___x_667_, v___x_670_);
v_x_647_ = v___x_671_;
v_x_648_ = v_tail_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object* v_i_675_, lean_object* v_source_676_, lean_object* v_target_677_){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_array_get_size(v_source_676_);
v___x_679_ = lean_nat_dec_lt(v_i_675_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec_ref(v_source_676_);
lean_dec(v_i_675_);
return v_target_677_;
}
else
{
lean_object* v_es_680_; lean_object* v___x_681_; lean_object* v_source_682_; lean_object* v_target_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_es_680_ = lean_array_fget(v_source_676_, v_i_675_);
v___x_681_ = lean_box(0);
v_source_682_ = lean_array_fset(v_source_676_, v_i_675_, v___x_681_);
v_target_683_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_677_, v_es_680_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_add(v_i_675_, v___x_684_);
lean_dec(v_i_675_);
v_i_675_ = v___x_685_;
v_source_676_ = v_source_682_;
v_target_677_ = v_target_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_data_687_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_nbuckets_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_688_ = lean_array_get_size(v_data_687_);
v___x_689_ = lean_unsigned_to_nat(2u);
v_nbuckets_690_ = lean_nat_mul(v___x_688_, v___x_689_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_box(0);
v___x_693_ = lean_mk_array(v_nbuckets_690_, v___x_692_);
v___x_694_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_691_, v_data_687_, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_a_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
else
{
lean_object* v_key_698_; lean_object* v_tail_699_; uint8_t v___x_700_; 
v_key_698_ = lean_ctor_get(v_x_696_, 0);
v_tail_699_ = lean_ctor_get(v_x_696_, 2);
v___x_700_ = lean_expr_eqv(v_key_698_, v_a_695_);
if (v___x_700_ == 0)
{
v_x_696_ = v_tail_699_;
goto _start;
}
else
{
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_702_, v_x_703_);
lean_dec(v_x_703_);
lean_dec_ref(v_a_702_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(lean_object* v_m_706_, lean_object* v_a_707_, lean_object* v_b_708_){
_start:
{
lean_object* v_size_709_; lean_object* v_buckets_710_; lean_object* v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v_fold_715_; uint64_t v___x_716_; uint64_t v___x_717_; uint64_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v_bkt_724_; uint8_t v___x_725_; 
v_size_709_ = lean_ctor_get(v_m_706_, 0);
v_buckets_710_ = lean_ctor_get(v_m_706_, 1);
v___x_711_ = lean_array_get_size(v_buckets_710_);
v___x_712_ = l_Lean_Expr_hash(v_a_707_);
v___x_713_ = 32ULL;
v___x_714_ = lean_uint64_shift_right(v___x_712_, v___x_713_);
v_fold_715_ = lean_uint64_xor(v___x_712_, v___x_714_);
v___x_716_ = 16ULL;
v___x_717_ = lean_uint64_shift_right(v_fold_715_, v___x_716_);
v___x_718_ = lean_uint64_xor(v_fold_715_, v___x_717_);
v___x_719_ = lean_uint64_to_usize(v___x_718_);
v___x_720_ = lean_usize_of_nat(v___x_711_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_sub(v___x_720_, v___x_721_);
v___x_723_ = lean_usize_land(v___x_719_, v___x_722_);
v_bkt_724_ = lean_array_uget_borrowed(v_buckets_710_, v___x_723_);
v___x_725_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_707_, v_bkt_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_746_; 
lean_inc_ref(v_buckets_710_);
lean_inc(v_size_709_);
v_isSharedCheck_746_ = !lean_is_exclusive(v_m_706_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; lean_object* v_unused_748_; 
v_unused_747_ = lean_ctor_get(v_m_706_, 1);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_m_706_, 0);
lean_dec(v_unused_748_);
v___x_727_ = v_m_706_;
v_isShared_728_ = v_isSharedCheck_746_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_m_706_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_746_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v_size_x27_730_; lean_object* v___x_731_; lean_object* v_buckets_x27_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v_size_x27_730_ = lean_nat_add(v_size_709_, v___x_729_);
lean_dec(v_size_709_);
lean_inc(v_bkt_724_);
v___x_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_731_, 0, v_a_707_);
lean_ctor_set(v___x_731_, 1, v_b_708_);
lean_ctor_set(v___x_731_, 2, v_bkt_724_);
v_buckets_x27_732_ = lean_array_uset(v_buckets_710_, v___x_723_, v___x_731_);
v___x_733_ = lean_unsigned_to_nat(4u);
v___x_734_ = lean_nat_mul(v_size_x27_730_, v___x_733_);
v___x_735_ = lean_unsigned_to_nat(3u);
v___x_736_ = lean_nat_div(v___x_734_, v___x_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_array_get_size(v_buckets_x27_732_);
v___x_738_ = lean_nat_dec_le(v___x_736_, v___x_737_);
lean_dec(v___x_736_);
if (v___x_738_ == 0)
{
lean_object* v_val_739_; lean_object* v___x_741_; 
v_val_739_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_732_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_val_739_);
lean_ctor_set(v___x_727_, 0, v_size_x27_730_);
v___x_741_ = v___x_727_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_size_x27_730_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_val_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_744_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_buckets_x27_732_);
lean_ctor_set(v___x_727_, 0, v_size_x27_730_);
v___x_744_ = v___x_727_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_size_x27_730_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_buckets_x27_732_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_dec(v_b_708_);
lean_dec_ref(v_a_707_);
return v_m_706_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(lean_object* v_m_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_buckets_751_; lean_object* v___x_752_; uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v___x_755_; uint64_t v_fold_756_; uint64_t v___x_757_; uint64_t v___x_758_; uint64_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_buckets_751_ = lean_ctor_get(v_m_749_, 1);
v___x_752_ = lean_array_get_size(v_buckets_751_);
v___x_753_ = l_Lean_Expr_hash(v_a_750_);
v___x_754_ = 32ULL;
v___x_755_ = lean_uint64_shift_right(v___x_753_, v___x_754_);
v_fold_756_ = lean_uint64_xor(v___x_753_, v___x_755_);
v___x_757_ = 16ULL;
v___x_758_ = lean_uint64_shift_right(v_fold_756_, v___x_757_);
v___x_759_ = lean_uint64_xor(v_fold_756_, v___x_758_);
v___x_760_ = lean_uint64_to_usize(v___x_759_);
v___x_761_ = lean_usize_of_nat(v___x_752_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_sub(v___x_761_, v___x_762_);
v___x_764_ = lean_usize_land(v___x_760_, v___x_763_);
v___x_765_ = lean_array_uget_borrowed(v_buckets_751_, v___x_764_);
v___x_766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_750_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_767_, lean_object* v_a_768_){
_start:
{
uint8_t v_res_769_; lean_object* v_r_770_; 
v_res_769_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_m_767_, v_a_768_);
lean_dec_ref(v_a_768_);
lean_dec_ref(v_m_767_);
v_r_770_ = lean_box(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object* v_mvarId_775_, lean_object* v_e_776_, lean_object* v_a_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_d_788_; lean_object* v_b_789_; lean_object* v___y_790_; uint8_t v___x_796_; 
v___x_796_ = l_Lean_Expr_hasExprMVar(v_e_776_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_e_776_);
v___x_797_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_a_777_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
else
{
uint8_t v___x_800_; 
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_a_777_, v_e_776_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_box(0);
lean_inc_ref(v_e_776_);
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(v_a_777_, v_e_776_, v___x_801_);
switch(lean_obj_tag(v_e_776_))
{
case 11:
{
lean_object* v_struct_803_; 
v_struct_803_ = lean_ctor_get(v_e_776_, 2);
lean_inc_ref(v_struct_803_);
lean_dec_ref(v_e_776_);
v_e_776_ = v_struct_803_;
v_a_777_ = v___x_802_;
goto _start;
}
case 7:
{
lean_object* v_binderType_805_; lean_object* v_body_806_; 
v_binderType_805_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_binderType_805_);
v_body_806_ = lean_ctor_get(v_e_776_, 2);
lean_inc_ref(v_body_806_);
lean_dec_ref(v_e_776_);
v_d_788_ = v_binderType_805_;
v_b_789_ = v_body_806_;
v___y_790_ = v___x_802_;
goto v___jp_787_;
}
case 6:
{
lean_object* v_binderType_807_; lean_object* v_body_808_; 
v_binderType_807_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_binderType_807_);
v_body_808_ = lean_ctor_get(v_e_776_, 2);
lean_inc_ref(v_body_808_);
lean_dec_ref(v_e_776_);
v_d_788_ = v_binderType_807_;
v_b_789_ = v_body_808_;
v___y_790_ = v___x_802_;
goto v___jp_787_;
}
case 8:
{
lean_object* v_type_809_; lean_object* v_value_810_; lean_object* v_body_811_; lean_object* v___x_812_; 
v_type_809_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_type_809_);
v_value_810_ = lean_ctor_get(v_e_776_, 2);
lean_inc_ref(v_value_810_);
v_body_811_ = lean_ctor_get(v_e_776_, 3);
lean_inc_ref(v_body_811_);
lean_dec_ref(v_e_776_);
v___x_812_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_775_, v_type_809_, v___x_802_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v_fst_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
v_fst_814_ = lean_ctor_get(v_a_813_, 0);
if (lean_obj_tag(v_fst_814_) == 0)
{
lean_dec(v_a_813_);
lean_dec_ref(v_body_811_);
lean_dec_ref(v_value_810_);
return v___x_812_;
}
else
{
lean_object* v_snd_815_; lean_object* v___x_816_; 
lean_dec_ref(v___x_812_);
v_snd_815_ = lean_ctor_get(v_a_813_, 1);
lean_inc(v_snd_815_);
lean_dec(v_a_813_);
v___x_816_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_775_, v_value_810_, v_snd_815_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v_fst_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
v_fst_818_ = lean_ctor_get(v_a_817_, 0);
if (lean_obj_tag(v_fst_818_) == 0)
{
lean_dec(v_a_817_);
lean_dec_ref(v_body_811_);
return v___x_816_;
}
else
{
lean_object* v_snd_819_; 
lean_dec_ref(v___x_816_);
v_snd_819_ = lean_ctor_get(v_a_817_, 1);
lean_inc(v_snd_819_);
lean_dec(v_a_817_);
v_e_776_ = v_body_811_;
v_a_777_ = v_snd_819_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_811_);
return v___x_816_;
}
}
}
else
{
lean_dec_ref(v_body_811_);
lean_dec_ref(v_value_810_);
return v___x_812_;
}
}
case 10:
{
lean_object* v_expr_821_; 
v_expr_821_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_expr_821_);
lean_dec_ref(v_e_776_);
v_e_776_ = v_expr_821_;
v_a_777_ = v___x_802_;
goto _start;
}
case 5:
{
lean_object* v_fn_823_; lean_object* v_arg_824_; lean_object* v___x_825_; 
v_fn_823_ = lean_ctor_get(v_e_776_, 0);
lean_inc_ref(v_fn_823_);
v_arg_824_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_arg_824_);
lean_dec_ref(v_e_776_);
v___x_825_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_775_, v_fn_823_, v___x_802_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v_fst_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
v_fst_827_ = lean_ctor_get(v_a_826_, 0);
if (lean_obj_tag(v_fst_827_) == 0)
{
lean_dec(v_a_826_);
lean_dec_ref(v_arg_824_);
return v___x_825_;
}
else
{
lean_object* v_snd_828_; 
lean_dec_ref(v___x_825_);
v_snd_828_ = lean_ctor_get(v_a_826_, 1);
lean_inc(v_snd_828_);
lean_dec(v_a_826_);
v_e_776_ = v_arg_824_;
v_a_777_ = v_snd_828_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_824_);
return v___x_825_;
}
}
case 2:
{
lean_object* v_mvarId_830_; lean_object* v___x_831_; 
v_mvarId_830_ = lean_ctor_get(v_e_776_, 0);
lean_inc(v_mvarId_830_);
lean_dec_ref(v_e_776_);
v___x_831_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(v_mvarId_775_, v_mvarId_830_, v___x_802_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_831_;
}
default: 
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec_ref(v_e_776_);
v___x_832_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___x_802_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v_e_776_);
v___x_835_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_a_777_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
v___jp_787_:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_775_, v_d_788_, v___y_790_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_fst_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
v_fst_793_ = lean_ctor_get(v_a_792_, 0);
if (lean_obj_tag(v_fst_793_) == 0)
{
lean_dec(v_a_792_);
lean_dec_ref(v_b_789_);
return v___x_791_;
}
else
{
lean_object* v_snd_794_; 
lean_dec_ref(v___x_791_);
v_snd_794_ = lean_ctor_get(v_a_792_, 1);
lean_inc(v_snd_794_);
lean_dec(v_a_792_);
v_e_776_ = v_b_789_;
v_a_777_ = v_snd_794_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_789_);
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(lean_object* v_mvarId_838_, lean_object* v_mvarId_x27_839_, lean_object* v_a_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = l_Lean_instBEqMVarId_beq(v_mvarId_838_, v_mvarId_x27_839_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_839_, v_a_840_, v___y_846_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_935_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_935_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_935_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_935_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_fst_856_; 
v_fst_856_ = lean_ctor_get(v_a_852_, 0);
lean_inc(v_fst_856_);
if (lean_obj_tag(v_fst_856_) == 0)
{
lean_object* v_snd_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_mvarId_x27_839_);
v_snd_857_ = lean_ctor_get(v_a_852_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_a_852_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v_a_852_, 0);
lean_dec(v_unused_876_);
v___x_859_ = v_a_852_;
v_isShared_860_ = v_isSharedCheck_875_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snd_857_);
lean_dec(v_a_852_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_875_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_874_; 
v_a_861_ = lean_ctor_get(v_fst_856_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_fst_856_);
if (v_isSharedCheck_874_ == 0)
{
v___x_863_ = v_fst_856_;
v_isShared_864_ = v_isSharedCheck_874_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v_fst_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_874_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_873_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_866_);
v___x_868_ = v___x_859_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_snd_857_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_868_);
v___x_870_ = v___x_854_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
else
{
lean_object* v_a_877_; 
lean_del_object(v___x_854_);
v_a_877_ = lean_ctor_get(v_fst_856_, 0);
lean_inc(v_a_877_);
lean_dec_ref(v_fst_856_);
if (lean_obj_tag(v_a_877_) == 0)
{
lean_object* v_snd_878_; lean_object* v___x_879_; 
v_snd_878_ = lean_ctor_get(v_a_852_, 1);
lean_inc(v_snd_878_);
lean_dec(v_a_852_);
v___x_879_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_839_, v_snd_878_, v___y_846_);
lean_dec(v_mvarId_x27_839_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_923_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_923_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_923_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_923_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_fst_884_; 
v_fst_884_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_fst_884_);
if (lean_obj_tag(v_fst_884_) == 0)
{
lean_object* v_snd_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_903_; 
v_snd_885_ = lean_ctor_get(v_a_880_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_880_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_a_880_, 0);
lean_dec(v_unused_904_);
v___x_887_ = v_a_880_;
v_isShared_888_ = v_isSharedCheck_903_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_snd_885_);
lean_dec(v_a_880_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_903_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_902_; 
v_a_889_ = lean_ctor_get(v_fst_884_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v_fst_884_);
if (v_isSharedCheck_902_ == 0)
{
v___x_891_ = v_fst_884_;
v_isShared_892_ = v_isSharedCheck_902_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v_fst_884_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_902_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_901_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_894_);
v___x_896_ = v___x_887_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_snd_885_);
v___x_896_ = v_reuseFailAlloc_900_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_896_);
v___x_898_ = v___x_882_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
else
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v_fst_884_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v_fst_884_);
if (lean_obj_tag(v_a_905_) == 0)
{
lean_object* v_snd_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_917_; 
v_snd_906_ = lean_ctor_get(v_a_880_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_880_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_a_880_, 0);
lean_dec(v_unused_918_);
v___x_908_ = v_a_880_;
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_snd_906_);
lean_dec(v_a_880_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_917_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_910_);
v___x_912_ = v___x_908_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_snd_906_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_912_);
v___x_914_ = v___x_882_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
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
else
{
lean_object* v_val_919_; lean_object* v_snd_920_; lean_object* v_mvarIdPending_921_; 
lean_del_object(v___x_882_);
v_val_919_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_val_919_);
lean_dec_ref(v_a_905_);
v_snd_920_ = lean_ctor_get(v_a_880_, 1);
lean_inc(v_snd_920_);
lean_dec(v_a_880_);
v_mvarIdPending_921_ = lean_ctor_get(v_val_919_, 1);
lean_inc(v_mvarIdPending_921_);
lean_dec(v_val_919_);
v_mvarId_x27_839_ = v_mvarIdPending_921_;
v_a_840_ = v_snd_920_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_879_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_879_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v_snd_932_; lean_object* v_val_933_; lean_object* v___x_934_; 
lean_dec(v_mvarId_x27_839_);
v_snd_932_ = lean_ctor_get(v_a_852_, 1);
lean_inc(v_snd_932_);
lean_dec(v_a_852_);
v_val_933_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_933_);
lean_dec_ref(v_a_877_);
v___x_934_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_838_, v_val_933_, v_snd_932_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_mvarId_x27_839_);
v_a_936_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_851_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_851_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_mvarId_x27_839_);
v___x_944_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___closed__1));
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_a_840_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_947_, lean_object* v_mvarId_x27_948_, lean_object* v_a_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8(v_mvarId_947_, v_mvarId_x27_948_, v_a_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v_mvarId_947_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object* v_mvarId_960_, lean_object* v_e_961_, lean_object* v_a_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_960_, v_e_961_, v_a_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v_mvarId_960_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_box(0);
v___x_974_ = lean_unsigned_to_nat(16u);
v___x_975_ = lean_mk_array(v___x_974_, v___x_973_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__0);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object* v_mvarId_979_, lean_object* v_e_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_Expr_hasExprMVar(v_e_980_);
if (v___x_990_ == 0)
{
uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref(v_e_980_);
v___x_991_ = 1;
v___x_992_ = lean_box(v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1, &l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___closed__1);
v___x_995_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(v_mvarId_979_, v_e_980_, v___x_994_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1010_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1010_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1010_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_fst_1000_; 
v_fst_1000_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_fst_1000_);
lean_dec(v_a_996_);
if (lean_obj_tag(v_fst_1000_) == 0)
{
uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_dec_ref(v_fst_1000_);
v___x_1001_ = 0;
v___x_1002_ = lean_box(v___x_1001_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1002_);
v___x_1004_ = v___x_998_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_dec_ref(v_fst_1000_);
v___x_1006_ = lean_box(v___x_990_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1006_);
v___x_1008_ = v___x_998_;
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
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_995_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_995_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object* v_mvarId_1019_, lean_object* v_e_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(v_mvarId_1019_, v_e_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v_mvarId_1019_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v_ks_1035_; lean_object* v_vs_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1060_; 
v_ks_1035_ = lean_ctor_get(v_x_1031_, 0);
v_vs_1036_ = lean_ctor_get(v_x_1031_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1038_ = v_x_1031_;
v_isShared_1039_ = v_isSharedCheck_1060_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_vs_1036_);
lean_inc(v_ks_1035_);
lean_dec(v_x_1031_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1060_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_array_get_size(v_ks_1035_);
v___x_1041_ = lean_nat_dec_lt(v_x_1032_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_dec(v_x_1032_);
v___x_1042_ = lean_array_push(v_ks_1035_, v_x_1033_);
v___x_1043_ = lean_array_push(v_vs_1036_, v_x_1034_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1043_);
lean_ctor_set(v___x_1038_, 0, v___x_1042_);
v___x_1045_ = v___x_1038_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v_k_x27_1047_; uint8_t v___x_1048_; 
v_k_x27_1047_ = lean_array_fget_borrowed(v_ks_1035_, v_x_1032_);
v___x_1048_ = l_Lean_instBEqMVarId_beq(v_x_1033_, v_k_x27_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1050_; 
if (v_isShared_1039_ == 0)
{
v___x_1050_ = v___x_1038_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_ks_1035_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_vs_1036_);
v___x_1050_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1u);
v___x_1052_ = lean_nat_add(v_x_1032_, v___x_1051_);
lean_dec(v_x_1032_);
v_x_1031_ = v___x_1050_;
v_x_1032_ = v___x_1052_;
goto _start;
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1055_ = lean_array_fset(v_ks_1035_, v_x_1032_, v_x_1033_);
v___x_1056_ = lean_array_fset(v_vs_1036_, v_x_1032_, v_x_1034_);
lean_dec(v_x_1032_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1056_);
lean_ctor_set(v___x_1038_, 0, v___x_1055_);
v___x_1058_ = v___x_1038_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1061_, lean_object* v_k_1062_, lean_object* v_v_1063_){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1061_, v___x_1064_, v_k_1062_, v_v_1063_);
return v___x_1065_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; 
v___x_1066_ = ((size_t)5ULL);
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_shift_left(v___x_1067_, v___x_1066_);
return v___x_1068_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; 
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1071_ = lean_usize_sub(v___x_1070_, v___x_1069_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(lean_object* v_x_1073_, size_t v_x_1074_, size_t v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
lean_object* v_es_1078_; size_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; lean_object* v_j_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_es_1078_ = lean_ctor_get(v_x_1073_, 0);
v___x_1079_ = ((size_t)5ULL);
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__1);
v___x_1082_ = lean_usize_land(v_x_1074_, v___x_1081_);
v_j_1083_ = lean_usize_to_nat(v___x_1082_);
v___x_1084_ = lean_array_get_size(v_es_1078_);
v___x_1085_ = lean_nat_dec_lt(v_j_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v_j_1083_);
lean_dec(v_x_1077_);
lean_dec(v_x_1076_);
return v_x_1073_;
}
else
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1122_; 
lean_inc_ref(v_es_1078_);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_x_1073_, 0);
lean_dec(v_unused_1123_);
v___x_1087_ = v_x_1073_;
v_isShared_1088_ = v_isSharedCheck_1122_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v_x_1073_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1122_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_v_1089_; lean_object* v___x_1090_; lean_object* v_xs_x27_1091_; lean_object* v___y_1093_; 
v_v_1089_ = lean_array_fget(v_es_1078_, v_j_1083_);
v___x_1090_ = lean_box(0);
v_xs_x27_1091_ = lean_array_fset(v_es_1078_, v_j_1083_, v___x_1090_);
switch(lean_obj_tag(v_v_1089_))
{
case 0:
{
lean_object* v_key_1098_; lean_object* v_val_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1109_; 
v_key_1098_ = lean_ctor_get(v_v_1089_, 0);
v_val_1099_ = lean_ctor_get(v_v_1089_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_v_1089_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1101_ = v_v_1089_;
v_isShared_1102_ = v_isSharedCheck_1109_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_val_1099_);
lean_inc(v_key_1098_);
lean_dec(v_v_1089_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1109_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_instBEqMVarId_beq(v_x_1076_, v_key_1098_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_del_object(v___x_1101_);
v___x_1104_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1098_, v_val_1099_, v_x_1076_, v_x_1077_);
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___y_1093_ = v___x_1105_;
goto v___jp_1092_;
}
else
{
lean_object* v___x_1107_; 
lean_dec(v_val_1099_);
lean_dec(v_key_1098_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_x_1077_);
lean_ctor_set(v___x_1101_, 0, v_x_1076_);
v___x_1107_ = v___x_1101_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_x_1076_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_x_1077_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
v___y_1093_ = v___x_1107_;
goto v___jp_1092_;
}
}
}
}
case 1:
{
lean_object* v_node_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1120_; 
v_node_1110_ = lean_ctor_get(v_v_1089_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_v_1089_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1112_ = v_v_1089_;
v_isShared_1113_ = v_isSharedCheck_1120_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_node_1110_);
lean_dec(v_v_1089_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1120_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
size_t v___x_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1114_ = lean_usize_shift_right(v_x_1074_, v___x_1079_);
v___x_1115_ = lean_usize_add(v_x_1075_, v___x_1080_);
v___x_1116_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_node_1110_, v___x_1114_, v___x_1115_, v_x_1076_, v_x_1077_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1116_);
v___x_1118_ = v___x_1112_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
v___y_1093_ = v___x_1118_;
goto v___jp_1092_;
}
}
}
default: 
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_x_1076_);
lean_ctor_set(v___x_1121_, 1, v_x_1077_);
v___y_1093_ = v___x_1121_;
goto v___jp_1092_;
}
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_array_fset(v_xs_x27_1091_, v_j_1083_, v___y_1093_);
lean_dec(v_j_1083_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1094_);
v___x_1096_ = v___x_1087_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
else
{
lean_object* v_ks_1124_; lean_object* v_vs_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1145_; 
v_ks_1124_ = lean_ctor_get(v_x_1073_, 0);
v_vs_1125_ = lean_ctor_get(v_x_1073_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1127_ = v_x_1073_;
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_vs_1125_);
lean_inc(v_ks_1124_);
lean_dec(v_x_1073_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_ks_1124_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_vs_1125_);
v___x_1130_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v_newNode_1131_; uint8_t v___y_1133_; size_t v___x_1139_; uint8_t v___x_1140_; 
v_newNode_1131_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1130_, v_x_1076_, v_x_1077_);
v___x_1139_ = ((size_t)7ULL);
v___x_1140_ = lean_usize_dec_le(v___x_1139_, v_x_1075_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1141_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1131_);
v___x_1142_ = lean_unsigned_to_nat(4u);
v___x_1143_ = lean_nat_dec_lt(v___x_1141_, v___x_1142_);
lean_dec(v___x_1141_);
v___y_1133_ = v___x_1143_;
goto v___jp_1132_;
}
else
{
v___y_1133_ = v___x_1140_;
goto v___jp_1132_;
}
v___jp_1132_:
{
if (v___y_1133_ == 0)
{
lean_object* v_ks_1134_; lean_object* v_vs_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_ks_1134_ = lean_ctor_get(v_newNode_1131_, 0);
lean_inc_ref(v_ks_1134_);
v_vs_1135_ = lean_ctor_get(v_newNode_1131_, 1);
lean_inc_ref(v_vs_1135_);
lean_dec_ref(v_newNode_1131_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___closed__2);
v___x_1138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1075_, v_ks_1134_, v_vs_1135_, v___x_1136_, v___x_1137_);
lean_dec_ref(v_vs_1135_);
lean_dec_ref(v_ks_1134_);
return v___x_1138_;
}
else
{
return v_newNode_1131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1146_, lean_object* v_keys_1147_, lean_object* v_vals_1148_, lean_object* v_i_1149_, lean_object* v_entries_1150_){
_start:
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = lean_array_get_size(v_keys_1147_);
v___x_1152_ = lean_nat_dec_lt(v_i_1149_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_dec(v_i_1149_);
return v_entries_1150_;
}
else
{
lean_object* v_k_1153_; lean_object* v_v_1154_; uint64_t v___x_1155_; size_t v_h_1156_; size_t v___x_1157_; lean_object* v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v_h_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_k_1153_ = lean_array_fget_borrowed(v_keys_1147_, v_i_1149_);
v_v_1154_ = lean_array_fget_borrowed(v_vals_1148_, v_i_1149_);
v___x_1155_ = l_Lean_instHashableMVarId_hash(v_k_1153_);
v_h_1156_ = lean_uint64_to_usize(v___x_1155_);
v___x_1157_ = ((size_t)5ULL);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = ((size_t)1ULL);
v___x_1160_ = lean_usize_sub(v_depth_1146_, v___x_1159_);
v___x_1161_ = lean_usize_mul(v___x_1157_, v___x_1160_);
v_h_1162_ = lean_usize_shift_right(v_h_1156_, v___x_1161_);
v___x_1163_ = lean_nat_add(v_i_1149_, v___x_1158_);
lean_dec(v_i_1149_);
lean_inc(v_v_1154_);
lean_inc(v_k_1153_);
v___x_1164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_entries_1150_, v_h_1162_, v_depth_1146_, v_k_1153_, v_v_1154_);
v_i_1149_ = v___x_1163_;
v_entries_1150_ = v___x_1164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1166_, lean_object* v_keys_1167_, lean_object* v_vals_1168_, lean_object* v_i_1169_, lean_object* v_entries_1170_){
_start:
{
size_t v_depth_boxed_1171_; lean_object* v_res_1172_; 
v_depth_boxed_1171_ = lean_unbox_usize(v_depth_1166_);
lean_dec(v_depth_1166_);
v_res_1172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1171_, v_keys_1167_, v_vals_1168_, v_i_1169_, v_entries_1170_);
lean_dec_ref(v_vals_1168_);
lean_dec_ref(v_keys_1167_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_){
_start:
{
size_t v_x_79966__boxed_1178_; size_t v_x_79967__boxed_1179_; lean_object* v_res_1180_; 
v_x_79966__boxed_1178_ = lean_unbox_usize(v_x_1174_);
lean_dec(v_x_1174_);
v_x_79967__boxed_1179_ = lean_unbox_usize(v_x_1175_);
lean_dec(v_x_1175_);
v_res_1180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_1173_, v_x_79966__boxed_1178_, v_x_79967__boxed_1179_, v_x_1176_, v_x_1177_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
uint64_t v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1184_ = l_Lean_instHashableMVarId_hash(v_x_1182_);
v___x_1185_ = lean_uint64_to_usize(v___x_1184_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_1181_, v___x_1185_, v___x_1186_, v_x_1182_, v_x_1183_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(lean_object* v_mvarId_1188_, lean_object* v_val_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_mctx_1193_; lean_object* v_cache_1194_; lean_object* v_zetaDeltaFVarIds_1195_; lean_object* v_postponed_1196_; lean_object* v_diag_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1225_; 
v___x_1192_ = lean_st_ref_take(v___y_1190_);
v_mctx_1193_ = lean_ctor_get(v___x_1192_, 0);
v_cache_1194_ = lean_ctor_get(v___x_1192_, 1);
v_zetaDeltaFVarIds_1195_ = lean_ctor_get(v___x_1192_, 2);
v_postponed_1196_ = lean_ctor_get(v___x_1192_, 3);
v_diag_1197_ = lean_ctor_get(v___x_1192_, 4);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1199_ = v___x_1192_;
v_isShared_1200_ = v_isSharedCheck_1225_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_diag_1197_);
lean_inc(v_postponed_1196_);
lean_inc(v_zetaDeltaFVarIds_1195_);
lean_inc(v_cache_1194_);
lean_inc(v_mctx_1193_);
lean_dec(v___x_1192_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1225_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_depth_1201_; lean_object* v_levelAssignDepth_1202_; lean_object* v_lmvarCounter_1203_; lean_object* v_mvarCounter_1204_; lean_object* v_lDecls_1205_; lean_object* v_decls_1206_; lean_object* v_userNames_1207_; lean_object* v_lAssignment_1208_; lean_object* v_eAssignment_1209_; lean_object* v_dAssignment_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1224_; 
v_depth_1201_ = lean_ctor_get(v_mctx_1193_, 0);
v_levelAssignDepth_1202_ = lean_ctor_get(v_mctx_1193_, 1);
v_lmvarCounter_1203_ = lean_ctor_get(v_mctx_1193_, 2);
v_mvarCounter_1204_ = lean_ctor_get(v_mctx_1193_, 3);
v_lDecls_1205_ = lean_ctor_get(v_mctx_1193_, 4);
v_decls_1206_ = lean_ctor_get(v_mctx_1193_, 5);
v_userNames_1207_ = lean_ctor_get(v_mctx_1193_, 6);
v_lAssignment_1208_ = lean_ctor_get(v_mctx_1193_, 7);
v_eAssignment_1209_ = lean_ctor_get(v_mctx_1193_, 8);
v_dAssignment_1210_ = lean_ctor_get(v_mctx_1193_, 9);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_mctx_1193_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1212_ = v_mctx_1193_;
v_isShared_1213_ = v_isSharedCheck_1224_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_dAssignment_1210_);
lean_inc(v_eAssignment_1209_);
lean_inc(v_lAssignment_1208_);
lean_inc(v_userNames_1207_);
lean_inc(v_decls_1206_);
lean_inc(v_lDecls_1205_);
lean_inc(v_mvarCounter_1204_);
lean_inc(v_lmvarCounter_1203_);
lean_inc(v_levelAssignDepth_1202_);
lean_inc(v_depth_1201_);
lean_dec(v_mctx_1193_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1224_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_eAssignment_1209_, v_mvarId_1188_, v_val_1189_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 8, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_depth_1201_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_levelAssignDepth_1202_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_lmvarCounter_1203_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_mvarCounter_1204_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_lDecls_1205_);
lean_ctor_set(v_reuseFailAlloc_1223_, 5, v_decls_1206_);
lean_ctor_set(v_reuseFailAlloc_1223_, 6, v_userNames_1207_);
lean_ctor_set(v_reuseFailAlloc_1223_, 7, v_lAssignment_1208_);
lean_ctor_set(v_reuseFailAlloc_1223_, 8, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1223_, 9, v_dAssignment_1210_);
v___x_1216_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1216_);
v___x_1218_ = v___x_1199_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_cache_1194_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_zetaDeltaFVarIds_1195_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_postponed_1196_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_diag_1197_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_st_ref_set(v___y_1190_, v___x_1218_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg___boxed(lean_object* v_mvarId_1226_, lean_object* v_val_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_1226_, v_val_1227_, v___y_1228_);
lean_dec(v___y_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1239_, uint8_t v_suppressElabErrors_1240_, lean_object* v_x_1241_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 1)
{
lean_object* v_pre_1242_; 
v_pre_1242_ = lean_ctor_get(v_x_1241_, 0);
switch(lean_obj_tag(v_pre_1242_))
{
case 1:
{
lean_object* v_pre_1243_; 
v_pre_1243_ = lean_ctor_get(v_pre_1242_, 0);
switch(lean_obj_tag(v_pre_1243_))
{
case 0:
{
lean_object* v_str_1244_; lean_object* v_str_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_str_1244_ = lean_ctor_get(v_x_1241_, 1);
v_str_1245_ = lean_ctor_get(v_pre_1242_, 1);
v___x_1246_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1247_ = lean_string_dec_eq(v_str_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1249_ = lean_string_dec_eq(v_str_1245_, v___x_1248_);
if (v___x_1249_ == 0)
{
return v___y_1239_;
}
else
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1251_ = lean_string_dec_eq(v_str_1244_, v___x_1250_);
if (v___x_1251_ == 0)
{
return v___y_1239_;
}
else
{
return v_suppressElabErrors_1240_;
}
}
}
else
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1253_ = lean_string_dec_eq(v_str_1244_, v___x_1252_);
if (v___x_1253_ == 0)
{
return v___y_1239_;
}
else
{
return v_suppressElabErrors_1240_;
}
}
}
case 1:
{
lean_object* v_pre_1254_; 
v_pre_1254_ = lean_ctor_get(v_pre_1243_, 0);
if (lean_obj_tag(v_pre_1254_) == 0)
{
lean_object* v_str_1255_; lean_object* v_str_1256_; lean_object* v_str_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_str_1255_ = lean_ctor_get(v_x_1241_, 1);
v_str_1256_ = lean_ctor_get(v_pre_1242_, 1);
v_str_1257_ = lean_ctor_get(v_pre_1243_, 1);
v___x_1258_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1259_ = lean_string_dec_eq(v_str_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
return v___y_1239_;
}
else
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1261_ = lean_string_dec_eq(v_str_1256_, v___x_1260_);
if (v___x_1261_ == 0)
{
return v___y_1239_;
}
else
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1263_ = lean_string_dec_eq(v_str_1255_, v___x_1262_);
if (v___x_1263_ == 0)
{
return v___y_1239_;
}
else
{
return v_suppressElabErrors_1240_;
}
}
}
}
else
{
return v___y_1239_;
}
}
default: 
{
return v___y_1239_;
}
}
}
case 0:
{
lean_object* v_str_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_str_1264_ = lean_ctor_get(v_x_1241_, 1);
v___x_1265_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1266_ = lean_string_dec_eq(v_str_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
return v___y_1239_;
}
else
{
return v_suppressElabErrors_1240_;
}
}
default: 
{
return v___y_1239_;
}
}
}
else
{
return v___y_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1267_, lean_object* v_suppressElabErrors_1268_, lean_object* v_x_1269_){
_start:
{
uint8_t v___y_80201__boxed_1270_; uint8_t v_suppressElabErrors_boxed_1271_; uint8_t v_res_1272_; lean_object* v_r_1273_; 
v___y_80201__boxed_1270_ = lean_unbox(v___y_1267_);
v_suppressElabErrors_boxed_1271_ = lean_unbox(v_suppressElabErrors_1268_);
v_res_1272_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0(v___y_80201__boxed_1270_, v_suppressElabErrors_boxed_1271_, v_x_1269_);
lean_dec(v_x_1269_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1275_, lean_object* v_msgData_1276_, uint8_t v_severity_1277_, uint8_t v_isSilent_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; uint8_t v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1321_; uint8_t v___y_1322_; uint8_t v___y_1323_; lean_object* v___y_1324_; uint8_t v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1346_; uint8_t v___y_1347_; uint8_t v___y_1348_; uint8_t v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1357_; uint8_t v___y_1358_; uint8_t v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; uint8_t v___x_1368_; lean_object* v___y_1370_; uint8_t v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; uint8_t v___y_1375_; uint8_t v___y_1376_; uint8_t v___y_1378_; uint8_t v___x_1393_; 
v___x_1368_ = 2;
v___x_1393_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1277_, v___x_1368_);
if (v___x_1393_ == 0)
{
v___y_1378_ = v___x_1393_;
goto v___jp_1377_;
}
else
{
uint8_t v___x_1394_; 
lean_inc_ref(v_msgData_1276_);
v___x_1394_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1276_);
v___y_1378_ = v___x_1394_;
goto v___jp_1377_;
}
v___jp_1284_:
{
lean_object* v___x_1294_; lean_object* v_currNamespace_1295_; lean_object* v_openDecls_1296_; lean_object* v_env_1297_; lean_object* v_nextMacroScope_1298_; lean_object* v_ngen_1299_; lean_object* v_auxDeclNGen_1300_; lean_object* v_traceState_1301_; lean_object* v_cache_1302_; lean_object* v_messages_1303_; lean_object* v_infoState_1304_; lean_object* v_snapshotTasks_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1319_; 
v___x_1294_ = lean_st_ref_take(v___y_1293_);
v_currNamespace_1295_ = lean_ctor_get(v___y_1292_, 6);
v_openDecls_1296_ = lean_ctor_get(v___y_1292_, 7);
v_env_1297_ = lean_ctor_get(v___x_1294_, 0);
v_nextMacroScope_1298_ = lean_ctor_get(v___x_1294_, 1);
v_ngen_1299_ = lean_ctor_get(v___x_1294_, 2);
v_auxDeclNGen_1300_ = lean_ctor_get(v___x_1294_, 3);
v_traceState_1301_ = lean_ctor_get(v___x_1294_, 4);
v_cache_1302_ = lean_ctor_get(v___x_1294_, 5);
v_messages_1303_ = lean_ctor_get(v___x_1294_, 6);
v_infoState_1304_ = lean_ctor_get(v___x_1294_, 7);
v_snapshotTasks_1305_ = lean_ctor_get(v___x_1294_, 8);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1307_ = v___x_1294_;
v_isShared_1308_ = v_isSharedCheck_1319_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snapshotTasks_1305_);
lean_inc(v_infoState_1304_);
lean_inc(v_messages_1303_);
lean_inc(v_cache_1302_);
lean_inc(v_traceState_1301_);
lean_inc(v_auxDeclNGen_1300_);
lean_inc(v_ngen_1299_);
lean_inc(v_nextMacroScope_1298_);
lean_inc(v_env_1297_);
lean_dec(v___x_1294_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1319_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_inc(v_openDecls_1296_);
lean_inc(v_currNamespace_1295_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_currNamespace_1295_);
lean_ctor_set(v___x_1309_, 1, v_openDecls_1296_);
v___x_1310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___y_1287_);
lean_inc_ref(v___y_1289_);
lean_inc_ref(v___y_1291_);
v___x_1311_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1311_, 0, v___y_1291_);
lean_ctor_set(v___x_1311_, 1, v___y_1290_);
lean_ctor_set(v___x_1311_, 2, v___y_1286_);
lean_ctor_set(v___x_1311_, 3, v___y_1289_);
lean_ctor_set(v___x_1311_, 4, v___x_1310_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5, v___y_1285_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5 + 1, v___y_1288_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5 + 2, v_isSilent_1278_);
v___x_1312_ = l_Lean_MessageLog_add(v___x_1311_, v_messages_1303_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 6, v___x_1312_);
v___x_1314_ = v___x_1307_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_env_1297_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_nextMacroScope_1298_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_ngen_1299_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_auxDeclNGen_1300_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_traceState_1301_);
lean_ctor_set(v_reuseFailAlloc_1318_, 5, v_cache_1302_);
lean_ctor_set(v_reuseFailAlloc_1318_, 6, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1318_, 7, v_infoState_1304_);
lean_ctor_set(v_reuseFailAlloc_1318_, 8, v_snapshotTasks_1305_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_st_ref_set(v___y_1293_, v___x_1314_);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
}
}
v___jp_1320_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1344_; 
v___x_1329_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1276_);
v___x_1330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6_spec__10(v___x_1329_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1344_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_inc_ref_n(v___y_1327_, 2);
v___x_1335_ = l_Lean_FileMap_toPosition(v___y_1327_, v___y_1324_);
lean_dec(v___y_1324_);
v___x_1336_ = l_Lean_FileMap_toPosition(v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___x_1338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1323_ == 0)
{
lean_del_object(v___x_1333_);
lean_dec_ref(v___y_1321_);
v___y_1285_ = v___y_1322_;
v___y_1286_ = v___x_1337_;
v___y_1287_ = v_a_1331_;
v___y_1288_ = v___y_1325_;
v___y_1289_ = v___x_1338_;
v___y_1290_ = v___x_1335_;
v___y_1291_ = v___y_1326_;
v___y_1292_ = v___y_1281_;
v___y_1293_ = v___y_1282_;
goto v___jp_1284_;
}
else
{
uint8_t v___x_1339_; 
lean_inc(v_a_1331_);
v___x_1339_ = l_Lean_MessageData_hasTag(v___y_1321_, v_a_1331_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_dec_ref(v___x_1337_);
lean_dec_ref(v___x_1335_);
lean_dec(v_a_1331_);
v___x_1340_ = lean_box(0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1340_);
v___x_1342_ = v___x_1333_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
else
{
lean_del_object(v___x_1333_);
v___y_1285_ = v___y_1322_;
v___y_1286_ = v___x_1337_;
v___y_1287_ = v_a_1331_;
v___y_1288_ = v___y_1325_;
v___y_1289_ = v___x_1338_;
v___y_1290_ = v___x_1335_;
v___y_1291_ = v___y_1326_;
v___y_1292_ = v___y_1281_;
v___y_1293_ = v___y_1282_;
goto v___jp_1284_;
}
}
}
}
v___jp_1345_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Syntax_getTailPos_x3f(v___y_1350_, v___y_1347_);
lean_dec(v___y_1350_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_inc(v___y_1353_);
v___y_1321_ = v___y_1346_;
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1348_;
v___y_1324_ = v___y_1353_;
v___y_1325_ = v___y_1349_;
v___y_1326_ = v___y_1352_;
v___y_1327_ = v___y_1351_;
v___y_1328_ = v___y_1353_;
goto v___jp_1320_;
}
else
{
lean_object* v_val_1355_; 
v_val_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref(v___x_1354_);
v___y_1321_ = v___y_1346_;
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1348_;
v___y_1324_ = v___y_1353_;
v___y_1325_ = v___y_1349_;
v___y_1326_ = v___y_1352_;
v___y_1327_ = v___y_1351_;
v___y_1328_ = v_val_1355_;
goto v___jp_1320_;
}
}
v___jp_1356_:
{
lean_object* v_ref_1364_; lean_object* v___x_1365_; 
v_ref_1364_ = l_Lean_replaceRef(v_ref_1275_, v___y_1360_);
v___x_1365_ = l_Lean_Syntax_getPos_x3f(v_ref_1364_, v___y_1358_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___y_1346_ = v___y_1357_;
v___y_1347_ = v___y_1358_;
v___y_1348_ = v___y_1359_;
v___y_1349_ = v___y_1363_;
v___y_1350_ = v_ref_1364_;
v___y_1351_ = v___y_1362_;
v___y_1352_ = v___y_1361_;
v___y_1353_ = v___x_1366_;
goto v___jp_1345_;
}
else
{
lean_object* v_val_1367_; 
v_val_1367_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_val_1367_);
lean_dec_ref(v___x_1365_);
v___y_1346_ = v___y_1357_;
v___y_1347_ = v___y_1358_;
v___y_1348_ = v___y_1359_;
v___y_1349_ = v___y_1363_;
v___y_1350_ = v_ref_1364_;
v___y_1351_ = v___y_1362_;
v___y_1352_ = v___y_1361_;
v___y_1353_ = v_val_1367_;
goto v___jp_1345_;
}
}
v___jp_1369_:
{
if (v___y_1376_ == 0)
{
v___y_1357_ = v___y_1370_;
v___y_1358_ = v___y_1375_;
v___y_1359_ = v___y_1371_;
v___y_1360_ = v___y_1372_;
v___y_1361_ = v___y_1374_;
v___y_1362_ = v___y_1373_;
v___y_1363_ = v_severity_1277_;
goto v___jp_1356_;
}
else
{
v___y_1357_ = v___y_1370_;
v___y_1358_ = v___y_1375_;
v___y_1359_ = v___y_1371_;
v___y_1360_ = v___y_1372_;
v___y_1361_ = v___y_1374_;
v___y_1362_ = v___y_1373_;
v___y_1363_ = v___x_1368_;
goto v___jp_1356_;
}
}
v___jp_1377_:
{
if (v___y_1378_ == 0)
{
lean_object* v_fileName_1379_; lean_object* v_fileMap_1380_; lean_object* v_options_1381_; lean_object* v_ref_1382_; uint8_t v_suppressElabErrors_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; uint8_t v___x_1387_; uint8_t v___x_1388_; 
v_fileName_1379_ = lean_ctor_get(v___y_1281_, 0);
v_fileMap_1380_ = lean_ctor_get(v___y_1281_, 1);
v_options_1381_ = lean_ctor_get(v___y_1281_, 2);
v_ref_1382_ = lean_ctor_get(v___y_1281_, 5);
v_suppressElabErrors_1383_ = lean_ctor_get_uint8(v___y_1281_, sizeof(void*)*14 + 1);
v___x_1384_ = lean_box(v___y_1378_);
v___x_1385_ = lean_box(v_suppressElabErrors_1383_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1386_, 0, v___x_1384_);
lean_closure_set(v___f_1386_, 1, v___x_1385_);
v___x_1387_ = 1;
v___x_1388_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1277_, v___x_1387_);
if (v___x_1388_ == 0)
{
v___y_1370_ = v___f_1386_;
v___y_1371_ = v_suppressElabErrors_1383_;
v___y_1372_ = v_ref_1382_;
v___y_1373_ = v_fileMap_1380_;
v___y_1374_ = v_fileName_1379_;
v___y_1375_ = v___y_1378_;
v___y_1376_ = v___x_1388_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = l_Lean_warningAsError;
v___x_1390_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_1381_, v___x_1389_);
v___y_1370_ = v___f_1386_;
v___y_1371_ = v_suppressElabErrors_1383_;
v___y_1372_ = v_ref_1382_;
v___y_1373_ = v_fileMap_1380_;
v___y_1374_ = v_fileName_1379_;
v___y_1375_ = v___y_1378_;
v___y_1376_ = v___x_1390_;
goto v___jp_1369_;
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_msgData_1276_);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1395_, lean_object* v_msgData_1396_, lean_object* v_severity_1397_, lean_object* v_isSilent_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_severity_boxed_1404_; uint8_t v_isSilent_boxed_1405_; lean_object* v_res_1406_; 
v_severity_boxed_1404_ = lean_unbox(v_severity_1397_);
v_isSilent_boxed_1405_ = lean_unbox(v_isSilent_1398_);
v_res_1406_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_1395_, v_msgData_1396_, v_severity_boxed_1404_, v_isSilent_boxed_1405_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v_ref_1395_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(lean_object* v_ref_1407_, lean_object* v_msgData_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = 1;
v___x_1419_ = 0;
v___x_1420_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_1407_, v_msgData_1408_, v___x_1418_, v___x_1419_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7___boxed(lean_object* v_ref_1421_, lean_object* v_msgData_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(v_ref_1421_, v_msgData_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v_ref_1421_);
return v_res_1432_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__0));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__2));
v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(lean_object* v_linterOption_1439_, lean_object* v_stx_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_name_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1466_; 
v_name_1451_ = lean_ctor_get(v_linterOption_1439_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_linterOption_1439_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_linterOption_1439_, 1);
lean_dec(v_unused_1467_);
v___x_1453_ = v_linterOption_1439_;
v_isShared_1454_ = v_isSharedCheck_1466_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_name_1451_);
lean_dec(v_linterOption_1439_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1466_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1455_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__1);
lean_inc(v_name_1451_);
v___x_1456_ = l_Lean_MessageData_ofName(v_name_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set_tag(v___x_1453_, 7);
lean_ctor_set(v___x_1453_, 1, v___x_1456_);
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_disable_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1459_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___closed__3);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v_disable_1461_ = l_Lean_MessageData_note(v___x_1460_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_msg_1441_);
lean_ctor_set(v___x_1462_, 1, v_disable_1461_);
v___x_1463_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_name_1451_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7(v_stx_1440_, v___x_1463_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4___boxed(lean_object* v_linterOption_1468_, lean_object* v_stx_1469_, lean_object* v_msg_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v_linterOption_1468_, v_stx_1469_, v_msg_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_stx_1469_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(lean_object* v_o_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v_env_1485_; lean_object* v___x_1486_; lean_object* v_toEnvExtension_1487_; lean_object* v_asyncMode_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_linterSets_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1484_ = lean_st_ref_get(v___y_1482_);
v_env_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc_ref(v_env_1485_);
lean_dec(v___x_1484_);
v___x_1486_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1487_ = lean_ctor_get(v___x_1486_, 0);
v_asyncMode_1488_ = lean_ctor_get(v_toEnvExtension_1487_, 2);
v___x_1489_ = lean_box(1);
v___x_1490_ = lean_box(0);
v_linterSets_1491_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1489_, v___x_1486_, v_env_1485_, v_asyncMode_1488_, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_o_1481_);
lean_ctor_set(v___x_1492_, 1, v_linterSets_1491_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg___boxed(lean_object* v_o_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_o_1494_, v___y_1495_);
lean_dec(v___y_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_options_1507_; lean_object* v___x_1508_; 
v_options_1507_ = lean_ctor_get(v___y_1504_, 2);
lean_inc_ref(v_options_1507_);
v___x_1508_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_options_1507_, v___y_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(lean_object* v___y_1519_, lean_object* v_mkInfoTree_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v_a_1528_, lean_object* v_a_x3f_1529_){
_start:
{
lean_object* v___x_1531_; lean_object* v_infoState_1532_; lean_object* v_trees_1533_; lean_object* v___x_1534_; 
v___x_1531_ = lean_st_ref_get(v___y_1519_);
v_infoState_1532_ = lean_ctor_get(v___x_1531_, 7);
lean_inc_ref(v_infoState_1532_);
lean_dec(v___x_1531_);
v_trees_1533_ = lean_ctor_get(v_infoState_1532_, 2);
lean_inc_ref(v_trees_1533_);
lean_dec_ref(v_infoState_1532_);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1527_);
lean_inc(v___y_1526_);
lean_inc_ref(v___y_1525_);
lean_inc(v___y_1524_);
lean_inc_ref(v___y_1523_);
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
v___x_1534_ = lean_apply_10(v_mkInfoTree_1520_, v_trees_1533_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1519_, lean_box(0));
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1573_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1573_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1573_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v_infoState_1540_; lean_object* v_env_1541_; lean_object* v_nextMacroScope_1542_; lean_object* v_ngen_1543_; lean_object* v_auxDeclNGen_1544_; lean_object* v_traceState_1545_; lean_object* v_cache_1546_; lean_object* v_messages_1547_; lean_object* v_snapshotTasks_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1572_; 
v___x_1539_ = lean_st_ref_take(v___y_1519_);
v_infoState_1540_ = lean_ctor_get(v___x_1539_, 7);
v_env_1541_ = lean_ctor_get(v___x_1539_, 0);
v_nextMacroScope_1542_ = lean_ctor_get(v___x_1539_, 1);
v_ngen_1543_ = lean_ctor_get(v___x_1539_, 2);
v_auxDeclNGen_1544_ = lean_ctor_get(v___x_1539_, 3);
v_traceState_1545_ = lean_ctor_get(v___x_1539_, 4);
v_cache_1546_ = lean_ctor_get(v___x_1539_, 5);
v_messages_1547_ = lean_ctor_get(v___x_1539_, 6);
v_snapshotTasks_1548_ = lean_ctor_get(v___x_1539_, 8);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1550_ = v___x_1539_;
v_isShared_1551_ = v_isSharedCheck_1572_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_snapshotTasks_1548_);
lean_inc(v_infoState_1540_);
lean_inc(v_messages_1547_);
lean_inc(v_cache_1546_);
lean_inc(v_traceState_1545_);
lean_inc(v_auxDeclNGen_1544_);
lean_inc(v_ngen_1543_);
lean_inc(v_nextMacroScope_1542_);
lean_inc(v_env_1541_);
lean_dec(v___x_1539_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1572_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
uint8_t v_enabled_1552_; lean_object* v_assignment_1553_; lean_object* v_lazyAssignment_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1570_; 
v_enabled_1552_ = lean_ctor_get_uint8(v_infoState_1540_, sizeof(void*)*3);
v_assignment_1553_ = lean_ctor_get(v_infoState_1540_, 0);
v_lazyAssignment_1554_ = lean_ctor_get(v_infoState_1540_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_infoState_1540_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_infoState_1540_, 2);
lean_dec(v_unused_1571_);
v___x_1556_ = v_infoState_1540_;
v_isShared_1557_ = v_isSharedCheck_1570_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_lazyAssignment_1554_);
lean_inc(v_assignment_1553_);
lean_dec(v_infoState_1540_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1570_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = l_Lean_PersistentArray_push___redArg(v_a_1528_, v_a_1535_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 2, v___x_1558_);
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_assignment_1553_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_lazyAssignment_1554_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v___x_1558_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*3, v_enabled_1552_);
v___x_1560_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 7, v___x_1560_);
v___x_1562_ = v___x_1550_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_env_1541_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_nextMacroScope_1542_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_ngen_1543_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v_auxDeclNGen_1544_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v_traceState_1545_);
lean_ctor_set(v_reuseFailAlloc_1568_, 5, v_cache_1546_);
lean_ctor_set(v_reuseFailAlloc_1568_, 6, v_messages_1547_);
lean_ctor_set(v_reuseFailAlloc_1568_, 7, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1568_, 8, v_snapshotTasks_1548_);
v___x_1562_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1563_ = lean_st_ref_set(v___y_1519_, v___x_1562_);
v___x_1564_ = lean_box(0);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1564_);
v___x_1566_ = v___x_1537_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_a_1528_);
v_a_1574_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1534_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1534_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0___boxed(lean_object* v___y_1582_, lean_object* v_mkInfoTree_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v_a_1591_, lean_object* v_a_x3f_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1582_, v_mkInfoTree_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v_a_1591_, v_a_x3f_1592_);
lean_dec(v_a_x3f_1592_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1582_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(lean_object* v_x_1595_, lean_object* v_mkInfoTree_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v_infoState_1607_; uint8_t v_enabled_1608_; 
v___x_1606_ = lean_st_ref_get(v___y_1604_);
v_infoState_1607_ = lean_ctor_get(v___x_1606_, 7);
lean_inc_ref(v_infoState_1607_);
lean_dec(v___x_1606_);
v_enabled_1608_ = lean_ctor_get_uint8(v_infoState_1607_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1607_);
if (v_enabled_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref(v_mkInfoTree_1596_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
v___x_1609_ = lean_apply_9(v_x_1595_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, lean_box(0));
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; lean_object* v_a_1611_; lean_object* v_r_1612_; 
v___x_1610_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_1604_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1610_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
v_r_1612_ = lean_apply_9(v_x_1595_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, lean_box(0));
if (lean_obj_tag(v_r_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1637_; 
v_a_1613_ = lean_ctor_get(v_r_1612_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_r_1612_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1615_ = v_r_1612_;
v_isShared_1616_ = v_isSharedCheck_1637_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v_r_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1637_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
lean_inc(v_a_1613_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 1);
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1604_, v_mkInfoTree_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v_a_1611_, v___x_1618_);
lean_dec_ref(v___x_1618_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1619_, 0);
lean_dec(v_unused_1627_);
v___x_1621_ = v___x_1619_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_dec(v___x_1619_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_a_1613_);
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1613_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec(v_a_1613_);
v_a_1628_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1619_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1619_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_a_1638_ = lean_ctor_get(v_r_1612_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v_r_1612_);
v___x_1639_ = lean_box(0);
v___x_1640_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___lam__0(v___y_1604_, v_mkInfoTree_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v_a_1611_, v___x_1639_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v___x_1640_, 0);
lean_dec(v_unused_1648_);
v___x_1642_ = v___x_1640_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_dec(v___x_1640_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
lean_ctor_set(v___x_1642_, 0, v_a_1638_);
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1638_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1638_);
v_a_1649_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1640_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1640_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg___boxed(lean_object* v_x_1657_, lean_object* v_mkInfoTree_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v_x_1657_, v_mkInfoTree_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1668_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__4));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__6));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__8));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__10));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object* v_usingArg_1690_, lean_object* v_snd_1691_, uint8_t v___x_1692_, uint8_t v___x_1693_, uint8_t v___x_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v___x_1697_, lean_object* v_simprocs_1698_, lean_object* v_discharge_x3f_1699_, lean_object* v_snd_1700_, lean_object* v___x_1701_, lean_object* v___f_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; 
if (lean_obj_tag(v_usingArg_1690_) == 1)
{
lean_object* v_val_1892_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___x_1944_; lean_object* v_infoState_1945_; uint8_t v_enabled_1946_; 
v_val_1892_ = lean_ctor_get(v_usingArg_1690_, 0);
lean_inc(v_val_1892_);
lean_dec_ref(v_usingArg_1690_);
v___x_1944_ = lean_st_ref_get(v___y_1710_);
v_infoState_1945_ = lean_ctor_get(v___x_1944_, 7);
lean_inc_ref(v_infoState_1945_);
lean_dec(v___x_1944_);
v_enabled_1946_ = lean_ctor_get_uint8(v_infoState_1945_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1945_);
if (v_enabled_1946_ == 0)
{
lean_dec_ref(v___f_1702_);
v___y_1894_ = v___y_1703_;
v___y_1895_ = v___y_1704_;
v___y_1896_ = v___y_1705_;
v___y_1897_ = v___y_1706_;
v___y_1898_ = v___y_1707_;
v___y_1899_ = v___y_1708_;
v___y_1900_ = v___y_1709_;
v___y_1901_ = v___y_1710_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1947_; lean_object* v_a_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; 
v___x_1947_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__7___redArg(v___y_1710_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___f_1949_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1949_, 0, v_a_1948_);
v___x_1950_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v___f_1949_, v___f_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_dec_ref(v___x_1950_);
v___y_1894_ = v___y_1703_;
v___y_1895_ = v___y_1704_;
v___y_1896_ = v___y_1705_;
v___y_1897_ = v___y_1706_;
v___y_1898_ = v___y_1707_;
v___y_1899_ = v___y_1708_;
v___y_1900_ = v___y_1709_;
v___y_1901_ = v___y_1710_;
goto v___jp_1893_;
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v_val_1892_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
v___jp_1893_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_st_ref_get(v___y_1899_);
v___x_1903_ = lean_box(0);
v___x_1904_ = l_Lean_Elab_Tactic_elabTerm(v_val_1892_, v___x_1903_, v___x_1692_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc_n(v_a_1905_, 2);
lean_dec_ref(v___x_1904_);
v___x_1906_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(v_snd_1691_, v_a_1905_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_mctx_1907_; lean_object* v_a_1908_; uint8_t v___x_1909_; 
v_mctx_1907_ = lean_ctor_get(v___x_1902_, 0);
lean_inc_ref(v_mctx_1907_);
lean_dec(v___x_1902_);
v_a_1908_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1906_);
v___x_1909_ = lean_unbox(v_a_1908_);
lean_dec(v_a_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec_ref(v_mctx_1907_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
v___x_1910_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__9);
v___x_1911_ = l_Lean_indentExpr(v_a_1905_);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__11);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = l_Lean_Expr_mvar___override(v_snd_1691_);
v___x_1916_ = l_Lean_MessageData_ofExpr(v___x_1915_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1914_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v___x_1917_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
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
else
{
lean_object* v_mvarCounter_1927_; 
v_mvarCounter_1927_ = lean_ctor_get(v_mctx_1907_, 3);
lean_inc(v_mvarCounter_1927_);
lean_dec_ref(v_mctx_1907_);
lean_inc(v_a_1905_);
v___y_1776_ = v_mvarCounter_1927_;
v___y_1777_ = v___x_1903_;
v___y_1778_ = v_a_1905_;
v___y_1779_ = v_a_1905_;
v___y_1780_ = v___x_1903_;
v___y_1781_ = v___y_1894_;
v___y_1782_ = v___y_1895_;
v___y_1783_ = v___y_1896_;
v___y_1784_ = v___y_1897_;
v___y_1785_ = v___y_1898_;
v___y_1786_ = v___y_1899_;
v___y_1787_ = v___y_1900_;
v___y_1788_ = v___y_1901_;
goto v___jp_1775_;
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1905_);
lean_dec(v___x_1902_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1928_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1906_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1906_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v___x_1902_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1936_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1904_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1904_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
else
{
lean_object* v_lctx_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec_ref(v___f_1702_);
lean_dec_ref(v___x_1695_);
lean_dec(v_usingArg_1690_);
v_lctx_1959_ = lean_ctor_get(v___y_1707_, 2);
v___x_1960_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__13));
v___x_1961_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_1959_, v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 1)
{
lean_object* v_val_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_val_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_val_1962_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = l_Lean_LocalDecl_fvarId(v_val_1962_);
lean_dec(v_val_1962_);
v___x_1964_ = lean_mk_empty_array_with_capacity(v___x_1696_);
v___x_1965_ = lean_array_push(v___x_1964_, v___x_1963_);
lean_inc_ref(v_snd_1700_);
v___x_1966_ = l_Lean_Meta_simpGoal(v_snd_1691_, v___x_1697_, v_simprocs_1698_, v_discharge_x3f_1699_, v___x_1693_, v___x_1965_, v_snd_1700_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1995_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1995_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1995_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_fst_1971_; 
v_fst_1971_ = lean_ctor_get(v_a_1967_, 0);
if (lean_obj_tag(v_fst_1971_) == 1)
{
lean_object* v_val_1972_; lean_object* v_snd_1973_; lean_object* v_snd_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1969_);
lean_dec_ref(v_snd_1700_);
v_val_1972_ = lean_ctor_get(v_fst_1971_, 0);
lean_inc(v_val_1972_);
v_snd_1973_ = lean_ctor_get(v_a_1967_, 1);
lean_inc(v_snd_1973_);
lean_dec(v_a_1967_);
v_snd_1974_ = lean_ctor_get(v_val_1972_, 1);
lean_inc(v_snd_1974_);
lean_dec(v_val_1972_);
v___x_1975_ = l_Lean_MVarId_assumption(v_snd_1974_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1975_, 0);
lean_dec(v_unused_1983_);
v___x_1977_ = v___x_1975_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v___x_1975_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_snd_1973_);
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_snd_1973_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_snd_1973_);
v_a_1984_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1975_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1975_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v___x_1993_; 
lean_dec(v_a_1967_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v_snd_1700_);
v___x_1993_ = v___x_1969_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_snd_1700_);
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
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_snd_1700_);
v_a_1996_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1966_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1966_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v___x_1961_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
v___x_2004_ = l_Lean_MVarId_assumption(v_snd_1691_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v___x_2004_, 0);
lean_dec(v_unused_2012_);
v___x_2006_ = v___x_2004_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v___x_2004_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v_snd_1700_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_snd_1700_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_snd_1700_);
v_a_2013_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2004_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2004_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
v___jp_1712_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v___x_1716_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_snd_1691_, v___y_1713_, v___y_1715_);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v___x_1716_, 0);
lean_dec(v_unused_1724_);
v___x_1718_ = v___x_1716_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_dec(v___x_1716_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___y_1714_);
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___y_1714_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
v___jp_1725_:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Core_mkFreshUserName(v___y_1739_, v___y_1737_, v___y_1740_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc_n(v_a_1743_, 2);
lean_dec_ref(v___x_1742_);
v___x_1744_ = l_Lean_MVarId_rename(v___y_1729_, v___y_1741_, v_a_1743_, v___y_1731_, v___y_1735_, v___y_1737_, v___y_1740_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc_n(v_a_1745_, 2);
lean_dec_ref(v___x_1744_);
v___x_1746_ = lean_box(v___x_1692_);
v___x_1747_ = lean_box(v___x_1693_);
v___x_1748_ = lean_box(v___x_1694_);
v___f_1749_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1749_, 0, v_a_1745_);
lean_closure_set(v___f_1749_, 1, v_a_1743_);
lean_closure_set(v___f_1749_, 2, v___x_1746_);
lean_closure_set(v___f_1749_, 3, v___x_1747_);
lean_closure_set(v___f_1749_, 4, v___x_1748_);
lean_closure_set(v___f_1749_, 5, v___y_1728_);
lean_closure_set(v___f_1749_, 6, v___y_1726_);
lean_closure_set(v___f_1749_, 7, v___x_1695_);
lean_closure_set(v___f_1749_, 8, v___y_1727_);
v___x_1750_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_a_1745_, v___f_1749_, v___y_1730_, v___y_1732_, v___y_1738_, v___y_1733_, v___y_1731_, v___y_1735_, v___y_1737_, v___y_1740_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_dec_ref(v___x_1750_);
v___y_1713_ = v___y_1734_;
v___y_1714_ = v___y_1736_;
v___y_1715_ = v___y_1735_;
goto v___jp_1712_;
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec_ref(v___y_1736_);
lean_dec_ref(v___y_1734_);
lean_dec(v_snd_1691_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
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
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
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
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_a_1743_);
lean_dec_ref(v___y_1736_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1759_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1744_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1744_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1736_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1767_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1742_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1742_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
v___jp_1775_:
{
lean_object* v___x_1789_; 
lean_inc(v_snd_1691_);
v___x_1789_ = l_Lean_MVarId_getType(v_snd_1691_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1791_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
lean_inc(v_snd_1691_);
v___x_1791_ = l_Lean_MVarId_getTag(v_snd_1691_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1790_, v_a_1792_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = l_Lean_Expr_mvarId_x21(v_a_1794_);
v___x_1796_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1));
lean_inc_ref(v___y_1779_);
v___x_1797_ = l_Lean_MVarId_note(v___x_1795_, v___x_1796_, v___y_1779_, v___y_1780_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1859_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1797_);
v_fst_1799_ = lean_ctor_get(v_a_1798_, 0);
v_snd_1800_ = lean_ctor_get(v_a_1798_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1802_ = v_a_1798_;
v_isShared_1803_ = v_isSharedCheck_1859_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_snd_1800_);
lean_inc(v_fst_1799_);
lean_dec(v_a_1798_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1859_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_mk_empty_array_with_capacity(v___x_1696_);
lean_inc(v_fst_1799_);
v___x_1805_ = lean_array_push(v___x_1804_, v_fst_1799_);
v___x_1806_ = l_Lean_Meta_simpGoal(v_snd_1800_, v___x_1697_, v_simprocs_1698_, v_discharge_x3f_1699_, v___x_1693_, v___x_1805_, v_snd_1700_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v_fst_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref(v___x_1806_);
v_fst_1808_ = lean_ctor_get(v_a_1807_, 0);
if (lean_obj_tag(v_fst_1808_) == 0)
{
lean_object* v_snd_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1842_; 
lean_dec(v_fst_1799_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___x_1695_);
v_snd_1809_ = lean_ctor_get(v_a_1807_, 1);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_a_1807_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v_a_1807_, 0);
lean_dec(v_unused_1843_);
v___x_1811_ = v_a_1807_;
v_isShared_1812_ = v_isSharedCheck_1842_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_snd_1809_);
lean_dec(v_a_1807_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1842_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v_a_1814_; uint8_t v___x_1815_; 
v___x_1813_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1814_);
lean_dec(v_a_1814_);
if (v___x_1815_ == 0)
{
lean_del_object(v___x_1811_);
lean_del_object(v___x_1802_);
lean_dec_ref(v___y_1779_);
v___y_1713_ = v_a_1794_;
v___y_1714_ = v_snd_1809_;
v___y_1715_ = v___y_1786_;
goto v___jp_1712_;
}
else
{
if (lean_obj_tag(v___y_1779_) == 1)
{
lean_object* v_fvarId_1816_; lean_object* v_lctx_1817_; lean_object* v___x_1818_; 
v_fvarId_1816_ = lean_ctor_get(v___y_1779_, 0);
v_lctx_1817_ = lean_ctor_get(v___y_1785_, 2);
lean_inc(v_fvarId_1816_);
lean_inc_ref(v_lctx_1817_);
v___x_1818_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1817_, v_fvarId_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_dec_ref(v___y_1779_);
lean_del_object(v___x_1811_);
lean_del_object(v___x_1802_);
v___y_1713_ = v_a_1794_;
v___y_1714_ = v_snd_1809_;
v___y_1715_ = v___y_1786_;
goto v___jp_1712_;
}
else
{
lean_dec_ref(v___x_1818_);
if (v___x_1694_ == 0)
{
lean_dec_ref(v___y_1779_);
lean_del_object(v___x_1811_);
lean_del_object(v___x_1802_);
v___y_1713_ = v_a_1794_;
v___y_1714_ = v_snd_1809_;
v___y_1715_ = v___y_1786_;
goto v___jp_1712_;
}
else
{
lean_object* v_ref_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v_ref_1819_ = lean_ctor_get(v___y_1787_, 5);
v___x_1820_ = l_linter_unnecessarySimpa;
v___x_1821_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3);
v___x_1822_ = l_Lean_MessageData_ofExpr(v___y_1779_);
lean_inc_ref(v___x_1822_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 7);
lean_ctor_set(v___x_1811_, 1, v___x_1822_);
lean_ctor_set(v___x_1811_, 0, v___x_1821_);
v___x_1824_ = v___x_1811_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__5);
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 7);
lean_ctor_set(v___x_1802_, 1, v___x_1825_);
lean_ctor_set(v___x_1802_, 0, v___x_1824_);
v___x_1827_ = v___x_1802_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1822_);
v___x_1829_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__7);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v___x_1820_, v_ref_1819_, v___x_1830_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref(v___x_1831_);
v___y_1713_ = v_a_1794_;
v___y_1714_ = v_snd_1809_;
v___y_1715_ = v___y_1786_;
goto v___jp_1712_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_snd_1809_);
lean_dec(v_a_1794_);
lean_dec(v_snd_1691_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
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
lean_del_object(v___x_1811_);
lean_del_object(v___x_1802_);
lean_dec_ref(v___y_1779_);
v___y_1713_ = v_a_1794_;
v___y_1714_ = v_snd_1809_;
v___y_1715_ = v___y_1786_;
goto v___jp_1712_;
}
}
}
}
else
{
lean_object* v_val_1844_; lean_object* v_snd_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
lean_del_object(v___x_1802_);
lean_dec_ref(v___y_1779_);
v_val_1844_ = lean_ctor_get(v_fst_1808_, 0);
lean_inc(v_val_1844_);
v_snd_1845_ = lean_ctor_get(v_a_1807_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_a_1807_);
v_fst_1846_ = lean_ctor_get(v_val_1844_, 0);
lean_inc(v_fst_1846_);
v_snd_1847_ = lean_ctor_get(v_val_1844_, 1);
lean_inc(v_snd_1847_);
lean_dec(v_val_1844_);
v___x_1848_ = lean_array_get_size(v_fst_1846_);
v___x_1849_ = lean_nat_dec_lt(v___x_1701_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec(v_fst_1846_);
v___y_1726_ = v___y_1776_;
v___y_1727_ = v___y_1777_;
v___y_1728_ = v___y_1778_;
v___y_1729_ = v_snd_1847_;
v___y_1730_ = v___y_1781_;
v___y_1731_ = v___y_1785_;
v___y_1732_ = v___y_1782_;
v___y_1733_ = v___y_1784_;
v___y_1734_ = v_a_1794_;
v___y_1735_ = v___y_1786_;
v___y_1736_ = v_snd_1845_;
v___y_1737_ = v___y_1787_;
v___y_1738_ = v___y_1783_;
v___y_1739_ = v___x_1796_;
v___y_1740_ = v___y_1788_;
v___y_1741_ = v_fst_1799_;
goto v___jp_1725_;
}
else
{
lean_object* v___x_1850_; 
lean_dec(v_fst_1799_);
v___x_1850_ = lean_array_fget(v_fst_1846_, v___x_1701_);
lean_dec(v_fst_1846_);
v___y_1726_ = v___y_1776_;
v___y_1727_ = v___y_1777_;
v___y_1728_ = v___y_1778_;
v___y_1729_ = v_snd_1847_;
v___y_1730_ = v___y_1781_;
v___y_1731_ = v___y_1785_;
v___y_1732_ = v___y_1782_;
v___y_1733_ = v___y_1784_;
v___y_1734_ = v_a_1794_;
v___y_1735_ = v___y_1786_;
v___y_1736_ = v_snd_1845_;
v___y_1737_ = v___y_1787_;
v___y_1738_ = v___y_1783_;
v___y_1739_ = v___x_1796_;
v___y_1740_ = v___y_1788_;
v___y_1741_ = v___x_1850_;
goto v___jp_1725_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_del_object(v___x_1802_);
lean_dec(v_fst_1799_);
lean_dec(v_a_1794_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1851_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1806_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1806_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_a_1794_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1860_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1797_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1797_);
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
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1868_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1793_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1793_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_a_1790_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1876_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1791_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1791_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v_snd_1700_);
lean_dec(v_discharge_x3f_1699_);
lean_dec_ref(v_simprocs_1698_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1695_);
lean_dec(v_snd_1691_);
v_a_1884_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1789_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1789_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2021_ = _args[0];
lean_object* v_snd_2022_ = _args[1];
lean_object* v___x_2023_ = _args[2];
lean_object* v___x_2024_ = _args[3];
lean_object* v___x_2025_ = _args[4];
lean_object* v___x_2026_ = _args[5];
lean_object* v___x_2027_ = _args[6];
lean_object* v___x_2028_ = _args[7];
lean_object* v_simprocs_2029_ = _args[8];
lean_object* v_discharge_x3f_2030_ = _args[9];
lean_object* v_snd_2031_ = _args[10];
lean_object* v___x_2032_ = _args[11];
lean_object* v___f_2033_ = _args[12];
lean_object* v___y_2034_ = _args[13];
lean_object* v___y_2035_ = _args[14];
lean_object* v___y_2036_ = _args[15];
lean_object* v___y_2037_ = _args[16];
lean_object* v___y_2038_ = _args[17];
lean_object* v___y_2039_ = _args[18];
lean_object* v___y_2040_ = _args[19];
lean_object* v___y_2041_ = _args[20];
lean_object* v___y_2042_ = _args[21];
_start:
{
uint8_t v___x_80914__boxed_2043_; uint8_t v___x_80915__boxed_2044_; uint8_t v___x_80916__boxed_2045_; lean_object* v_res_2046_; 
v___x_80914__boxed_2043_ = lean_unbox(v___x_2023_);
v___x_80915__boxed_2044_ = lean_unbox(v___x_2024_);
v___x_80916__boxed_2045_ = lean_unbox(v___x_2025_);
v_res_2046_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(v_usingArg_2021_, v_snd_2022_, v___x_80914__boxed_2043_, v___x_80915__boxed_2044_, v___x_80916__boxed_2045_, v___x_2026_, v___x_2027_, v___x_2028_, v_simprocs_2029_, v_discharge_x3f_2030_, v_snd_2031_, v___x_2032_, v___f_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___x_2032_);
lean_dec(v___x_2027_);
return v_res_2046_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2047_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_unsigned_to_nat(32u);
v___x_2051_ = lean_mk_empty_array_with_capacity(v___x_2050_);
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4));
v___x_2057_ = l_Lean_MessageData_ofFormat(v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object* v___x_2058_, lean_object* v_tk_2059_, lean_object* v___x_2060_, lean_object* v___x_2061_, lean_object* v___x_2062_, lean_object* v_simprocs_2063_, uint8_t v___x_2064_, lean_object* v_usingArg_2065_, uint8_t v___x_2066_, uint8_t v___x_2067_, lean_object* v___x_2068_, lean_object* v___x_2069_, lean_object* v_usingTk_x3f_2070_, lean_object* v_discharge_x3f_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___y_2082_; 
if (lean_obj_tag(v_usingTk_x3f_2070_) == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_box(0);
v___y_2082_ = v___x_2186_;
goto v___jp_2081_;
}
else
{
lean_object* v_val_2187_; 
v_val_2187_ = lean_ctor_get(v_usingTk_x3f_2070_, 0);
lean_inc(v_val_2187_);
lean_dec_ref(v_usingTk_x3f_2070_);
v___y_2082_ = v_val_2187_;
goto v___jp_2081_;
}
v___jp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2083_ = lean_mk_empty_array_with_capacity(v___x_2058_);
v___x_2084_ = lean_array_push(v___x_2083_, v_tk_2059_);
v___x_2085_ = lean_array_push(v___x_2084_, v___y_2082_);
v___x_2086_ = lean_box(2);
v___x_2087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2060_);
lean_ctor_set(v___x_2087_, 2, v___x_2085_);
v___x_2088_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2087_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2073_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = lean_mk_empty_array_with_capacity(v___x_2061_);
v___x_2093_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1);
lean_inc_n(v___x_2061_, 3);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___x_2061_);
v___x_2095_ = lean_unsigned_to_nat(32u);
v___x_2096_ = lean_mk_empty_array_with_capacity(v___x_2095_);
v___x_2097_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2);
v___x_2098_ = ((size_t)5ULL);
v___x_2099_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2096_);
lean_ctor_set(v___x_2099_, 2, v___x_2061_);
lean_ctor_set(v___x_2099_, 3, v___x_2061_);
lean_ctor_set_usize(v___x_2099_, 4, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2093_);
lean_ctor_set(v___x_2100_, 1, v___x_2093_);
lean_ctor_set(v___x_2100_, 2, v___x_2093_);
lean_ctor_set(v___x_2100_, 3, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2094_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
lean_inc_ref(v___x_2101_);
lean_inc(v_discharge_x3f_2071_);
lean_inc_ref(v_simprocs_2063_);
lean_inc_ref(v___x_2062_);
v___x_2102_ = l_Lean_Meta_simpGoal(v_a_2091_, v___x_2062_, v_simprocs_2063_, v_discharge_x3f_2071_, v___x_2064_, v___x_2092_, v___x_2101_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v_fst_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2102_);
v_fst_2104_ = lean_ctor_get(v_a_2103_, 0);
if (lean_obj_tag(v_fst_2104_) == 1)
{
lean_object* v_val_2105_; lean_object* v_snd_2106_; lean_object* v_snd_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v___x_2101_);
v_val_2105_ = lean_ctor_get(v_fst_2104_, 0);
lean_inc(v_val_2105_);
v_snd_2106_ = lean_ctor_get(v_a_2103_, 1);
lean_inc(v_snd_2106_);
lean_dec(v_a_2103_);
v_snd_2107_ = lean_ctor_get(v_val_2105_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_val_2105_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_val_2105_, 0);
lean_dec(v_unused_2131_);
v___x_2109_ = v_val_2105_;
v_isShared_2110_ = v_isSharedCheck_2130_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_snd_2107_);
lean_dec(v_val_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2130_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_box(0);
lean_inc(v_snd_2107_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 1);
lean_ctor_set(v___x_2109_, 1, v___x_2111_);
lean_ctor_set(v___x_2109_, 0, v_snd_2107_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_snd_2107_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2113_, v___y_2073_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___y_2119_; lean_object* v___x_2120_; 
lean_dec_ref(v___x_2114_);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2115_, 0, v_a_2089_);
v___x_2116_ = lean_box(v___x_2064_);
v___x_2117_ = lean_box(v___x_2066_);
v___x_2118_ = lean_box(v___x_2067_);
lean_inc(v_snd_2107_);
v___y_2119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 22, 13);
lean_closure_set(v___y_2119_, 0, v_usingArg_2065_);
lean_closure_set(v___y_2119_, 1, v_snd_2107_);
lean_closure_set(v___y_2119_, 2, v___x_2116_);
lean_closure_set(v___y_2119_, 3, v___x_2117_);
lean_closure_set(v___y_2119_, 4, v___x_2118_);
lean_closure_set(v___y_2119_, 5, v___x_2068_);
lean_closure_set(v___y_2119_, 6, v___x_2069_);
lean_closure_set(v___y_2119_, 7, v___x_2062_);
lean_closure_set(v___y_2119_, 8, v_simprocs_2063_);
lean_closure_set(v___y_2119_, 9, v_discharge_x3f_2071_);
lean_closure_set(v___y_2119_, 10, v_snd_2106_);
lean_closure_set(v___y_2119_, 11, v___x_2061_);
lean_closure_set(v___y_2119_, 12, v___f_2115_);
v___x_2120_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___redArg(v_snd_2107_, v___y_2119_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
return v___x_2120_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_snd_2107_);
lean_dec(v_snd_2106_);
lean_dec(v_a_2089_);
lean_dec(v_discharge_x3f_2071_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2068_);
lean_dec(v_usingArg_2065_);
lean_dec_ref(v_simprocs_2063_);
lean_dec_ref(v___x_2062_);
lean_dec(v___x_2061_);
v_a_2121_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2114_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2114_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_2103_);
lean_dec(v_a_2089_);
lean_dec(v_discharge_x3f_2071_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2068_);
lean_dec(v_usingArg_2065_);
lean_dec_ref(v_simprocs_2063_);
lean_dec_ref(v___x_2062_);
lean_dec(v___x_2061_);
v___x_2132_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2161_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2161_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
uint8_t v___x_2137_; 
v___x_2137_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2133_);
lean_dec(v_a_2133_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2139_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2101_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2101_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
else
{
lean_object* v_ref_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_del_object(v___x_2135_);
v_ref_2141_ = lean_ctor_get(v___y_2078_, 5);
v___x_2142_ = l_linter_unnecessarySimpa;
v___x_2143_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5);
v___x_2144_ = l_Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4(v___x_2142_, v_ref_2141_, v___x_2143_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2144_, 0);
lean_dec(v_unused_2152_);
v___x_2146_ = v___x_2144_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v___x_2144_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2101_);
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2101_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v___x_2101_);
v_a_2153_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2144_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v___x_2101_);
lean_dec(v_a_2089_);
lean_dec(v_discharge_x3f_2071_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2068_);
lean_dec(v_usingArg_2065_);
lean_dec_ref(v_simprocs_2063_);
lean_dec_ref(v___x_2062_);
lean_dec(v___x_2061_);
v_a_2162_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2102_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2102_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2089_);
lean_dec(v_discharge_x3f_2071_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2068_);
lean_dec(v_usingArg_2065_);
lean_dec_ref(v_simprocs_2063_);
lean_dec_ref(v___x_2062_);
lean_dec(v___x_2061_);
v_a_2170_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2090_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2090_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_discharge_x3f_2071_);
lean_dec(v___x_2069_);
lean_dec_ref(v___x_2068_);
lean_dec(v_usingArg_2065_);
lean_dec_ref(v_simprocs_2063_);
lean_dec_ref(v___x_2062_);
lean_dec(v___x_2061_);
v_a_2178_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2088_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2088_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object** _args){
lean_object* v___x_2188_ = _args[0];
lean_object* v_tk_2189_ = _args[1];
lean_object* v___x_2190_ = _args[2];
lean_object* v___x_2191_ = _args[3];
lean_object* v___x_2192_ = _args[4];
lean_object* v_simprocs_2193_ = _args[5];
lean_object* v___x_2194_ = _args[6];
lean_object* v_usingArg_2195_ = _args[7];
lean_object* v___x_2196_ = _args[8];
lean_object* v___x_2197_ = _args[9];
lean_object* v___x_2198_ = _args[10];
lean_object* v___x_2199_ = _args[11];
lean_object* v_usingTk_x3f_2200_ = _args[12];
lean_object* v_discharge_x3f_2201_ = _args[13];
lean_object* v___y_2202_ = _args[14];
lean_object* v___y_2203_ = _args[15];
lean_object* v___y_2204_ = _args[16];
lean_object* v___y_2205_ = _args[17];
lean_object* v___y_2206_ = _args[18];
lean_object* v___y_2207_ = _args[19];
lean_object* v___y_2208_ = _args[20];
lean_object* v___y_2209_ = _args[21];
lean_object* v___y_2210_ = _args[22];
_start:
{
uint8_t v___x_81636__boxed_2211_; uint8_t v___x_81637__boxed_2212_; uint8_t v___x_81638__boxed_2213_; lean_object* v_res_2214_; 
v___x_81636__boxed_2211_ = lean_unbox(v___x_2194_);
v___x_81637__boxed_2212_ = lean_unbox(v___x_2196_);
v___x_81638__boxed_2213_ = lean_unbox(v___x_2197_);
v_res_2214_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(v___x_2188_, v_tk_2189_, v___x_2190_, v___x_2191_, v___x_2192_, v_simprocs_2193_, v___x_81636__boxed_2211_, v_usingArg_2195_, v___x_81637__boxed_2212_, v___x_81638__boxed_2213_, v___x_2198_, v___x_2199_, v_usingTk_x3f_2200_, v_discharge_x3f_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___x_2188_);
return v_res_2214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Array_mkArray0(lean_box(0));
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__16));
v___x_2235_ = lean_unsigned_to_nat(15u);
v___x_2236_ = lean_unsigned_to_nat(116u);
v___x_2237_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__15));
v___x_2238_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__14));
v___x_2239_ = l_mkPanicMessageWithDecl(v___x_2238_, v___x_2237_, v___x_2236_, v___x_2235_, v___x_2234_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object* v_tk_2241_, lean_object* v___x_2242_, lean_object* v___x_2243_, lean_object* v___x_2244_, lean_object* v___x_2245_, lean_object* v___x_2246_, uint8_t v___x_2247_, lean_object* v___x_2248_, lean_object* v___f_2249_, lean_object* v___x_2250_, lean_object* v___x_2251_, lean_object* v___x_2252_, lean_object* v___x_2253_, lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v_usingArg_2256_, lean_object* v___x_2257_, uint8_t v___x_2258_, lean_object* v_usingTk_x3f_2259_, lean_object* v_squeeze_2260_, lean_object* v_unfold_2261_, lean_object* v_args_2262_, lean_object* v_only_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___y_2275_; lean_object* v___y_2279_; lean_object* v_stx_2280_; lean_object* v___y_2281_; lean_object* v_ref_2282_; lean_object* v___y_2283_; lean_object* v___y_2301_; lean_object* v_stx_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v_options_2306_; lean_object* v_ref_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; uint8_t v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v_args_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v_only_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2603_; lean_object* v___y_2604_; uint8_t v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2663_; lean_object* v___y_2664_; uint8_t v___y_2665_; lean_object* v___y_2676_; lean_object* v___y_2677_; uint8_t v___y_2678_; uint8_t v___y_2679_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; uint8_t v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2757_; 
v_options_2306_ = lean_ctor_get(v___y_2271_, 2);
v_ref_2307_ = lean_ctor_get(v___y_2271_, 5);
v___x_2308_ = 0;
v___x_2309_ = l_Lean_SourceInfo_fromRef(v_ref_2307_, v___x_2308_);
v___x_2310_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3));
lean_inc_ref(v___x_2244_);
lean_inc_ref(v___x_2243_);
lean_inc_ref(v___x_2242_);
v___x_2311_ = l_Lean_Name_mkStr4(v___x_2242_, v___x_2243_, v___x_2244_, v___x_2310_);
lean_inc(v___x_2309_);
v___x_2312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2309_);
lean_ctor_set(v___x_2312_, 1, v___x_2310_);
v___x_2313_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5));
v___x_2314_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6);
if (lean_obj_tag(v___y_2264_) == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2757_ = v___x_2766_;
goto v___jp_2756_;
}
else
{
lean_object* v_val_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_val_2767_ = lean_ctor_get(v___y_2264_, 0);
lean_inc(v_val_2767_);
lean_dec_ref(v___y_2264_);
v___x_2768_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___x_2769_ = lean_array_push(v___x_2768_, v_val_2767_);
v___y_2757_ = v___x_2769_;
goto v___jp_2756_;
}
v___jp_2274_:
{
lean_object* v_diag_2276_; lean_object* v___x_2277_; 
v_diag_2276_ = lean_ctor_get(v___y_2275_, 1);
lean_inc_ref(v_diag_2276_);
lean_dec_ref(v___y_2275_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_diag_2276_);
return v___x_2277_;
}
v___jp_2278_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2284_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1));
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v_stx_2280_);
v___x_2286_ = lean_box(0);
v___x_2287_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
lean_ctor_set(v___x_2287_, 2, v___x_2286_);
lean_ctor_set(v___x_2287_, 3, v___x_2286_);
lean_ctor_set(v___x_2287_, 4, v___x_2286_);
lean_ctor_set(v___x_2287_, 5, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_ref_2282_);
v___x_2289_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2));
v___x_2290_ = 4;
v___x_2291_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2241_, v___x_2287_, v___x_2288_, v___x_2289_, v___x_2286_, v___x_2290_, v___y_2281_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2281_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_dec_ref(v___x_2291_);
v___y_2275_ = v___y_2279_;
goto v___jp_2274_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v___y_2279_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
v___jp_2300_:
{
lean_object* v_ref_2305_; 
v_ref_2305_ = lean_ctor_get(v___y_2303_, 5);
lean_inc(v_ref_2305_);
v___y_2279_ = v___y_2301_;
v_stx_2280_ = v_stx_2302_;
v___y_2281_ = v___y_2303_;
v_ref_2282_ = v_ref_2305_;
v___y_2283_ = v___y_2304_;
goto v___jp_2278_;
}
v___jp_2315_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2327_ = l_Array_append___redArg(v___x_2314_, v___y_2326_);
lean_dec_ref(v___y_2326_);
lean_inc_n(v___y_2320_, 2);
v___x_2328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2328_, 0, v___y_2320_);
lean_ctor_set(v___x_2328_, 1, v___x_2313_);
lean_ctor_set(v___x_2328_, 2, v___x_2327_);
v___x_2329_ = l_Lean_Syntax_node5(v___y_2320_, v___x_2245_, v___y_2318_, v___y_2317_, v___y_2324_, v___y_2322_, v___x_2328_);
lean_inc(v___y_2325_);
v___x_2330_ = l_Lean_Syntax_node4(v___y_2320_, v___x_2248_, v___y_2323_, v___y_2325_, v___y_2325_, v___x_2329_);
v___y_2301_ = v___y_2316_;
v_stx_2302_ = v___x_2330_;
v___y_2303_ = v___y_2319_;
v___y_2304_ = v___y_2321_;
goto v___jp_2300_;
}
v___jp_2331_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = l_Array_append___redArg(v___x_2314_, v___y_2342_);
lean_dec_ref(v___y_2342_);
lean_inc(v___y_2336_);
v___x_2344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2344_, 0, v___y_2336_);
lean_ctor_set(v___x_2344_, 1, v___x_2313_);
lean_ctor_set(v___x_2344_, 2, v___x_2343_);
if (lean_obj_tag(v___y_2338_) == 1)
{
lean_object* v_val_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v___x_2246_);
v_val_2345_ = lean_ctor_get(v___y_2338_, 0);
lean_inc(v_val_2345_);
lean_dec_ref(v___y_2338_);
v___x_2346_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2336_);
v___x_2347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___y_2336_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = l_Array_mkArray2___redArg(v___x_2347_, v_val_2345_);
v___y_2316_ = v___y_2332_;
v___y_2317_ = v___y_2334_;
v___y_2318_ = v___y_2333_;
v___y_2319_ = v___y_2335_;
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2337_;
v___y_2322_ = v___x_2344_;
v___y_2323_ = v___y_2340_;
v___y_2324_ = v___y_2339_;
v___y_2325_ = v___y_2341_;
v___y_2326_ = v___x_2348_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2349_; 
lean_dec(v___y_2338_);
v___x_2349_ = lean_mk_empty_array_with_capacity(v___x_2246_);
lean_dec(v___x_2246_);
v___y_2316_ = v___y_2332_;
v___y_2317_ = v___y_2334_;
v___y_2318_ = v___y_2333_;
v___y_2319_ = v___y_2335_;
v___y_2320_ = v___y_2336_;
v___y_2321_ = v___y_2337_;
v___y_2322_ = v___x_2344_;
v___y_2323_ = v___y_2340_;
v___y_2324_ = v___y_2339_;
v___y_2325_ = v___y_2341_;
v___y_2326_ = v___x_2349_;
goto v___jp_2315_;
}
}
v___jp_2350_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = l_Array_append___redArg(v___x_2314_, v___y_2361_);
lean_dec_ref(v___y_2361_);
lean_inc(v___y_2356_);
v___x_2363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2363_, 0, v___y_2356_);
lean_ctor_set(v___x_2363_, 1, v___x_2313_);
lean_ctor_set(v___x_2363_, 2, v___x_2362_);
if (lean_obj_tag(v___y_2352_) == 1)
{
lean_object* v_val_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_val_2364_ = lean_ctor_get(v___y_2352_, 0);
lean_inc(v_val_2364_);
lean_dec_ref(v___y_2352_);
v___x_2365_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2366_ = l_Lean_Name_mkStr4(v___x_2242_, v___x_2243_, v___x_2244_, v___x_2365_);
v___x_2367_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___y_2356_, 4);
v___x_2368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___y_2356_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = l_Array_append___redArg(v___x_2314_, v_val_2364_);
lean_dec(v_val_2364_);
v___x_2370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2370_, 0, v___y_2356_);
lean_ctor_set(v___x_2370_, 1, v___x_2313_);
lean_ctor_set(v___x_2370_, 2, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___y_2356_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Lean_Syntax_node3(v___y_2356_, v___x_2366_, v___x_2368_, v___x_2370_, v___x_2372_);
v___x_2374_ = l_Array_mkArray1___redArg(v___x_2373_);
v___y_2332_ = v___y_2351_;
v___y_2333_ = v___y_2354_;
v___y_2334_ = v___y_2353_;
v___y_2335_ = v___y_2355_;
v___y_2336_ = v___y_2356_;
v___y_2337_ = v___y_2357_;
v___y_2338_ = v___y_2359_;
v___y_2339_ = v___x_2363_;
v___y_2340_ = v___y_2358_;
v___y_2341_ = v___y_2360_;
v___y_2342_ = v___x_2374_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2375_; 
lean_dec(v___y_2352_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
v___x_2375_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2332_ = v___y_2351_;
v___y_2333_ = v___y_2354_;
v___y_2334_ = v___y_2353_;
v___y_2335_ = v___y_2355_;
v___y_2336_ = v___y_2356_;
v___y_2337_ = v___y_2357_;
v___y_2338_ = v___y_2359_;
v___y_2339_ = v___x_2363_;
v___y_2340_ = v___y_2358_;
v___y_2341_ = v___y_2360_;
v___y_2342_ = v___x_2375_;
goto v___jp_2331_;
}
}
v___jp_2376_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = l_Array_append___redArg(v___x_2314_, v___y_2387_);
lean_dec_ref(v___y_2387_);
lean_inc(v___y_2381_);
v___x_2389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2389_, 0, v___y_2381_);
lean_ctor_set(v___x_2389_, 1, v___x_2313_);
lean_ctor_set(v___x_2389_, 2, v___x_2388_);
if (lean_obj_tag(v___y_2382_) == 1)
{
lean_object* v_val_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_val_2390_ = lean_ctor_get(v___y_2382_, 0);
lean_inc(v_val_2390_);
lean_dec_ref(v___y_2382_);
v___x_2391_ = l_Lean_SourceInfo_fromRef(v_val_2390_, v___x_2247_);
lean_dec(v_val_2390_);
v___x_2392_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Array_mkArray1___redArg(v___x_2393_);
v___y_2351_ = v___y_2377_;
v___y_2352_ = v___y_2379_;
v___y_2353_ = v___x_2389_;
v___y_2354_ = v___y_2378_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v___y_2381_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2385_;
v___y_2359_ = v___y_2384_;
v___y_2360_ = v___y_2386_;
v___y_2361_ = v___x_2394_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2395_; 
lean_dec(v___y_2382_);
v___x_2395_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2351_ = v___y_2377_;
v___y_2352_ = v___y_2379_;
v___y_2353_ = v___x_2389_;
v___y_2354_ = v___y_2378_;
v___y_2355_ = v___y_2380_;
v___y_2356_ = v___y_2381_;
v___y_2357_ = v___y_2383_;
v___y_2358_ = v___y_2385_;
v___y_2359_ = v___y_2384_;
v___y_2360_ = v___y_2386_;
v___y_2361_ = v___x_2395_;
goto v___jp_2350_;
}
}
v___jp_2396_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2408_ = l_Array_append___redArg(v___x_2314_, v___y_2407_);
lean_dec_ref(v___y_2407_);
lean_inc_n(v___y_2398_, 2);
v___x_2409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2409_, 0, v___y_2398_);
lean_ctor_set(v___x_2409_, 1, v___x_2313_);
lean_ctor_set(v___x_2409_, 2, v___x_2408_);
v___x_2410_ = l_Lean_Syntax_node5(v___y_2398_, v___x_2245_, v___y_2399_, v___y_2403_, v___y_2401_, v___y_2406_, v___x_2409_);
v___x_2411_ = l_Lean_Syntax_node2(v___y_2398_, v___y_2405_, v___y_2404_, v___x_2410_);
v___y_2301_ = v___y_2397_;
v_stx_2302_ = v___x_2411_;
v___y_2303_ = v___y_2400_;
v___y_2304_ = v___y_2402_;
goto v___jp_2300_;
}
v___jp_2412_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = l_Array_append___redArg(v___x_2314_, v___y_2423_);
lean_dec_ref(v___y_2423_);
lean_inc(v___y_2414_);
v___x_2425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2425_, 0, v___y_2414_);
lean_ctor_set(v___x_2425_, 1, v___x_2313_);
lean_ctor_set(v___x_2425_, 2, v___x_2424_);
if (lean_obj_tag(v___y_2422_) == 1)
{
lean_object* v_val_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_dec(v___x_2246_);
v_val_2426_ = lean_ctor_get(v___y_2422_, 0);
lean_inc(v_val_2426_);
lean_dec_ref(v___y_2422_);
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7));
lean_inc(v___y_2414_);
v___x_2428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2414_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = l_Array_mkArray2___redArg(v___x_2428_, v_val_2426_);
v___y_2397_ = v___y_2413_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2415_;
v___y_2400_ = v___y_2416_;
v___y_2401_ = v___y_2417_;
v___y_2402_ = v___y_2419_;
v___y_2403_ = v___y_2418_;
v___y_2404_ = v___y_2421_;
v___y_2405_ = v___y_2420_;
v___y_2406_ = v___x_2425_;
v___y_2407_ = v___x_2429_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2430_; 
lean_dec(v___y_2422_);
v___x_2430_ = lean_mk_empty_array_with_capacity(v___x_2246_);
lean_dec(v___x_2246_);
v___y_2397_ = v___y_2413_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2415_;
v___y_2400_ = v___y_2416_;
v___y_2401_ = v___y_2417_;
v___y_2402_ = v___y_2419_;
v___y_2403_ = v___y_2418_;
v___y_2404_ = v___y_2421_;
v___y_2405_ = v___y_2420_;
v___y_2406_ = v___x_2425_;
v___y_2407_ = v___x_2430_;
goto v___jp_2396_;
}
}
v___jp_2431_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = l_Array_append___redArg(v___x_2314_, v___y_2442_);
lean_dec_ref(v___y_2442_);
lean_inc(v___y_2433_);
v___x_2444_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2444_, 0, v___y_2433_);
lean_ctor_set(v___x_2444_, 1, v___x_2313_);
lean_ctor_set(v___x_2444_, 2, v___x_2443_);
if (lean_obj_tag(v___y_2434_) == 1)
{
lean_object* v_val_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_val_2445_ = lean_ctor_get(v___y_2434_, 0);
lean_inc(v_val_2445_);
lean_dec_ref(v___y_2434_);
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__8));
v___x_2447_ = l_Lean_Name_mkStr4(v___x_2242_, v___x_2243_, v___x_2244_, v___x_2446_);
v___x_2448_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___y_2433_, 4);
v___x_2449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___y_2433_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l_Array_append___redArg(v___x_2314_, v_val_2445_);
lean_dec(v_val_2445_);
v___x_2451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2451_, 0, v___y_2433_);
lean_ctor_set(v___x_2451_, 1, v___x_2313_);
lean_ctor_set(v___x_2451_, 2, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___y_2433_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = l_Lean_Syntax_node3(v___y_2433_, v___x_2447_, v___x_2449_, v___x_2451_, v___x_2453_);
v___x_2455_ = l_Array_mkArray1___redArg(v___x_2454_);
v___y_2413_ = v___y_2432_;
v___y_2414_ = v___y_2433_;
v___y_2415_ = v___y_2435_;
v___y_2416_ = v___y_2436_;
v___y_2417_ = v___x_2444_;
v___y_2418_ = v___y_2438_;
v___y_2419_ = v___y_2437_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2439_;
v___y_2422_ = v___y_2441_;
v___y_2423_ = v___x_2455_;
goto v___jp_2412_;
}
else
{
lean_object* v___x_2456_; 
lean_dec(v___y_2434_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
v___x_2456_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2413_ = v___y_2432_;
v___y_2414_ = v___y_2433_;
v___y_2415_ = v___y_2435_;
v___y_2416_ = v___y_2436_;
v___y_2417_ = v___x_2444_;
v___y_2418_ = v___y_2438_;
v___y_2419_ = v___y_2437_;
v___y_2420_ = v___y_2440_;
v___y_2421_ = v___y_2439_;
v___y_2422_ = v___y_2441_;
v___y_2423_ = v___x_2456_;
goto v___jp_2412_;
}
}
v___jp_2457_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = l_Array_append___redArg(v___x_2314_, v___y_2468_);
lean_dec_ref(v___y_2468_);
lean_inc(v___y_2459_);
v___x_2470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2470_, 0, v___y_2459_);
lean_ctor_set(v___x_2470_, 1, v___x_2313_);
lean_ctor_set(v___x_2470_, 2, v___x_2469_);
if (lean_obj_tag(v___y_2463_) == 1)
{
lean_object* v_val_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_val_2471_ = lean_ctor_get(v___y_2463_, 0);
lean_inc(v_val_2471_);
lean_dec_ref(v___y_2463_);
v___x_2472_ = l_Lean_SourceInfo_fromRef(v_val_2471_, v___x_2247_);
lean_dec(v_val_2471_);
v___x_2473_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = l_Array_mkArray1___redArg(v___x_2474_);
v___y_2432_ = v___y_2458_;
v___y_2433_ = v___y_2459_;
v___y_2434_ = v___y_2461_;
v___y_2435_ = v___y_2460_;
v___y_2436_ = v___y_2462_;
v___y_2437_ = v___y_2464_;
v___y_2438_ = v___x_2470_;
v___y_2439_ = v___y_2466_;
v___y_2440_ = v___y_2465_;
v___y_2441_ = v___y_2467_;
v___y_2442_ = v___x_2475_;
goto v___jp_2431_;
}
else
{
lean_object* v___x_2476_; 
lean_dec(v___y_2463_);
v___x_2476_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2432_ = v___y_2458_;
v___y_2433_ = v___y_2459_;
v___y_2434_ = v___y_2461_;
v___y_2435_ = v___y_2460_;
v___y_2436_ = v___y_2462_;
v___y_2437_ = v___y_2464_;
v___y_2438_ = v___x_2470_;
v___y_2439_ = v___y_2466_;
v___y_2440_ = v___y_2465_;
v___y_2441_ = v___y_2467_;
v___y_2442_ = v___x_2476_;
goto v___jp_2431_;
}
}
v___jp_2477_:
{
if (v___y_2489_ == 0)
{
lean_object* v___x_2493_; 
lean_inc(v___y_2488_);
lean_inc_ref(v___y_2482_);
v___x_2493_ = lean_apply_9(v___f_2249_, v___y_2478_, v___y_2487_, v___y_2481_, v___y_2490_, v___y_2491_, v___y_2480_, v___y_2482_, v___y_2488_, lean_box(0));
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc_n(v_a_2494_, 3);
lean_dec_ref(v___x_2493_);
v___x_2495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2250_);
v___x_2496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2313_);
lean_ctor_set(v___x_2496_, 2, v___x_2314_);
if (lean_obj_tag(v___y_2492_) == 0)
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2377_ = v___y_2479_;
v___y_2378_ = v___y_2485_;
v___y_2379_ = v___y_2486_;
v___y_2380_ = v___y_2482_;
v___y_2381_ = v_a_2494_;
v___y_2382_ = v___y_2483_;
v___y_2383_ = v___y_2488_;
v___y_2384_ = v___y_2484_;
v___y_2385_ = v___x_2495_;
v___y_2386_ = v___x_2496_;
v___y_2387_ = v___x_2497_;
goto v___jp_2376_;
}
else
{
lean_object* v_val_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v_val_2498_ = lean_ctor_get(v___y_2492_, 0);
lean_inc(v_val_2498_);
lean_dec_ref(v___y_2492_);
v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___x_2500_ = lean_array_push(v___x_2499_, v_val_2498_);
v___y_2377_ = v___y_2479_;
v___y_2378_ = v___y_2485_;
v___y_2379_ = v___y_2486_;
v___y_2380_ = v___y_2482_;
v___y_2381_ = v_a_2494_;
v___y_2382_ = v___y_2483_;
v___y_2383_ = v___y_2488_;
v___y_2384_ = v___y_2484_;
v___y_2385_ = v___x_2495_;
v___y_2386_ = v___x_2496_;
v___y_2387_ = v___x_2500_;
goto v___jp_2376_;
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v___y_2492_);
lean_dec(v___y_2488_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___x_2250_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
lean_dec(v_tk_2241_);
v_a_2501_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2493_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2493_);
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
else
{
lean_object* v___x_2509_; 
lean_dec_ref(v___x_2250_);
lean_dec(v___x_2248_);
lean_inc(v___y_2488_);
lean_inc_ref(v___y_2482_);
v___x_2509_ = lean_apply_9(v___f_2249_, v___y_2478_, v___y_2487_, v___y_2481_, v___y_2490_, v___y_2491_, v___y_2480_, v___y_2482_, v___y_2488_, lean_box(0));
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc_n(v_a_2510_, 2);
lean_dec_ref(v___x_2509_);
v___x_2511_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__12));
lean_inc_ref(v___x_2244_);
lean_inc_ref(v___x_2243_);
lean_inc_ref(v___x_2242_);
v___x_2512_ = l_Lean_Name_mkStr4(v___x_2242_, v___x_2243_, v___x_2244_, v___x_2511_);
v___x_2513_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__13));
v___x_2514_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2514_, 0, v_a_2510_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
if (lean_obj_tag(v___y_2492_) == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2458_ = v___y_2479_;
v___y_2459_ = v_a_2510_;
v___y_2460_ = v___y_2485_;
v___y_2461_ = v___y_2486_;
v___y_2462_ = v___y_2482_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2488_;
v___y_2465_ = v___x_2512_;
v___y_2466_ = v___x_2514_;
v___y_2467_ = v___y_2484_;
v___y_2468_ = v___x_2515_;
goto v___jp_2457_;
}
else
{
lean_object* v_val_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_val_2516_ = lean_ctor_get(v___y_2492_, 0);
lean_inc(v_val_2516_);
lean_dec_ref(v___y_2492_);
v___x_2517_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___x_2518_ = lean_array_push(v___x_2517_, v_val_2516_);
v___y_2458_ = v___y_2479_;
v___y_2459_ = v_a_2510_;
v___y_2460_ = v___y_2485_;
v___y_2461_ = v___y_2486_;
v___y_2462_ = v___y_2482_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2488_;
v___y_2465_ = v___x_2512_;
v___y_2466_ = v___x_2514_;
v___y_2467_ = v___y_2484_;
v___y_2468_ = v___x_2518_;
goto v___jp_2457_;
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v___y_2492_);
lean_dec(v___y_2488_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v___y_2479_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
lean_dec(v_tk_2241_);
v_a_2519_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2509_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2509_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
v___jp_2527_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = lean_unsigned_to_nat(5u);
v___x_2545_ = l_Lean_Syntax_getArg(v___y_2534_, v___x_2544_);
lean_dec(v___y_2534_);
v___x_2546_ = l_Lean_Syntax_matchesNull(v___x_2545_, v___x_2246_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_args_2535_);
lean_dec(v___y_2533_);
lean_dec(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
v___x_2547_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2548_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2547_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref(v___x_2548_);
v___y_2301_ = v___y_2528_;
v_stx_2302_ = v_a_2549_;
v___y_2303_ = v___y_2542_;
v___y_2304_ = v___y_2543_;
goto v___jp_2300_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v___y_2528_);
lean_dec(v_tk_2241_);
v_a_2550_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2548_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2548_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Syntax_getOptional_x3f(v___y_2529_);
lean_dec(v___y_2529_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_box(0);
v___y_2478_ = v___y_2536_;
v___y_2479_ = v___y_2528_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___y_2538_;
v___y_2482_ = v___y_2542_;
v___y_2483_ = v___y_2531_;
v___y_2484_ = v___y_2533_;
v___y_2485_ = v___y_2530_;
v___y_2486_ = v_args_2535_;
v___y_2487_ = v___y_2537_;
v___y_2488_ = v___y_2543_;
v___y_2489_ = v___y_2532_;
v___y_2490_ = v___y_2539_;
v___y_2491_ = v___y_2540_;
v___y_2492_ = v___x_2559_;
goto v___jp_2477_;
}
else
{
lean_object* v_val_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_val_2560_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2558_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_val_2560_);
lean_dec(v___x_2558_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_val_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
v___y_2478_ = v___y_2536_;
v___y_2479_ = v___y_2528_;
v___y_2480_ = v___y_2541_;
v___y_2481_ = v___y_2538_;
v___y_2482_ = v___y_2542_;
v___y_2483_ = v___y_2531_;
v___y_2484_ = v___y_2533_;
v___y_2485_ = v___y_2530_;
v___y_2486_ = v_args_2535_;
v___y_2487_ = v___y_2537_;
v___y_2488_ = v___y_2543_;
v___y_2489_ = v___y_2532_;
v___y_2490_ = v___y_2539_;
v___y_2491_ = v___y_2540_;
v___y_2492_ = v___x_2565_;
goto v___jp_2477_;
}
}
}
}
}
v___jp_2568_:
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = l_Lean_Syntax_getArg(v___y_2574_, v___x_2251_);
v___x_2585_ = l_Lean_Syntax_isNone(v___x_2584_);
if (v___x_2585_ == 0)
{
uint8_t v___x_2586_; 
lean_inc(v___x_2584_);
v___x_2586_ = l_Lean_Syntax_matchesNull(v___x_2584_, v___x_2252_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec(v___x_2584_);
lean_dec(v_only_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
v___x_2587_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2588_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2587_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v___y_2301_ = v___y_2569_;
v_stx_2302_ = v_a_2589_;
v___y_2303_ = v___y_2582_;
v___y_2304_ = v___y_2583_;
goto v___jp_2300_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v___y_2569_);
lean_dec(v_tk_2241_);
v_a_2590_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2588_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2588_);
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
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = l_Lean_Syntax_getArg(v___x_2584_, v___x_2253_);
lean_dec(v___x_2253_);
lean_dec(v___x_2584_);
v___x_2599_ = l_Lean_Syntax_getArgs(v___x_2598_);
lean_dec(v___x_2598_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
v___y_2528_ = v___y_2569_;
v___y_2529_ = v___y_2570_;
v___y_2530_ = v___y_2571_;
v___y_2531_ = v_only_2575_;
v___y_2532_ = v___y_2572_;
v___y_2533_ = v___y_2573_;
v___y_2534_ = v___y_2574_;
v_args_2535_ = v___x_2600_;
v___y_2536_ = v___y_2576_;
v___y_2537_ = v___y_2577_;
v___y_2538_ = v___y_2578_;
v___y_2539_ = v___y_2579_;
v___y_2540_ = v___y_2580_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
goto v___jp_2527_;
}
}
else
{
lean_object* v___x_2601_; 
lean_dec(v___x_2584_);
lean_dec(v___x_2253_);
v___x_2601_ = lean_box(0);
v___y_2528_ = v___y_2569_;
v___y_2529_ = v___y_2570_;
v___y_2530_ = v___y_2571_;
v___y_2531_ = v_only_2575_;
v___y_2532_ = v___y_2572_;
v___y_2533_ = v___y_2573_;
v___y_2534_ = v___y_2574_;
v_args_2535_ = v___x_2601_;
v___y_2536_ = v___y_2576_;
v___y_2537_ = v___y_2577_;
v___y_2538_ = v___y_2578_;
v___y_2539_ = v___y_2579_;
v___y_2540_ = v___y_2580_;
v___y_2541_ = v___y_2581_;
v___y_2542_ = v___y_2582_;
v___y_2543_ = v___y_2583_;
goto v___jp_2527_;
}
}
v___jp_2602_:
{
lean_object* v_usedTheorems_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_usedTheorems_2607_ = lean_ctor_get(v___y_2603_, 0);
v___x_2608_ = l_Lean_Syntax_unsetTrailing(v___y_2604_);
v___x_2609_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2608_, v_usedTheorems_2607_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; uint8_t v___x_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc_n(v_a_2610_, 2);
lean_dec_ref(v___x_2609_);
v___x_2611_ = l_Lean_Syntax_isOfKind(v_a_2610_, v___x_2311_);
lean_dec(v___x_2311_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_inc(v_ref_2307_);
lean_dec(v_a_2610_);
lean_dec(v___y_2606_);
lean_dec(v___x_2255_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
v___x_2612_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2613_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2612_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2613_);
v___y_2279_ = v___y_2603_;
v_stx_2280_ = v_a_2614_;
v___y_2281_ = v___y_2271_;
v_ref_2282_ = v_ref_2307_;
v___y_2283_ = v___y_2272_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v___y_2603_);
lean_dec(v_ref_2307_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v_tk_2241_);
v_a_2615_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2613_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2613_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = l_Lean_Syntax_getArg(v_a_2610_, v___x_2253_);
lean_inc(v___x_2623_);
v___x_2624_ = l_Lean_Syntax_isOfKind(v___x_2623_, v___x_2254_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_inc(v_ref_2307_);
lean_dec(v___x_2623_);
lean_dec(v_a_2610_);
lean_dec(v___y_2606_);
lean_dec(v___x_2255_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
v___x_2625_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2626_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2625_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v___x_2626_);
v___y_2279_ = v___y_2603_;
v_stx_2280_ = v_a_2627_;
v___y_2281_ = v___y_2271_;
v_ref_2282_ = v_ref_2307_;
v___y_2283_ = v___y_2272_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v___y_2603_);
lean_dec(v_ref_2307_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v_tk_2241_);
v_a_2628_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2626_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2626_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2636_ = l_Lean_Syntax_getArg(v_a_2610_, v___x_2255_);
lean_dec(v___x_2255_);
v___x_2637_ = l_Lean_Syntax_getArg(v_a_2610_, v___x_2252_);
v___x_2638_ = l_Lean_Syntax_isNone(v___x_2637_);
if (v___x_2638_ == 0)
{
uint8_t v___x_2639_; 
lean_inc(v___x_2637_);
v___x_2639_ = l_Lean_Syntax_matchesNull(v___x_2637_, v___x_2253_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_inc(v_ref_2307_);
lean_dec(v___x_2637_);
lean_dec(v___x_2636_);
lean_dec(v___x_2623_);
lean_dec(v_a_2610_);
lean_dec(v___y_2606_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
v___x_2640_ = lean_obj_once(&l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17, &l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17_once, _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__17);
v___x_2641_ = l_panic___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__9(v___x_2640_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref(v___x_2641_);
v___y_2279_ = v___y_2603_;
v_stx_2280_ = v_a_2642_;
v___y_2281_ = v___y_2271_;
v_ref_2282_ = v_ref_2307_;
v___y_2283_ = v___y_2272_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v___y_2603_);
lean_dec(v_ref_2307_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v_tk_2241_);
v_a_2643_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2641_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2641_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = l_Lean_Syntax_getArg(v___x_2637_, v___x_2246_);
lean_dec(v___x_2637_);
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
v___y_2569_ = v___y_2603_;
v___y_2570_ = v___x_2636_;
v___y_2571_ = v___x_2623_;
v___y_2572_ = v___y_2605_;
v___y_2573_ = v___y_2606_;
v___y_2574_ = v_a_2610_;
v_only_2575_ = v___x_2652_;
v___y_2576_ = v___y_2265_;
v___y_2577_ = v___y_2266_;
v___y_2578_ = v___y_2267_;
v___y_2579_ = v___y_2268_;
v___y_2580_ = v___y_2269_;
v___y_2581_ = v___y_2270_;
v___y_2582_ = v___y_2271_;
v___y_2583_ = v___y_2272_;
goto v___jp_2568_;
}
}
else
{
lean_object* v___x_2653_; 
lean_dec(v___x_2637_);
v___x_2653_ = lean_box(0);
v___y_2569_ = v___y_2603_;
v___y_2570_ = v___x_2636_;
v___y_2571_ = v___x_2623_;
v___y_2572_ = v___y_2605_;
v___y_2573_ = v___y_2606_;
v___y_2574_ = v_a_2610_;
v_only_2575_ = v___x_2653_;
v___y_2576_ = v___y_2265_;
v___y_2577_ = v___y_2266_;
v___y_2578_ = v___y_2267_;
v___y_2579_ = v___y_2268_;
v___y_2580_ = v___y_2269_;
v___y_2581_ = v___y_2270_;
v___y_2582_ = v___y_2271_;
v___y_2583_ = v___y_2272_;
goto v___jp_2568_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2603_);
lean_dec(v___x_2311_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___x_2255_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
lean_dec(v_tk_2241_);
v_a_2654_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2609_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2609_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
v___jp_2662_:
{
if (lean_obj_tag(v_usingArg_2256_) == 0)
{
v___y_2603_ = v___y_2663_;
v___y_2604_ = v___y_2664_;
v___y_2605_ = v___y_2665_;
v___y_2606_ = v_usingArg_2256_;
goto v___jp_2602_;
}
else
{
lean_object* v_val_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2674_; 
v_val_2666_ = lean_ctor_get(v_usingArg_2256_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_usingArg_2256_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2668_ = v_usingArg_2256_;
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_val_2666_);
lean_dec(v_usingArg_2256_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2670_ = l_Lean_Syntax_unsetTrailing(v_val_2666_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2670_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
v___y_2603_ = v___y_2663_;
v___y_2604_ = v___y_2664_;
v___y_2605_ = v___y_2665_;
v___y_2606_ = v___x_2672_;
goto v___jp_2602_;
}
}
}
}
v___jp_2675_:
{
if (v___y_2679_ == 0)
{
lean_dec(v___y_2677_);
lean_dec(v___x_2311_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_usingArg_2256_);
lean_dec(v___x_2255_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
lean_dec(v_tk_2241_);
v___y_2275_ = v___y_2676_;
goto v___jp_2274_;
}
else
{
v___y_2663_ = v___y_2676_;
v___y_2664_ = v___y_2677_;
v___y_2665_ = v___y_2678_;
goto v___jp_2662_;
}
}
v___jp_2680_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; 
v___x_2686_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_2685_, v___x_2308_);
v___x_2687_ = lean_box(v___x_2247_);
v___x_2688_ = lean_box(v___x_2308_);
v___x_2689_ = lean_box(v___x_2258_);
lean_inc(v___x_2253_);
lean_inc_ref(v___x_2250_);
lean_inc(v_usingArg_2256_);
lean_inc(v___x_2246_);
lean_inc(v_tk_2241_);
lean_inc(v___x_2255_);
v___f_2690_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 23, 13);
lean_closure_set(v___f_2690_, 0, v___x_2255_);
lean_closure_set(v___f_2690_, 1, v_tk_2241_);
lean_closure_set(v___f_2690_, 2, v___x_2313_);
lean_closure_set(v___f_2690_, 3, v___x_2246_);
lean_closure_set(v___f_2690_, 4, v___x_2686_);
lean_closure_set(v___f_2690_, 5, v___y_2681_);
lean_closure_set(v___f_2690_, 6, v___x_2687_);
lean_closure_set(v___f_2690_, 7, v_usingArg_2256_);
lean_closure_set(v___f_2690_, 8, v___x_2688_);
lean_closure_set(v___f_2690_, 9, v___x_2689_);
lean_closure_set(v___f_2690_, 10, v___x_2250_);
lean_closure_set(v___f_2690_, 11, v___x_2253_);
lean_closure_set(v___f_2690_, 12, v_usingTk_x3f_2259_);
v___x_2691_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_2683_, v___f_2690_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2683_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v___x_2693_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_2694_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__10(v_options_2306_, v___x_2693_);
if (v___x_2694_ == 0)
{
if (lean_obj_tag(v_squeeze_2260_) == 0)
{
v___y_2676_ = v_a_2692_;
v___y_2677_ = v___y_2682_;
v___y_2678_ = v___y_2684_;
v___y_2679_ = v___x_2694_;
goto v___jp_2675_;
}
else
{
v___y_2676_ = v_a_2692_;
v___y_2677_ = v___y_2682_;
v___y_2678_ = v___y_2684_;
v___y_2679_ = v___x_2258_;
goto v___jp_2675_;
}
}
else
{
v___y_2663_ = v_a_2692_;
v___y_2664_ = v___y_2682_;
v___y_2665_ = v___y_2684_;
goto v___jp_2662_;
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v___y_2682_);
lean_dec(v___x_2311_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_usingArg_2256_);
lean_dec(v___x_2255_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
lean_dec(v_tk_2241_);
v_a_2695_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2691_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2691_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
v___jp_2703_:
{
v___y_2681_ = v___y_2706_;
v___y_2682_ = v___y_2707_;
v___y_2683_ = v___y_2705_;
v___y_2684_ = v___x_2308_;
v___y_2685_ = v___y_2704_;
goto v___jp_2680_;
}
v___jp_2708_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2712_ = l_Array_append___redArg(v___x_2314_, v___y_2711_);
lean_dec_ref(v___y_2711_);
lean_inc_n(v___x_2309_, 2);
v___x_2713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2309_);
lean_ctor_set(v___x_2713_, 1, v___x_2313_);
lean_ctor_set(v___x_2713_, 2, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2309_);
lean_ctor_set(v___x_2714_, 1, v___x_2313_);
lean_ctor_set(v___x_2714_, 2, v___x_2314_);
lean_inc(v___x_2311_);
v___x_2715_ = l_Lean_Syntax_node6(v___x_2309_, v___x_2311_, v___x_2312_, v___x_2257_, v___y_2710_, v___y_2709_, v___x_2713_, v___x_2714_);
v___x_2716_ = 0;
v___x_2717_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__18));
v___x_2718_ = lean_box(v___x_2308_);
v___x_2719_ = lean_box(v___x_2716_);
v___x_2720_ = lean_box(v___x_2308_);
lean_inc(v___x_2715_);
v___x_2721_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_2721_, 0, v___x_2715_);
lean_closure_set(v___x_2721_, 1, v___x_2718_);
lean_closure_set(v___x_2721_, 2, v___x_2719_);
lean_closure_set(v___x_2721_, 3, v___x_2720_);
lean_closure_set(v___x_2721_, 4, v___x_2717_);
v___x_2722_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_2721_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref(v___x_2722_);
if (lean_obj_tag(v_unfold_2261_) == 0)
{
lean_object* v_ctx_2724_; lean_object* v_simprocs_2725_; lean_object* v_dischargeWrapper_2726_; 
v_ctx_2724_ = lean_ctor_get(v_a_2723_, 0);
lean_inc_ref(v_ctx_2724_);
v_simprocs_2725_ = lean_ctor_get(v_a_2723_, 1);
lean_inc_ref(v_simprocs_2725_);
v_dischargeWrapper_2726_ = lean_ctor_get(v_a_2723_, 2);
lean_inc(v_dischargeWrapper_2726_);
lean_dec(v_a_2723_);
v___y_2704_ = v_ctx_2724_;
v___y_2705_ = v_dischargeWrapper_2726_;
v___y_2706_ = v_simprocs_2725_;
v___y_2707_ = v___x_2715_;
goto v___jp_2703_;
}
else
{
if (v___x_2258_ == 0)
{
lean_object* v_ctx_2727_; lean_object* v_simprocs_2728_; lean_object* v_dischargeWrapper_2729_; 
v_ctx_2727_ = lean_ctor_get(v_a_2723_, 0);
lean_inc_ref(v_ctx_2727_);
v_simprocs_2728_ = lean_ctor_get(v_a_2723_, 1);
lean_inc_ref(v_simprocs_2728_);
v_dischargeWrapper_2729_ = lean_ctor_get(v_a_2723_, 2);
lean_inc(v_dischargeWrapper_2729_);
lean_dec(v_a_2723_);
v___y_2704_ = v_ctx_2727_;
v___y_2705_ = v_dischargeWrapper_2729_;
v___y_2706_ = v_simprocs_2728_;
v___y_2707_ = v___x_2715_;
goto v___jp_2703_;
}
else
{
lean_object* v_ctx_2730_; lean_object* v_simprocs_2731_; lean_object* v_dischargeWrapper_2732_; lean_object* v___x_2733_; 
v_ctx_2730_ = lean_ctor_get(v_a_2723_, 0);
lean_inc_ref(v_ctx_2730_);
v_simprocs_2731_ = lean_ctor_get(v_a_2723_, 1);
lean_inc_ref(v_simprocs_2731_);
v_dischargeWrapper_2732_ = lean_ctor_get(v_a_2723_, 2);
lean_inc(v_dischargeWrapper_2732_);
lean_dec(v_a_2723_);
v___x_2733_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_2730_);
v___y_2681_ = v_simprocs_2731_;
v___y_2682_ = v___x_2715_;
v___y_2683_ = v_dischargeWrapper_2732_;
v___y_2684_ = v___x_2258_;
v___y_2685_ = v___x_2733_;
goto v___jp_2680_;
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v___x_2715_);
lean_dec(v___x_2311_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_usingTk_x3f_2259_);
lean_dec(v_usingArg_2256_);
lean_dec(v___x_2255_);
lean_dec(v___x_2253_);
lean_dec_ref(v___x_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v___x_2248_);
lean_dec(v___x_2246_);
lean_dec(v___x_2245_);
lean_dec_ref(v___x_2244_);
lean_dec_ref(v___x_2243_);
lean_dec_ref(v___x_2242_);
lean_dec(v_tk_2241_);
v_a_2734_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2722_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2722_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
v___jp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = l_Array_append___redArg(v___x_2314_, v___y_2744_);
lean_dec_ref(v___y_2744_);
lean_inc(v___x_2309_);
v___x_2746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2309_);
lean_ctor_set(v___x_2746_, 1, v___x_2313_);
lean_ctor_set(v___x_2746_, 2, v___x_2745_);
if (lean_obj_tag(v_args_2262_) == 1)
{
lean_object* v_val_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_val_2747_ = lean_ctor_get(v_args_2262_, 0);
v___x_2748_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__9));
lean_inc_n(v___x_2309_, 3);
v___x_2749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2309_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = l_Array_append___redArg(v___x_2314_, v_val_2747_);
v___x_2751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2309_);
lean_ctor_set(v___x_2751_, 1, v___x_2313_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
v___x_2752_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__10));
v___x_2753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2309_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Array_mkArray3___redArg(v___x_2749_, v___x_2751_, v___x_2753_);
v___y_2709_ = v___x_2746_;
v___y_2710_ = v___y_2743_;
v___y_2711_ = v___x_2754_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2709_ = v___x_2746_;
v___y_2710_ = v___y_2743_;
v___y_2711_ = v___x_2755_;
goto v___jp_2708_;
}
}
v___jp_2756_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = l_Array_append___redArg(v___x_2314_, v___y_2757_);
lean_dec_ref(v___y_2757_);
lean_inc(v___x_2309_);
v___x_2759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2309_);
lean_ctor_set(v___x_2759_, 1, v___x_2313_);
lean_ctor_set(v___x_2759_, 2, v___x_2758_);
if (lean_obj_tag(v_only_2263_) == 1)
{
lean_object* v_val_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_val_2760_ = lean_ctor_get(v_only_2263_, 0);
v___x_2761_ = l_Lean_SourceInfo_fromRef(v_val_2760_, v___x_2247_);
v___x_2762_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__11));
v___x_2763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Array_mkArray1___redArg(v___x_2763_);
v___y_2743_ = v___x_2759_;
v___y_2744_ = v___x_2764_;
goto v___jp_2742_;
}
else
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___y_2743_ = v___x_2759_;
v___y_2744_ = v___x_2765_;
goto v___jp_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object** _args){
lean_object* v_tk_2770_ = _args[0];
lean_object* v___x_2771_ = _args[1];
lean_object* v___x_2772_ = _args[2];
lean_object* v___x_2773_ = _args[3];
lean_object* v___x_2774_ = _args[4];
lean_object* v___x_2775_ = _args[5];
lean_object* v___x_2776_ = _args[6];
lean_object* v___x_2777_ = _args[7];
lean_object* v___f_2778_ = _args[8];
lean_object* v___x_2779_ = _args[9];
lean_object* v___x_2780_ = _args[10];
lean_object* v___x_2781_ = _args[11];
lean_object* v___x_2782_ = _args[12];
lean_object* v___x_2783_ = _args[13];
lean_object* v___x_2784_ = _args[14];
lean_object* v_usingArg_2785_ = _args[15];
lean_object* v___x_2786_ = _args[16];
lean_object* v___x_2787_ = _args[17];
lean_object* v_usingTk_x3f_2788_ = _args[18];
lean_object* v_squeeze_2789_ = _args[19];
lean_object* v_unfold_2790_ = _args[20];
lean_object* v_args_2791_ = _args[21];
lean_object* v_only_2792_ = _args[22];
lean_object* v___y_2793_ = _args[23];
lean_object* v___y_2794_ = _args[24];
lean_object* v___y_2795_ = _args[25];
lean_object* v___y_2796_ = _args[26];
lean_object* v___y_2797_ = _args[27];
lean_object* v___y_2798_ = _args[28];
lean_object* v___y_2799_ = _args[29];
lean_object* v___y_2800_ = _args[30];
lean_object* v___y_2801_ = _args[31];
lean_object* v___y_2802_ = _args[32];
_start:
{
uint8_t v___x_82020__boxed_2803_; uint8_t v___x_82030__boxed_2804_; lean_object* v_res_2805_; 
v___x_82020__boxed_2803_ = lean_unbox(v___x_2776_);
v___x_82030__boxed_2804_ = lean_unbox(v___x_2787_);
v_res_2805_ = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(v_tk_2770_, v___x_2771_, v___x_2772_, v___x_2773_, v___x_2774_, v___x_2775_, v___x_82020__boxed_2803_, v___x_2777_, v___f_2778_, v___x_2779_, v___x_2780_, v___x_2781_, v___x_2782_, v___x_2783_, v___x_2784_, v_usingArg_2785_, v___x_2786_, v___x_82030__boxed_2804_, v_usingTk_x3f_2788_, v_squeeze_2789_, v_unfold_2790_, v_args_2791_, v_only_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v_only_2792_);
lean_dec(v_args_2791_);
lean_dec(v_unfold_2790_);
lean_dec(v_squeeze_2789_);
lean_dec(v___x_2783_);
lean_dec(v___x_2781_);
lean_dec(v___x_2780_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_stx_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2842_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0));
v___x_2843_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1));
v___x_2844_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_2845_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2));
v___x_2846_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
lean_inc(v_stx_2832_);
v___x_2847_ = l_Lean_Syntax_isOfKind(v_stx_2832_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
lean_dec(v_stx_2832_);
v___x_2848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2848_;
}
else
{
lean_object* v___f_2849_; lean_object* v___x_2850_; lean_object* v_tk_2851_; lean_object* v___x_2852_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; uint8_t v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v_usingTk_x3f_2902_; lean_object* v_usingArg_2903_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; uint8_t v___y_2933_; lean_object* v___y_2934_; lean_object* v_args_2935_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v_only_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v_unfold_2991_; lean_object* v_squeeze_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___f_2849_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4));
v___x_2850_ = lean_unsigned_to_nat(0u);
v_tk_2851_ = l_Lean_Syntax_getArg(v_stx_2832_, v___x_2850_);
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_3027_ = l_Lean_Syntax_getArg(v_stx_2832_, v___x_2852_);
v___x_3028_ = l_Lean_Syntax_isNone(v___x_3027_);
if (v___x_3028_ == 0)
{
uint8_t v___x_3029_; 
lean_inc(v___x_3027_);
v___x_3029_ = l_Lean_Syntax_matchesNull(v___x_3027_, v___x_2852_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_dec(v___x_3027_);
lean_dec(v_tk_2851_);
lean_dec(v_stx_2832_);
v___x_3030_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3030_;
}
else
{
lean_object* v_squeeze_3031_; lean_object* v___x_3032_; 
v_squeeze_3031_ = l_Lean_Syntax_getArg(v___x_3027_, v___x_2850_);
lean_dec(v___x_3027_);
v___x_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3032_, 0, v_squeeze_3031_);
v_squeeze_3010_ = v___x_3032_;
v___y_3011_ = v_a_2833_;
v___y_3012_ = v_a_2834_;
v___y_3013_ = v_a_2835_;
v___y_3014_ = v_a_2836_;
v___y_3015_ = v_a_2837_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
goto v___jp_3009_;
}
}
else
{
lean_object* v___x_3033_; 
lean_dec(v___x_3027_);
v___x_3033_ = lean_box(0);
v_squeeze_3010_ = v___x_3033_;
v___y_3011_ = v_a_2833_;
v___y_3012_ = v_a_2834_;
v___y_3013_ = v_a_2835_;
v___y_3014_ = v_a_2836_;
v___y_3015_ = v_a_2837_;
v___y_3016_ = v_a_2838_;
v___y_3017_ = v_a_2839_;
v___y_3018_ = v_a_2840_;
goto v___jp_3009_;
}
v___jp_2853_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2876_ = lean_box(v___x_2847_);
v___x_2877_ = lean_box(v___y_2872_);
lean_inc(v___y_2866_);
lean_inc(v___y_2863_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 33, 24);
lean_closure_set(v___f_2878_, 0, v_tk_2851_);
lean_closure_set(v___f_2878_, 1, v___x_2842_);
lean_closure_set(v___f_2878_, 2, v___x_2843_);
lean_closure_set(v___f_2878_, 3, v___x_2844_);
lean_closure_set(v___f_2878_, 4, v___y_2863_);
lean_closure_set(v___f_2878_, 5, v___x_2850_);
lean_closure_set(v___f_2878_, 6, v___x_2876_);
lean_closure_set(v___f_2878_, 7, v___x_2846_);
lean_closure_set(v___f_2878_, 8, v___f_2849_);
lean_closure_set(v___f_2878_, 9, v___x_2845_);
lean_closure_set(v___f_2878_, 10, v___y_2854_);
lean_closure_set(v___f_2878_, 11, v___y_2864_);
lean_closure_set(v___f_2878_, 12, v___x_2852_);
lean_closure_set(v___f_2878_, 13, v___y_2866_);
lean_closure_set(v___f_2878_, 14, v___y_2862_);
lean_closure_set(v___f_2878_, 15, v___y_2860_);
lean_closure_set(v___f_2878_, 16, v___y_2856_);
lean_closure_set(v___f_2878_, 17, v___x_2877_);
lean_closure_set(v___f_2878_, 18, v___y_2873_);
lean_closure_set(v___f_2878_, 19, v___y_2861_);
lean_closure_set(v___f_2878_, 20, v___y_2855_);
lean_closure_set(v___f_2878_, 21, v___y_2857_);
lean_closure_set(v___f_2878_, 22, v___y_2870_);
lean_closure_set(v___f_2878_, 23, v___y_2875_);
v___x_2879_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_2879_, 0, v___f_2878_);
v___x_2880_ = l_Lean_Elab_Tactic_focus___redArg(v___x_2879_, v___y_2859_, v___y_2865_, v___y_2869_, v___y_2874_, v___y_2867_, v___y_2871_, v___y_2868_, v___y_2858_);
return v___x_2880_;
}
v___jp_2881_:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_Syntax_getOptional_x3f(v___y_2886_);
lean_dec(v___y_2886_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_box(0);
v___y_2854_ = v___y_2882_;
v___y_2855_ = v___y_2883_;
v___y_2856_ = v___y_2884_;
v___y_2857_ = v___y_2885_;
v___y_2858_ = v___y_2887_;
v___y_2859_ = v___y_2888_;
v___y_2860_ = v_usingArg_2903_;
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
v___y_2871_ = v___y_2900_;
v___y_2872_ = v___y_2899_;
v___y_2873_ = v_usingTk_x3f_2902_;
v___y_2874_ = v___y_2901_;
v___y_2875_ = v___x_2905_;
goto v___jp_2853_;
}
else
{
lean_object* v_val_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_val_2906_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2904_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_val_2906_);
lean_dec(v___x_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_val_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v___y_2854_ = v___y_2882_;
v___y_2855_ = v___y_2883_;
v___y_2856_ = v___y_2884_;
v___y_2857_ = v___y_2885_;
v___y_2858_ = v___y_2887_;
v___y_2859_ = v___y_2888_;
v___y_2860_ = v_usingArg_2903_;
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
v___y_2871_ = v___y_2900_;
v___y_2872_ = v___y_2899_;
v___y_2873_ = v_usingTk_x3f_2902_;
v___y_2874_ = v___y_2901_;
v___y_2875_ = v___x_2911_;
goto v___jp_2853_;
}
}
}
}
v___jp_2914_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2936_ = lean_unsigned_to_nat(4u);
v___x_2937_ = l_Lean_Syntax_getArg(v___y_2930_, v___x_2936_);
lean_dec(v___y_2930_);
v___x_2938_ = l_Lean_Syntax_isNone(v___x_2937_);
if (v___x_2938_ == 0)
{
uint8_t v___x_2939_; 
lean_inc(v___x_2937_);
v___x_2939_ = l_Lean_Syntax_matchesNull(v___x_2937_, v___y_2916_);
lean_dec(v___y_2916_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; 
lean_dec(v___x_2937_);
lean_dec(v_args_2935_);
lean_dec(v___y_2931_);
lean_dec(v___y_2924_);
lean_dec(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec(v___y_2915_);
lean_dec(v_tk_2851_);
v___x_2940_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2940_;
}
else
{
lean_object* v_usingTk_x3f_2941_; lean_object* v_usingArg_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_usingTk_x3f_2941_ = l_Lean_Syntax_getArg(v___x_2937_, v___x_2850_);
v_usingArg_2942_ = l_Lean_Syntax_getArg(v___x_2937_, v___x_2852_);
lean_dec(v___x_2937_);
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_usingTk_x3f_2941_);
v___x_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2944_, 0, v_usingArg_2942_);
v___y_2882_ = v___x_2936_;
v___y_2883_ = v___y_2915_;
v___y_2884_ = v___y_2917_;
v___y_2885_ = v_args_2935_;
v___y_2886_ = v___y_2918_;
v___y_2887_ = v___y_2919_;
v___y_2888_ = v___y_2920_;
v___y_2889_ = v___y_2921_;
v___y_2890_ = v___y_2922_;
v___y_2891_ = v___y_2923_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2927_;
v___y_2896_ = v___y_2928_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___y_2931_;
v___y_2899_ = v___y_2933_;
v___y_2900_ = v___y_2932_;
v___y_2901_ = v___y_2934_;
v_usingTk_x3f_2902_ = v___x_2943_;
v_usingArg_2903_ = v___x_2944_;
goto v___jp_2881_;
}
}
else
{
lean_object* v___x_2945_; 
lean_dec(v___x_2937_);
lean_dec(v___y_2916_);
v___x_2945_ = lean_box(0);
v___y_2882_ = v___x_2936_;
v___y_2883_ = v___y_2915_;
v___y_2884_ = v___y_2917_;
v___y_2885_ = v_args_2935_;
v___y_2886_ = v___y_2918_;
v___y_2887_ = v___y_2919_;
v___y_2888_ = v___y_2920_;
v___y_2889_ = v___y_2921_;
v___y_2890_ = v___y_2922_;
v___y_2891_ = v___y_2923_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2927_;
v___y_2896_ = v___y_2928_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___y_2931_;
v___y_2899_ = v___y_2933_;
v___y_2900_ = v___y_2932_;
v___y_2901_ = v___y_2934_;
v_usingTk_x3f_2902_ = v___x_2945_;
v_usingArg_2903_ = v___x_2945_;
goto v___jp_2881_;
}
}
v___jp_2946_:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = l_Lean_Syntax_getArg(v___y_2955_, v___y_2957_);
lean_dec(v___y_2957_);
v___x_2969_ = l_Lean_Syntax_isNone(v___x_2968_);
if (v___x_2969_ == 0)
{
uint8_t v___x_2970_; 
lean_inc(v___x_2968_);
v___x_2970_ = l_Lean_Syntax_matchesNull(v___x_2968_, v___x_2852_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; 
lean_dec(v___x_2968_);
lean_dec(v_only_2959_);
lean_dec(v___y_2958_);
lean_dec(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec(v___y_2953_);
lean_dec(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v_tk_2851_);
v___x_2971_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = l_Lean_Syntax_getArg(v___x_2968_, v___x_2850_);
lean_dec(v___x_2968_);
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5));
lean_inc(v___x_2972_);
v___x_2974_ = l_Lean_Syntax_isOfKind(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; 
lean_dec(v___x_2972_);
lean_dec(v_only_2959_);
lean_dec(v___y_2958_);
lean_dec(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec(v___y_2953_);
lean_dec(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec(v_tk_2851_);
v___x_2975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v_args_2977_; lean_object* v___x_2978_; 
v___x_2976_ = l_Lean_Syntax_getArg(v___x_2972_, v___x_2852_);
lean_dec(v___x_2972_);
v_args_2977_ = l_Lean_Syntax_getArgs(v___x_2976_);
lean_dec(v___x_2976_);
v___x_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_args_2977_);
v___y_2915_ = v___y_2948_;
v___y_2916_ = v___y_2956_;
v___y_2917_ = v___y_2949_;
v___y_2918_ = v___y_2958_;
v___y_2919_ = v___y_2967_;
v___y_2920_ = v___y_2960_;
v___y_2921_ = v___y_2950_;
v___y_2922_ = v___y_2951_;
v___y_2923_ = v___y_2952_;
v___y_2924_ = v___y_2953_;
v___y_2925_ = v___y_2961_;
v___y_2926_ = v___y_2947_;
v___y_2927_ = v___y_2964_;
v___y_2928_ = v___y_2966_;
v___y_2929_ = v___y_2962_;
v___y_2930_ = v___y_2955_;
v___y_2931_ = v_only_2959_;
v___y_2932_ = v___y_2965_;
v___y_2933_ = v___y_2954_;
v___y_2934_ = v___y_2963_;
v_args_2935_ = v___x_2978_;
goto v___jp_2914_;
}
}
}
else
{
lean_object* v___x_2979_; 
lean_dec(v___x_2968_);
v___x_2979_ = lean_box(0);
v___y_2915_ = v___y_2948_;
v___y_2916_ = v___y_2956_;
v___y_2917_ = v___y_2949_;
v___y_2918_ = v___y_2958_;
v___y_2919_ = v___y_2967_;
v___y_2920_ = v___y_2960_;
v___y_2921_ = v___y_2950_;
v___y_2922_ = v___y_2951_;
v___y_2923_ = v___y_2952_;
v___y_2924_ = v___y_2953_;
v___y_2925_ = v___y_2961_;
v___y_2926_ = v___y_2947_;
v___y_2927_ = v___y_2964_;
v___y_2928_ = v___y_2966_;
v___y_2929_ = v___y_2962_;
v___y_2930_ = v___y_2955_;
v___y_2931_ = v_only_2959_;
v___y_2932_ = v___y_2965_;
v___y_2933_ = v___y_2954_;
v___y_2934_ = v___y_2963_;
v_args_2935_ = v___x_2979_;
goto v___jp_2914_;
}
}
v___jp_2980_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2992_ = lean_unsigned_to_nat(3u);
v___x_2993_ = l_Lean_Syntax_getArg(v_stx_2832_, v___x_2992_);
lean_dec(v_stx_2832_);
v___x_2994_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7));
lean_inc(v___x_2993_);
v___x_2995_ = l_Lean_Syntax_isOfKind(v___x_2993_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v___x_2993_);
lean_dec(v_unfold_2991_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v_tk_2851_);
v___x_2996_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_2996_;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v___x_2997_ = l_Lean_Syntax_getArg(v___x_2993_, v___x_2850_);
v___x_2998_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9));
lean_inc(v___x_2997_);
v___x_2999_ = l_Lean_Syntax_isOfKind(v___x_2997_, v___x_2998_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v___x_2997_);
lean_dec(v___x_2993_);
lean_dec(v_unfold_2991_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v_tk_2851_);
v___x_3000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3001_ = l_Lean_Syntax_getArg(v___x_2993_, v___x_2852_);
v___x_3002_ = l_Lean_Syntax_getArg(v___x_2993_, v___y_2988_);
v___x_3003_ = l_Lean_Syntax_isNone(v___x_3002_);
if (v___x_3003_ == 0)
{
uint8_t v___x_3004_; 
lean_inc(v___x_3002_);
v___x_3004_ = l_Lean_Syntax_matchesNull(v___x_3002_, v___x_2852_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
lean_dec(v___x_3002_);
lean_dec(v___x_3001_);
lean_dec(v___x_2997_);
lean_dec(v___x_2993_);
lean_dec(v_unfold_2991_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec(v_tk_2851_);
v___x_3005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3005_;
}
else
{
lean_object* v_only_3006_; lean_object* v___x_3007_; 
v_only_3006_ = l_Lean_Syntax_getArg(v___x_3002_, v___x_2850_);
lean_dec(v___x_3002_);
v___x_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_only_3006_);
lean_inc(v___y_2988_);
v___y_2947_ = v___x_2998_;
v___y_2948_ = v_unfold_2991_;
v___y_2949_ = v___x_2997_;
v___y_2950_ = v___y_2987_;
v___y_2951_ = v___y_2988_;
v___y_2952_ = v___x_2994_;
v___y_2953_ = v___x_2992_;
v___y_2954_ = v___x_2999_;
v___y_2955_ = v___x_2993_;
v___y_2956_ = v___y_2988_;
v___y_2957_ = v___x_2992_;
v___y_2958_ = v___x_3001_;
v_only_2959_ = v___x_3007_;
v___y_2960_ = v___y_2984_;
v___y_2961_ = v___y_2986_;
v___y_2962_ = v___y_2982_;
v___y_2963_ = v___y_2983_;
v___y_2964_ = v___y_2981_;
v___y_2965_ = v___y_2989_;
v___y_2966_ = v___y_2985_;
v___y_2967_ = v___y_2990_;
goto v___jp_2946_;
}
}
else
{
lean_object* v___x_3008_; 
lean_dec(v___x_3002_);
v___x_3008_ = lean_box(0);
lean_inc(v___y_2988_);
v___y_2947_ = v___x_2998_;
v___y_2948_ = v_unfold_2991_;
v___y_2949_ = v___x_2997_;
v___y_2950_ = v___y_2987_;
v___y_2951_ = v___y_2988_;
v___y_2952_ = v___x_2994_;
v___y_2953_ = v___x_2992_;
v___y_2954_ = v___x_2999_;
v___y_2955_ = v___x_2993_;
v___y_2956_ = v___y_2988_;
v___y_2957_ = v___x_2992_;
v___y_2958_ = v___x_3001_;
v_only_2959_ = v___x_3008_;
v___y_2960_ = v___y_2984_;
v___y_2961_ = v___y_2986_;
v___y_2962_ = v___y_2982_;
v___y_2963_ = v___y_2983_;
v___y_2964_ = v___y_2981_;
v___y_2965_ = v___y_2989_;
v___y_2966_ = v___y_2985_;
v___y_2967_ = v___y_2990_;
goto v___jp_2946_;
}
}
}
}
v___jp_3009_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3019_ = lean_unsigned_to_nat(2u);
v___x_3020_ = l_Lean_Syntax_getArg(v_stx_2832_, v___x_3019_);
v___x_3021_ = l_Lean_Syntax_isNone(v___x_3020_);
if (v___x_3021_ == 0)
{
uint8_t v___x_3022_; 
lean_inc(v___x_3020_);
v___x_3022_ = l_Lean_Syntax_matchesNull(v___x_3020_, v___x_2852_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
lean_dec(v___x_3020_);
lean_dec(v_squeeze_3010_);
lean_dec(v_tk_2851_);
lean_dec(v_stx_2832_);
v___x_3023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___redArg();
return v___x_3023_;
}
else
{
lean_object* v_unfold_3024_; lean_object* v___x_3025_; 
v_unfold_3024_ = l_Lean_Syntax_getArg(v___x_3020_, v___x_2850_);
lean_dec(v___x_3020_);
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_unfold_3024_);
v___y_2981_ = v___y_3015_;
v___y_2982_ = v___y_3013_;
v___y_2983_ = v___y_3014_;
v___y_2984_ = v___y_3011_;
v___y_2985_ = v___y_3017_;
v___y_2986_ = v___y_3012_;
v___y_2987_ = v_squeeze_3010_;
v___y_2988_ = v___x_3019_;
v___y_2989_ = v___y_3016_;
v___y_2990_ = v___y_3018_;
v_unfold_2991_ = v___x_3025_;
goto v___jp_2980_;
}
}
else
{
lean_object* v___x_3026_; 
lean_dec(v___x_3020_);
v___x_3026_ = lean_box(0);
v___y_2981_ = v___y_3015_;
v___y_2982_ = v___y_3013_;
v___y_2983_ = v___y_3014_;
v___y_2984_ = v___y_3011_;
v___y_2985_ = v___y_3017_;
v___y_2986_ = v___y_3012_;
v___y_2987_ = v_squeeze_3010_;
v___y_2988_ = v___x_3019_;
v___y_2989_ = v___y_3016_;
v___y_2990_ = v___y_3018_;
v_unfold_2991_ = v___x_3026_;
goto v___jp_2980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_stx_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_stx_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(lean_object* v_mvarId_3045_, lean_object* v_val_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___redArg(v_mvarId_3045_, v_val_3046_, v___y_3052_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2___boxed(lean_object* v_mvarId_3057_, lean_object* v_val_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2(v_mvarId_3057_, v_val_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(lean_object* v_o_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___redArg(v_o_3069_, v___y_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5___boxed(lean_object* v_o_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__5(v_o_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(lean_object* v_00_u03b1_3091_, lean_object* v_msg_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___redArg(v_msg_3092_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6___boxed(lean_object* v_00_u03b1_3103_, lean_object* v_msg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__6(v_00_u03b1_3103_, v_msg_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(lean_object* v_00_u03b1_3115_, lean_object* v_x_3116_, lean_object* v_mkInfoTree_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___redArg(v_x_3116_, v_mkInfoTree_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8___boxed(lean_object* v_00_u03b1_3128_, lean_object* v_x_3129_, lean_object* v_mkInfoTree_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__8(v_00_u03b1_3128_, v_x_3129_, v_mkInfoTree_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3(lean_object* v_00_u03b2_3141_, lean_object* v_x_3142_, lean_object* v_x_3143_, lean_object* v_x_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3___redArg(v_x_3142_, v_x_3143_, v_x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3146_, lean_object* v_m_3147_, lean_object* v_a_3148_){
_start:
{
uint8_t v___x_3149_; 
v___x_3149_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___redArg(v_m_3147_, v_a_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3150_, lean_object* v_m_3151_, lean_object* v_a_3152_){
_start:
{
uint8_t v_res_3153_; lean_object* v_r_3154_; 
v_res_3153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6(v_00_u03b2_3150_, v_m_3151_, v_a_3152_);
lean_dec_ref(v_a_3152_);
lean_dec_ref(v_m_3151_);
v_r_3154_ = lean_box(v_res_3153_);
return v_r_3154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3155_, lean_object* v_m_3156_, lean_object* v_a_3157_, lean_object* v_b_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7___redArg(v_m_3156_, v_a_3157_, v_b_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3160_, v___y_3161_, v___y_3167_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__18(v_mvarId_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v_mvarId_3172_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3184_, v___y_3185_, v___y_3191_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__8_spec__19(v_mvarId_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v_mvarId_3196_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3208_, lean_object* v_x_3209_, size_t v_x_3210_, size_t v_x_3211_, lean_object* v_x_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___redArg(v_x_3209_, v_x_3210_, v_x_3211_, v_x_3212_, v_x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_){
_start:
{
size_t v_x_83810__boxed_3221_; size_t v_x_83811__boxed_3222_; lean_object* v_res_3223_; 
v_x_83810__boxed_3221_ = lean_unbox_usize(v_x_3217_);
lean_dec(v_x_3217_);
v_x_83811__boxed_3222_ = lean_unbox_usize(v_x_3218_);
lean_dec(v_x_3218_);
v_res_3223_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11(v_00_u03b2_3215_, v_x_3216_, v_x_83810__boxed_3221_, v_x_83811__boxed_3222_, v_x_3219_, v_x_3220_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(lean_object* v_ref_3224_, lean_object* v_msgData_3225_, uint8_t v_severity_3226_, uint8_t v_isSilent_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___redArg(v_ref_3224_, v_msgData_3225_, v_severity_3226_, v_isSilent_3227_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3238_, lean_object* v_msgData_3239_, lean_object* v_severity_3240_, lean_object* v_isSilent_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_severity_boxed_3251_; uint8_t v_isSilent_boxed_3252_; lean_object* v_res_3253_; 
v_severity_boxed_3251_ = lean_unbox(v_severity_3240_);
v_isSilent_boxed_3252_ = lean_unbox(v_isSilent_3241_);
v_res_3253_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__4_spec__7_spec__16(v_ref_3238_, v_msgData_3239_, v_severity_boxed_3251_, v_isSilent_boxed_3252_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v_ref_3238_);
return v_res_3253_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3254_, lean_object* v_a_3255_, lean_object* v_x_3256_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3255_, v_x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3258_, lean_object* v_a_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_res_3261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3258_, v_a_3259_, v_x_3260_);
lean_dec(v_x_3260_);
lean_dec_ref(v_a_3259_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3263_, lean_object* v_data_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3266_, lean_object* v_n_3267_, lean_object* v_k_3268_, lean_object* v_v_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3267_, v_k_3268_, v_v_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3271_, size_t v_depth_3272_, lean_object* v_keys_3273_, lean_object* v_vals_3274_, lean_object* v_heq_3275_, lean_object* v_i_3276_, lean_object* v_entries_3277_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3272_, v_keys_3273_, v_vals_3274_, v_i_3276_, v_entries_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3279_, lean_object* v_depth_3280_, lean_object* v_keys_3281_, lean_object* v_vals_3282_, lean_object* v_heq_3283_, lean_object* v_i_3284_, lean_object* v_entries_3285_){
_start:
{
size_t v_depth_boxed_3286_; lean_object* v_res_3287_; 
v_depth_boxed_3286_ = lean_unbox_usize(v_depth_3280_);
lean_dec(v_depth_3280_);
v_res_3287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3279_, v_depth_boxed_3286_, v_keys_3281_, v_vals_3282_, v_heq_3283_, v_i_3284_, v_entries_3285_);
lean_dec_ref(v_vals_3282_);
lean_dec_ref(v_keys_3281_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3288_, lean_object* v_i_3289_, lean_object* v_source_3290_, lean_object* v_target_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3289_, v_source_3290_, v_target_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3294_, v_x_3295_, v_x_3296_, v_x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3300_, v_x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3312_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3313_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3));
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3315_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3316_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3312_, v___x_3313_, v___x_3314_, v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3347_ = l_Lean_addBuiltinDeclarationRanges(v___x_3345_, v___x_3346_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3349_;
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
