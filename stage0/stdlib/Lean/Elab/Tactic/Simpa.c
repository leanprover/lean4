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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Type mismatch: After simplification, term"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0;
static lean_once_cell_t l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Try `simp at "};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` instead of `simpa using "};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Occurs check failed: Expression"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\ncontains the goal "};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12_value),LEAN_SCALAR_PTR_LITERAL(38, 116, 214, 236, 212, 160, 188, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "try 'simp' instead of 'simpa'"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.Tactic.Simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Elab.Tactic.Simpa.0.Lean.Elab.Tactic.Simpa.evalSimpaCore"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "using"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "using!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpaUsingBang"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "simpaUsingBangArgsRest"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticSimpa!_"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simpa!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22;
static const lean_closure_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 186, 141, 63, 66, 208, 56, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value),LEAN_SCALAR_PTR_LITERAL(158, 198, 190, 154, 66, 126, 242, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpaArgsRest"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(137, 133, 181, 17, 86, 74, 251, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalSimpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
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
static const lean_array_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value),LEAN_SCALAR_PTR_LITERAL(207, 241, 251, 37, 131, 174, 231, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value),LEAN_SCALAR_PTR_LITERAL(8, 141, 117, 125, 176, 67, 228, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "evalSimpaUsingBang"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 230, 37, 137, 25, 71, 189, 138)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 14, 13, 235, 216, 153, 126, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object*);
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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0(lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0___boxed(lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0(v_x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_mvarId_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; 
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0___boxed), 10, 5);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_mvarId_130_, lean_object* v_x_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_mvarId_130_, v_x_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_142_, lean_object* v_mvarId_143_, lean_object* v_x_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_mvarId_143_, v_x_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_155_, lean_object* v_mvarId_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_155_, v_mvarId_156_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
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
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0(void){
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
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((size_t)5ULL);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_unsigned_to_nat(32u);
v___x_174_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0);
v___x_176_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_172_);
lean_ctor_set(v___x_176_, 3, v___x_172_);
lean_ctor_set_usize(v___x_176_, 4, v___x_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v___y_177_){
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
v___x_201_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_213_);
lean_dec(v___y_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_80917__overap_248_; lean_object* v___x_249_; 
v___f_247_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0));
v___x_80917__overap_248_ = lean_panic_fn_borrowed(v___f_247_, v_msg_237_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
v___x_249_ = lean_apply_9(v___x_80917__overap_248_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, lean_box(0));
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___boxed(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(lean_object* v_opts_261_, lean_object* v_opt_262_){
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
lean_dec_ref_known(v___x_266_, 1);
if (lean_obj_tag(v_val_268_) == 1)
{
uint8_t v_v_269_; 
v_v_269_ = lean_ctor_get_uint8(v_val_268_, 0);
lean_dec_ref_known(v_val_268_, 0);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10___boxed(lean_object* v_opts_271_, lean_object* v_opt_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_opts_271_, v_opt_272_);
lean_dec_ref(v_opt_272_);
lean_dec_ref(v_opts_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v_a_298_, lean_object* v_trees_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object* v_a_327_, lean_object* v_trees_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v_a_327_, v_trees_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4(void){
_start:
{
uint8_t v___x_345_; uint64_t v___x_346_; 
v___x_345_ = 2;
v___x_346_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_347_, lean_object* v_a_348_, uint8_t v___x_349_, uint8_t v___x_350_, lean_object* v_a_351_, lean_object* v_mvarCounter_352_, lean_object* v___x_353_, lean_object* v___x_354_, uint8_t v_useReducible_355_, uint8_t v___x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; 
lean_inc(v_a_347_);
v___x_366_ = l_Lean_MVarId_getType(v_a_347_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_n(v_a_367_, 2);
lean_dec_ref_known(v___x_366_, 1);
v___x_368_ = lean_mk_syntax_ident(v_a_348_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_a_367_);
v___x_370_ = l_Lean_Elab_Term_elabTerm(v___x_368_, v___x_369_, v___x_349_, v___x_349_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___x_405_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_405_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_350_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_405_, 0);
lean_dec(v_unused_560_);
v___x_407_ = v___x_405_;
v_isShared_408_ = v_isSharedCheck_559_;
goto v_resetjp_406_;
}
else
{
lean_dec(v___x_405_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_559_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; 
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v___y_362_);
lean_inc_ref(v___y_361_);
lean_inc(v_a_371_);
v___x_409_ = lean_infer_type(v_a_371_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; uint8_t v_a_412_; lean_object* v___y_423_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
if (v_useReducible_355_ == 0)
{
lean_object* v___x_434_; uint8_t v_foApprox_435_; uint8_t v_ctxApprox_436_; uint8_t v_quasiPatternApprox_437_; uint8_t v_constApprox_438_; uint8_t v_isDefEqStuckEx_439_; uint8_t v_unificationHints_440_; uint8_t v_proofIrrelevance_441_; uint8_t v_offsetCnstrs_442_; uint8_t v_transparency_443_; uint8_t v_etaStruct_444_; uint8_t v_univApprox_445_; uint8_t v_iota_446_; uint8_t v_beta_447_; uint8_t v_proj_448_; uint8_t v_zeta_449_; uint8_t v_zetaDelta_450_; uint8_t v_zetaUnused_451_; uint8_t v_zetaHave_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_473_; 
v___x_434_ = l_Lean_Meta_Context_config(v___y_361_);
v_foApprox_435_ = lean_ctor_get_uint8(v___x_434_, 0);
v_ctxApprox_436_ = lean_ctor_get_uint8(v___x_434_, 1);
v_quasiPatternApprox_437_ = lean_ctor_get_uint8(v___x_434_, 2);
v_constApprox_438_ = lean_ctor_get_uint8(v___x_434_, 3);
v_isDefEqStuckEx_439_ = lean_ctor_get_uint8(v___x_434_, 4);
v_unificationHints_440_ = lean_ctor_get_uint8(v___x_434_, 5);
v_proofIrrelevance_441_ = lean_ctor_get_uint8(v___x_434_, 6);
v_offsetCnstrs_442_ = lean_ctor_get_uint8(v___x_434_, 8);
v_transparency_443_ = lean_ctor_get_uint8(v___x_434_, 9);
v_etaStruct_444_ = lean_ctor_get_uint8(v___x_434_, 10);
v_univApprox_445_ = lean_ctor_get_uint8(v___x_434_, 11);
v_iota_446_ = lean_ctor_get_uint8(v___x_434_, 12);
v_beta_447_ = lean_ctor_get_uint8(v___x_434_, 13);
v_proj_448_ = lean_ctor_get_uint8(v___x_434_, 14);
v_zeta_449_ = lean_ctor_get_uint8(v___x_434_, 15);
v_zetaDelta_450_ = lean_ctor_get_uint8(v___x_434_, 16);
v_zetaUnused_451_ = lean_ctor_get_uint8(v___x_434_, 17);
v_zetaHave_452_ = lean_ctor_get_uint8(v___x_434_, 18);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_473_ == 0)
{
v___x_454_ = v___x_434_;
v_isShared_455_ = v_isSharedCheck_473_;
goto v_resetjp_453_;
}
else
{
lean_dec(v___x_434_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_473_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v_trackZetaDelta_456_; lean_object* v_zetaDeltaSet_457_; lean_object* v_lctx_458_; lean_object* v_localInstances_459_; lean_object* v_defEqCtx_x3f_460_; lean_object* v_synthPendingDepth_461_; lean_object* v_canUnfold_x3f_462_; uint8_t v_univApprox_463_; uint8_t v_inTypeClassResolution_464_; uint8_t v_cacheInferType_465_; lean_object* v___x_467_; 
v_trackZetaDelta_456_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7);
v_zetaDeltaSet_457_ = lean_ctor_get(v___y_361_, 1);
v_lctx_458_ = lean_ctor_get(v___y_361_, 2);
v_localInstances_459_ = lean_ctor_get(v___y_361_, 3);
v_defEqCtx_x3f_460_ = lean_ctor_get(v___y_361_, 4);
v_synthPendingDepth_461_ = lean_ctor_get(v___y_361_, 5);
v_canUnfold_x3f_462_ = lean_ctor_get(v___y_361_, 6);
v_univApprox_463_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_464_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 2);
v_cacheInferType_465_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 3);
if (v_isShared_455_ == 0)
{
v___x_467_ = v___x_454_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 0, v_foApprox_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 1, v_ctxApprox_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 2, v_quasiPatternApprox_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 3, v_constApprox_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 4, v_isDefEqStuckEx_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 5, v_unificationHints_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 6, v_proofIrrelevance_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 8, v_offsetCnstrs_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 9, v_transparency_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 10, v_etaStruct_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 11, v_univApprox_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 12, v_iota_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 13, v_beta_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 14, v_proj_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 15, v_zeta_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 16, v_zetaDelta_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 17, v_zetaUnused_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, 18, v_zetaHave_452_);
v___x_467_ = v_reuseFailAlloc_472_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
uint64_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_ctor_set_uint8(v___x_467_, 7, v___x_356_);
v___x_468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set_uint64(v___x_469_, sizeof(void*)*1, v___x_468_);
lean_inc(v_canUnfold_x3f_462_);
lean_inc(v_synthPendingDepth_461_);
lean_inc(v_defEqCtx_x3f_460_);
lean_inc_ref(v_localInstances_459_);
lean_inc_ref(v_lctx_458_);
lean_inc(v_zetaDeltaSet_457_);
v___x_470_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_zetaDeltaSet_457_);
lean_ctor_set(v___x_470_, 2, v_lctx_458_);
lean_ctor_set(v___x_470_, 3, v_localInstances_459_);
lean_ctor_set(v___x_470_, 4, v_defEqCtx_x3f_460_);
lean_ctor_set(v___x_470_, 5, v_synthPendingDepth_461_);
lean_ctor_set(v___x_470_, 6, v_canUnfold_x3f_462_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*7, v_trackZetaDelta_456_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*7 + 1, v_univApprox_463_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*7 + 2, v_inTypeClassResolution_464_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*7 + 3, v_cacheInferType_465_);
lean_inc(v_a_410_);
lean_inc(v_a_367_);
v___x_471_ = l_Lean_Meta_isExprDefEq(v_a_367_, v_a_410_, v___x_470_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref_known(v___x_470_, 7);
v___y_423_ = v___x_471_;
goto v___jp_422_;
}
}
}
else
{
lean_object* v___x_474_; uint8_t v_foApprox_475_; uint8_t v_ctxApprox_476_; uint8_t v_quasiPatternApprox_477_; uint8_t v_constApprox_478_; uint8_t v_isDefEqStuckEx_479_; uint8_t v_unificationHints_480_; uint8_t v_proofIrrelevance_481_; uint8_t v_assignSyntheticOpaque_482_; uint8_t v_offsetCnstrs_483_; uint8_t v_etaStruct_484_; uint8_t v_univApprox_485_; uint8_t v_iota_486_; uint8_t v_beta_487_; uint8_t v_proj_488_; uint8_t v_zeta_489_; uint8_t v_zetaDelta_490_; uint8_t v_zetaUnused_491_; uint8_t v_zetaHave_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_550_; 
v___x_474_ = l_Lean_Meta_Context_config(v___y_361_);
v_foApprox_475_ = lean_ctor_get_uint8(v___x_474_, 0);
v_ctxApprox_476_ = lean_ctor_get_uint8(v___x_474_, 1);
v_quasiPatternApprox_477_ = lean_ctor_get_uint8(v___x_474_, 2);
v_constApprox_478_ = lean_ctor_get_uint8(v___x_474_, 3);
v_isDefEqStuckEx_479_ = lean_ctor_get_uint8(v___x_474_, 4);
v_unificationHints_480_ = lean_ctor_get_uint8(v___x_474_, 5);
v_proofIrrelevance_481_ = lean_ctor_get_uint8(v___x_474_, 6);
v_assignSyntheticOpaque_482_ = lean_ctor_get_uint8(v___x_474_, 7);
v_offsetCnstrs_483_ = lean_ctor_get_uint8(v___x_474_, 8);
v_etaStruct_484_ = lean_ctor_get_uint8(v___x_474_, 10);
v_univApprox_485_ = lean_ctor_get_uint8(v___x_474_, 11);
v_iota_486_ = lean_ctor_get_uint8(v___x_474_, 12);
v_beta_487_ = lean_ctor_get_uint8(v___x_474_, 13);
v_proj_488_ = lean_ctor_get_uint8(v___x_474_, 14);
v_zeta_489_ = lean_ctor_get_uint8(v___x_474_, 15);
v_zetaDelta_490_ = lean_ctor_get_uint8(v___x_474_, 16);
v_zetaUnused_491_ = lean_ctor_get_uint8(v___x_474_, 17);
v_zetaHave_492_ = lean_ctor_get_uint8(v___x_474_, 18);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_550_ == 0)
{
v___x_494_ = v___x_474_;
v_isShared_495_ = v_isSharedCheck_550_;
goto v_resetjp_493_;
}
else
{
lean_dec(v___x_474_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_550_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
uint8_t v_trackZetaDelta_496_; lean_object* v_zetaDeltaSet_497_; lean_object* v_lctx_498_; lean_object* v_localInstances_499_; lean_object* v_defEqCtx_x3f_500_; lean_object* v_synthPendingDepth_501_; lean_object* v_canUnfold_x3f_502_; uint8_t v_univApprox_503_; uint8_t v_inTypeClassResolution_504_; uint8_t v_cacheInferType_505_; uint8_t v___x_506_; lean_object* v_config_508_; 
v_trackZetaDelta_496_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7);
v_zetaDeltaSet_497_ = lean_ctor_get(v___y_361_, 1);
v_lctx_498_ = lean_ctor_get(v___y_361_, 2);
v_localInstances_499_ = lean_ctor_get(v___y_361_, 3);
v_defEqCtx_x3f_500_ = lean_ctor_get(v___y_361_, 4);
v_synthPendingDepth_501_ = lean_ctor_get(v___y_361_, 5);
v_canUnfold_x3f_502_ = lean_ctor_get(v___y_361_, 6);
v_univApprox_503_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_504_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 2);
v_cacheInferType_505_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 3);
v___x_506_ = 2;
if (v_isShared_495_ == 0)
{
v_config_508_ = v___x_494_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 0, v_foApprox_475_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 1, v_ctxApprox_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 2, v_quasiPatternApprox_477_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 3, v_constApprox_478_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 4, v_isDefEqStuckEx_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 5, v_unificationHints_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 6, v_proofIrrelevance_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 7, v_assignSyntheticOpaque_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 8, v_offsetCnstrs_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 10, v_etaStruct_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 11, v_univApprox_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 12, v_iota_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 13, v_beta_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 14, v_proj_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 15, v_zeta_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 16, v_zetaDelta_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 17, v_zetaUnused_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, 18, v_zetaHave_492_);
v_config_508_ = v_reuseFailAlloc_549_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v_key_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v_foApprox_518_; uint8_t v_ctxApprox_519_; uint8_t v_quasiPatternApprox_520_; uint8_t v_constApprox_521_; uint8_t v_isDefEqStuckEx_522_; uint8_t v_unificationHints_523_; uint8_t v_proofIrrelevance_524_; uint8_t v_offsetCnstrs_525_; uint8_t v_transparency_526_; uint8_t v_etaStruct_527_; uint8_t v_univApprox_528_; uint8_t v_iota_529_; uint8_t v_beta_530_; uint8_t v_proj_531_; uint8_t v_zeta_532_; uint8_t v_zetaDelta_533_; uint8_t v_zetaUnused_534_; uint8_t v_zetaHave_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_548_; 
lean_ctor_set_uint8(v_config_508_, 9, v___x_506_);
v___x_509_ = l_Lean_Meta_Context_configKey(v___y_361_);
v___x_510_ = 3ULL;
v___x_511_ = lean_uint64_shift_right(v___x_509_, v___x_510_);
v___x_512_ = lean_uint64_shift_left(v___x_511_, v___x_510_);
v___x_513_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4);
v_key_514_ = lean_uint64_lor(v___x_512_, v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_515_, 0, v_config_508_);
lean_ctor_set_uint64(v___x_515_, sizeof(void*)*1, v_key_514_);
lean_inc(v_canUnfold_x3f_502_);
lean_inc(v_synthPendingDepth_501_);
lean_inc(v_defEqCtx_x3f_500_);
lean_inc_ref(v_localInstances_499_);
lean_inc_ref(v_lctx_498_);
lean_inc(v_zetaDeltaSet_497_);
v___x_516_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v_zetaDeltaSet_497_);
lean_ctor_set(v___x_516_, 2, v_lctx_498_);
lean_ctor_set(v___x_516_, 3, v_localInstances_499_);
lean_ctor_set(v___x_516_, 4, v_defEqCtx_x3f_500_);
lean_ctor_set(v___x_516_, 5, v_synthPendingDepth_501_);
lean_ctor_set(v___x_516_, 6, v_canUnfold_x3f_502_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*7, v_trackZetaDelta_496_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*7 + 1, v_univApprox_503_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*7 + 2, v_inTypeClassResolution_504_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*7 + 3, v_cacheInferType_505_);
v___x_517_ = l_Lean_Meta_Context_config(v___x_516_);
lean_dec_ref_known(v___x_516_, 7);
v_foApprox_518_ = lean_ctor_get_uint8(v___x_517_, 0);
v_ctxApprox_519_ = lean_ctor_get_uint8(v___x_517_, 1);
v_quasiPatternApprox_520_ = lean_ctor_get_uint8(v___x_517_, 2);
v_constApprox_521_ = lean_ctor_get_uint8(v___x_517_, 3);
v_isDefEqStuckEx_522_ = lean_ctor_get_uint8(v___x_517_, 4);
v_unificationHints_523_ = lean_ctor_get_uint8(v___x_517_, 5);
v_proofIrrelevance_524_ = lean_ctor_get_uint8(v___x_517_, 6);
v_offsetCnstrs_525_ = lean_ctor_get_uint8(v___x_517_, 8);
v_transparency_526_ = lean_ctor_get_uint8(v___x_517_, 9);
v_etaStruct_527_ = lean_ctor_get_uint8(v___x_517_, 10);
v_univApprox_528_ = lean_ctor_get_uint8(v___x_517_, 11);
v_iota_529_ = lean_ctor_get_uint8(v___x_517_, 12);
v_beta_530_ = lean_ctor_get_uint8(v___x_517_, 13);
v_proj_531_ = lean_ctor_get_uint8(v___x_517_, 14);
v_zeta_532_ = lean_ctor_get_uint8(v___x_517_, 15);
v_zetaDelta_533_ = lean_ctor_get_uint8(v___x_517_, 16);
v_zetaUnused_534_ = lean_ctor_get_uint8(v___x_517_, 17);
v_zetaHave_535_ = lean_ctor_get_uint8(v___x_517_, 18);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_548_ == 0)
{
v___x_537_ = v___x_517_;
v_isShared_538_ = v_isSharedCheck_548_;
goto v_resetjp_536_;
}
else
{
lean_dec(v___x_517_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_548_;
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
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 0, v_foApprox_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 1, v_ctxApprox_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 2, v_quasiPatternApprox_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 3, v_constApprox_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 4, v_isDefEqStuckEx_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 5, v_unificationHints_523_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 6, v_proofIrrelevance_524_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 8, v_offsetCnstrs_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 9, v_transparency_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 10, v_etaStruct_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 11, v_univApprox_528_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 12, v_iota_529_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 13, v_beta_530_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 14, v_proj_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 15, v_zeta_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 16, v_zetaDelta_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 17, v_zetaUnused_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_547_, 18, v_zetaHave_535_);
v___x_540_ = v_reuseFailAlloc_547_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
uint64_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_ctor_set_uint8(v___x_540_, 7, v___x_356_);
v___x_541_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint64(v___x_542_, sizeof(void*)*1, v___x_541_);
lean_inc(v_canUnfold_x3f_502_);
lean_inc(v_synthPendingDepth_501_);
lean_inc(v_defEqCtx_x3f_500_);
lean_inc_ref(v_localInstances_499_);
lean_inc_ref(v_lctx_498_);
lean_inc(v_zetaDeltaSet_497_);
v___x_543_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v_zetaDeltaSet_497_);
lean_ctor_set(v___x_543_, 2, v_lctx_498_);
lean_ctor_set(v___x_543_, 3, v_localInstances_499_);
lean_ctor_set(v___x_543_, 4, v_defEqCtx_x3f_500_);
lean_ctor_set(v___x_543_, 5, v_synthPendingDepth_501_);
lean_ctor_set(v___x_543_, 6, v_canUnfold_x3f_502_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*7, v_trackZetaDelta_496_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*7 + 1, v_univApprox_503_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*7 + 2, v_inTypeClassResolution_504_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*7 + 3, v_cacheInferType_505_);
lean_inc(v_a_410_);
lean_inc(v_a_367_);
v___x_544_ = l_Lean_Meta_isExprDefEq(v_a_367_, v_a_410_, v___x_543_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref_known(v___x_543_, 7);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; uint8_t v___x_546_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = lean_unbox(v_a_545_);
lean_dec(v_a_545_);
v_a_412_ = v___x_546_;
goto v___jp_411_;
}
else
{
v___y_423_ = v___x_544_;
goto v___jp_422_;
}
}
}
}
}
}
v___jp_411_:
{
if (v_a_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_413_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1);
lean_inc_ref(v_a_351_);
v___x_414_ = l_Lean_indentExpr(v_a_351_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 1);
lean_ctor_set(v___x_407_, 0, v___x_417_);
v___x_419_ = v___x_407_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_421_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; 
lean_inc(v_a_371_);
v___x_420_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_419_, v_a_367_, v_a_410_, v_a_371_, v___x_354_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref(v___x_419_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_dec_ref_known(v___x_420_, 1);
v___y_373_ = v___y_357_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
v___y_378_ = v___y_362_;
v___y_379_ = v___y_363_;
v___y_380_ = v___y_364_;
goto v___jp_372_;
}
else
{
lean_dec(v_a_371_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
return v___x_420_;
}
}
}
else
{
lean_dec(v_a_410_);
lean_del_object(v___x_407_);
lean_dec(v_a_367_);
lean_dec(v___x_354_);
v___y_373_ = v___y_357_;
v___y_374_ = v___y_358_;
v___y_375_ = v___y_359_;
v___y_376_ = v___y_360_;
v___y_377_ = v___y_361_;
v___y_378_ = v___y_362_;
v___y_379_ = v___y_363_;
v___y_380_ = v___y_364_;
goto v___jp_372_;
}
}
v___jp_422_:
{
if (lean_obj_tag(v___y_423_) == 0)
{
lean_object* v_a_424_; uint8_t v___x_425_; 
v_a_424_ = lean_ctor_get(v___y_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___y_423_, 1);
v___x_425_ = lean_unbox(v_a_424_);
lean_dec(v_a_424_);
v_a_412_ = v___x_425_;
goto v___jp_411_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_a_410_);
lean_del_object(v___x_407_);
lean_dec(v_a_371_);
lean_dec(v_a_367_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
v_a_426_ = lean_ctor_get(v___y_423_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___y_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___y_423_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___y_423_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_del_object(v___x_407_);
lean_dec(v_a_371_);
lean_dec(v_a_367_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
v_a_551_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_409_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_409_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
else
{
lean_dec(v_a_371_);
lean_dec(v_a_367_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
return v___x_405_;
}
v___jp_372_:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_getMVars(v_a_351_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
v___x_383_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_382_, v_mvarCounter_352_, v___y_378_);
lean_dec(v_a_382_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v___x_385_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_384_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v_a_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; 
lean_dec_ref_known(v___x_385_, 1);
v___x_386_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_347_, v___y_374_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec_ref_known(v___x_386_, 1);
v___x_387_ = l_Lean_Name_mkStr1(v___x_353_);
v___x_388_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_387_, v_a_371_, v___x_350_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v___x_388_;
}
else
{
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v_a_371_);
lean_dec_ref(v___x_353_);
return v___x_386_;
}
}
else
{
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v_a_371_);
lean_dec_ref(v___x_353_);
lean_dec(v_a_347_);
return v___x_385_;
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v_a_371_);
lean_dec_ref(v___x_353_);
lean_dec(v_a_347_);
v_a_389_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_383_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_383_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v_a_371_);
lean_dec_ref(v___x_353_);
lean_dec(v_a_347_);
v_a_397_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_381_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_381_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_a_367_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
v_a_561_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_370_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_370_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_348_);
lean_dec(v_a_347_);
v_a_569_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_366_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_366_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object** _args){
lean_object* v_a_577_ = _args[0];
lean_object* v_a_578_ = _args[1];
lean_object* v___x_579_ = _args[2];
lean_object* v___x_580_ = _args[3];
lean_object* v_a_581_ = _args[4];
lean_object* v_mvarCounter_582_ = _args[5];
lean_object* v___x_583_ = _args[6];
lean_object* v___x_584_ = _args[7];
lean_object* v_useReducible_585_ = _args[8];
lean_object* v___x_586_ = _args[9];
lean_object* v___y_587_ = _args[10];
lean_object* v___y_588_ = _args[11];
lean_object* v___y_589_ = _args[12];
lean_object* v___y_590_ = _args[13];
lean_object* v___y_591_ = _args[14];
lean_object* v___y_592_ = _args[15];
lean_object* v___y_593_ = _args[16];
lean_object* v___y_594_ = _args[17];
lean_object* v___y_595_ = _args[18];
_start:
{
uint8_t v___x_93523__boxed_596_; uint8_t v___x_93524__boxed_597_; uint8_t v_useReducible_boxed_598_; uint8_t v___x_93528__boxed_599_; lean_object* v_res_600_; 
v___x_93523__boxed_596_ = lean_unbox(v___x_579_);
v___x_93524__boxed_597_ = lean_unbox(v___x_580_);
v_useReducible_boxed_598_ = lean_unbox(v_useReducible_585_);
v___x_93528__boxed_599_ = lean_unbox(v___x_586_);
v_res_600_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_577_, v_a_578_, v___x_93523__boxed_596_, v___x_93524__boxed_597_, v_a_581_, v_mvarCounter_582_, v___x_583_, v___x_584_, v_useReducible_boxed_598_, v___x_93528__boxed_599_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v_mvarCounter_582_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; lean_object* v_infoState_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_traceState_617_; lean_object* v_cache_618_; lean_object* v_messages_619_; lean_object* v_snapshotTasks_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_641_; 
v___x_611_ = lean_st_ref_take(v___y_609_);
v_infoState_612_ = lean_ctor_get(v___x_611_, 7);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_traceState_617_ = lean_ctor_get(v___x_611_, 4);
v_cache_618_ = lean_ctor_get(v___x_611_, 5);
v_messages_619_ = lean_ctor_get(v___x_611_, 6);
v_snapshotTasks_620_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_641_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snapshotTasks_620_);
lean_inc(v_infoState_612_);
lean_inc(v_messages_619_);
lean_inc(v_cache_618_);
lean_inc(v_traceState_617_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint8_t v_enabled_624_; lean_object* v_assignment_625_; lean_object* v_lazyAssignment_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_639_; 
v_enabled_624_ = lean_ctor_get_uint8(v_infoState_612_, sizeof(void*)*3);
v_assignment_625_ = lean_ctor_get(v_infoState_612_, 0);
v_lazyAssignment_626_ = lean_ctor_get(v_infoState_612_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_infoState_612_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v_infoState_612_, 2);
lean_dec(v_unused_640_);
v___x_628_ = v_infoState_612_;
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_lazyAssignment_626_);
lean_inc(v_assignment_625_);
lean_dec(v_infoState_612_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 2, v_a_601_);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_assignment_625_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_lazyAssignment_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_a_601_);
lean_ctor_set_uint8(v_reuseFailAlloc_638_, sizeof(void*)*3, v_enabled_624_);
v___x_631_ = v_reuseFailAlloc_638_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 7, v___x_631_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_env_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_traceState_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_cache_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_messages_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_637_, 8, v_snapshotTasks_620_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_st_ref_set(v___y_609_, v___x_633_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object* v_a_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
return v_x_653_;
}
else
{
lean_object* v_key_655_; lean_object* v_value_656_; lean_object* v_tail_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_680_; 
v_key_655_ = lean_ctor_get(v_x_654_, 0);
v_value_656_ = lean_ctor_get(v_x_654_, 1);
v_tail_657_ = lean_ctor_get(v_x_654_, 2);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_680_ == 0)
{
v___x_659_ = v_x_654_;
v_isShared_660_ = v_isSharedCheck_680_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_tail_657_);
lean_inc(v_value_656_);
lean_inc(v_key_655_);
lean_dec(v_x_654_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_680_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; uint64_t v_fold_665_; uint64_t v___x_666_; uint64_t v___x_667_; uint64_t v___x_668_; size_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_661_ = lean_array_get_size(v_x_653_);
v___x_662_ = l_Lean_Expr_hash(v_key_655_);
v___x_663_ = 32ULL;
v___x_664_ = lean_uint64_shift_right(v___x_662_, v___x_663_);
v_fold_665_ = lean_uint64_xor(v___x_662_, v___x_664_);
v___x_666_ = 16ULL;
v___x_667_ = lean_uint64_shift_right(v_fold_665_, v___x_666_);
v___x_668_ = lean_uint64_xor(v_fold_665_, v___x_667_);
v___x_669_ = lean_uint64_to_usize(v___x_668_);
v___x_670_ = lean_usize_of_nat(v___x_661_);
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_sub(v___x_670_, v___x_671_);
v___x_673_ = lean_usize_land(v___x_669_, v___x_672_);
v___x_674_ = lean_array_uget_borrowed(v_x_653_, v___x_673_);
lean_inc(v___x_674_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 2, v___x_674_);
v___x_676_ = v___x_659_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_key_655_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_value_656_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v___x_674_);
v___x_676_ = v_reuseFailAlloc_679_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; 
v___x_677_ = lean_array_uset(v_x_653_, v___x_673_, v___x_676_);
v_x_653_ = v___x_677_;
v_x_654_ = v_tail_657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object* v_i_681_, lean_object* v_source_682_, lean_object* v_target_683_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_array_get_size(v_source_682_);
v___x_685_ = lean_nat_dec_lt(v_i_681_, v___x_684_);
if (v___x_685_ == 0)
{
lean_dec_ref(v_source_682_);
lean_dec(v_i_681_);
return v_target_683_;
}
else
{
lean_object* v_es_686_; lean_object* v___x_687_; lean_object* v_source_688_; lean_object* v_target_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_es_686_ = lean_array_fget(v_source_682_, v_i_681_);
v___x_687_ = lean_box(0);
v_source_688_ = lean_array_fset(v_source_682_, v_i_681_, v___x_687_);
v_target_689_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_683_, v_es_686_);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_add(v_i_681_, v___x_690_);
lean_dec(v_i_681_);
v_i_681_ = v___x_691_;
v_source_682_ = v_source_688_;
v_target_683_ = v_target_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_data_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_nbuckets_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_694_ = lean_array_get_size(v_data_693_);
v___x_695_ = lean_unsigned_to_nat(2u);
v_nbuckets_696_ = lean_nat_mul(v___x_694_, v___x_695_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_box(0);
v___x_699_ = lean_mk_array(v_nbuckets_696_, v___x_698_);
v___x_700_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_697_, v_data_693_, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_a_701_, lean_object* v_x_702_){
_start:
{
if (lean_obj_tag(v_x_702_) == 0)
{
uint8_t v___x_703_; 
v___x_703_ = 0;
return v___x_703_;
}
else
{
lean_object* v_key_704_; lean_object* v_tail_705_; uint8_t v___x_706_; 
v_key_704_ = lean_ctor_get(v_x_702_, 0);
v_tail_705_ = lean_ctor_get(v_x_702_, 2);
v___x_706_ = lean_expr_eqv(v_key_704_, v_a_701_);
if (v___x_706_ == 0)
{
v_x_702_ = v_tail_705_;
goto _start;
}
else
{
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_a_708_, lean_object* v_x_709_){
_start:
{
uint8_t v_res_710_; lean_object* v_r_711_; 
v_res_710_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_708_, v_x_709_);
lean_dec(v_x_709_);
lean_dec_ref(v_a_708_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(lean_object* v_m_712_, lean_object* v_a_713_, lean_object* v_b_714_){
_start:
{
lean_object* v_size_715_; lean_object* v_buckets_716_; lean_object* v___x_717_; uint64_t v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; uint64_t v_fold_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v___x_724_; size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; lean_object* v_bkt_730_; uint8_t v___x_731_; 
v_size_715_ = lean_ctor_get(v_m_712_, 0);
v_buckets_716_ = lean_ctor_get(v_m_712_, 1);
v___x_717_ = lean_array_get_size(v_buckets_716_);
v___x_718_ = l_Lean_Expr_hash(v_a_713_);
v___x_719_ = 32ULL;
v___x_720_ = lean_uint64_shift_right(v___x_718_, v___x_719_);
v_fold_721_ = lean_uint64_xor(v___x_718_, v___x_720_);
v___x_722_ = 16ULL;
v___x_723_ = lean_uint64_shift_right(v_fold_721_, v___x_722_);
v___x_724_ = lean_uint64_xor(v_fold_721_, v___x_723_);
v___x_725_ = lean_uint64_to_usize(v___x_724_);
v___x_726_ = lean_usize_of_nat(v___x_717_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_sub(v___x_726_, v___x_727_);
v___x_729_ = lean_usize_land(v___x_725_, v___x_728_);
v_bkt_730_ = lean_array_uget_borrowed(v_buckets_716_, v___x_729_);
v___x_731_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_713_, v_bkt_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_752_; 
lean_inc_ref(v_buckets_716_);
lean_inc(v_size_715_);
v_isSharedCheck_752_ = !lean_is_exclusive(v_m_712_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_753_ = lean_ctor_get(v_m_712_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_m_712_, 0);
lean_dec(v_unused_754_);
v___x_733_ = v_m_712_;
v_isShared_734_ = v_isSharedCheck_752_;
goto v_resetjp_732_;
}
else
{
lean_dec(v_m_712_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_752_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v_size_x27_736_; lean_object* v___x_737_; lean_object* v_buckets_x27_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v_size_x27_736_ = lean_nat_add(v_size_715_, v___x_735_);
lean_dec(v_size_715_);
lean_inc(v_bkt_730_);
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v_a_713_);
lean_ctor_set(v___x_737_, 1, v_b_714_);
lean_ctor_set(v___x_737_, 2, v_bkt_730_);
v_buckets_x27_738_ = lean_array_uset(v_buckets_716_, v___x_729_, v___x_737_);
v___x_739_ = lean_unsigned_to_nat(4u);
v___x_740_ = lean_nat_mul(v_size_x27_736_, v___x_739_);
v___x_741_ = lean_unsigned_to_nat(3u);
v___x_742_ = lean_nat_div(v___x_740_, v___x_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_array_get_size(v_buckets_x27_738_);
v___x_744_ = lean_nat_dec_le(v___x_742_, v___x_743_);
lean_dec(v___x_742_);
if (v___x_744_ == 0)
{
lean_object* v_val_745_; lean_object* v___x_747_; 
v_val_745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_738_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_val_745_);
lean_ctor_set(v___x_733_, 0, v_size_x27_736_);
v___x_747_ = v___x_733_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_size_x27_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_val_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v___x_750_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v_buckets_x27_738_);
lean_ctor_set(v___x_733_, 0, v_size_x27_736_);
v___x_750_ = v___x_733_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_size_x27_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_buckets_x27_738_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_dec(v_b_714_);
lean_dec_ref(v_a_713_);
return v_m_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(lean_object* v_mvarId_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_mctx_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_759_ = lean_st_ref_get(v___y_757_);
v_mctx_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc_ref(v_mctx_760_);
lean_dec(v___x_759_);
v___x_761_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_760_, v_mvarId_755_);
lean_dec_ref(v_mctx_760_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___y_756_);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object* v_mvarId_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec(v_mvarId_765_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_mvarId_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; lean_object* v_mctx_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_774_ = lean_st_ref_get(v___y_772_);
v_mctx_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_ref(v_mctx_775_);
lean_dec(v___x_774_);
v___x_776_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_775_, v_mvarId_770_);
lean_dec_ref(v_mctx_775_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___y_771_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_mvarId_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec(v_mvarId_780_);
return v_res_784_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_buckets_787_; lean_object* v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v_fold_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_buckets_787_ = lean_ctor_get(v_m_785_, 1);
v___x_788_ = lean_array_get_size(v_buckets_787_);
v___x_789_ = l_Lean_Expr_hash(v_a_786_);
v___x_790_ = 32ULL;
v___x_791_ = lean_uint64_shift_right(v___x_789_, v___x_790_);
v_fold_792_ = lean_uint64_xor(v___x_789_, v___x_791_);
v___x_793_ = 16ULL;
v___x_794_ = lean_uint64_shift_right(v_fold_792_, v___x_793_);
v___x_795_ = lean_uint64_xor(v_fold_792_, v___x_794_);
v___x_796_ = lean_uint64_to_usize(v___x_795_);
v___x_797_ = lean_usize_of_nat(v___x_788_);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_sub(v___x_797_, v___x_798_);
v___x_800_ = lean_usize_land(v___x_796_, v___x_799_);
v___x_801_ = lean_array_uget_borrowed(v_buckets_787_, v___x_800_);
v___x_802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_786_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_803_, v_a_804_);
lean_dec_ref(v_a_804_);
lean_dec_ref(v_m_803_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_811_, lean_object* v_e_812_, lean_object* v_a_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_d_824_; lean_object* v_b_825_; lean_object* v___y_826_; uint8_t v___x_832_; 
v___x_832_ = l_Lean_Expr_hasExprMVar(v_e_812_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_e_812_);
v___x_833_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_a_813_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
else
{
uint8_t v___x_836_; 
v___x_836_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_813_, v_e_812_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_box(0);
lean_inc_ref(v_e_812_);
v___x_838_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_a_813_, v_e_812_, v___x_837_);
switch(lean_obj_tag(v_e_812_))
{
case 11:
{
lean_object* v_struct_839_; 
v_struct_839_ = lean_ctor_get(v_e_812_, 2);
lean_inc_ref(v_struct_839_);
lean_dec_ref_known(v_e_812_, 3);
v_e_812_ = v_struct_839_;
v_a_813_ = v___x_838_;
goto _start;
}
case 7:
{
lean_object* v_binderType_841_; lean_object* v_body_842_; 
v_binderType_841_ = lean_ctor_get(v_e_812_, 1);
lean_inc_ref(v_binderType_841_);
v_body_842_ = lean_ctor_get(v_e_812_, 2);
lean_inc_ref(v_body_842_);
lean_dec_ref_known(v_e_812_, 3);
v_d_824_ = v_binderType_841_;
v_b_825_ = v_body_842_;
v___y_826_ = v___x_838_;
goto v___jp_823_;
}
case 6:
{
lean_object* v_binderType_843_; lean_object* v_body_844_; 
v_binderType_843_ = lean_ctor_get(v_e_812_, 1);
lean_inc_ref(v_binderType_843_);
v_body_844_ = lean_ctor_get(v_e_812_, 2);
lean_inc_ref(v_body_844_);
lean_dec_ref_known(v_e_812_, 3);
v_d_824_ = v_binderType_843_;
v_b_825_ = v_body_844_;
v___y_826_ = v___x_838_;
goto v___jp_823_;
}
case 8:
{
lean_object* v_type_845_; lean_object* v_value_846_; lean_object* v_body_847_; lean_object* v___x_848_; 
v_type_845_ = lean_ctor_get(v_e_812_, 1);
lean_inc_ref(v_type_845_);
v_value_846_ = lean_ctor_get(v_e_812_, 2);
lean_inc_ref(v_value_846_);
v_body_847_ = lean_ctor_get(v_e_812_, 3);
lean_inc_ref(v_body_847_);
lean_dec_ref_known(v_e_812_, 4);
v___x_848_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_811_, v_type_845_, v___x_838_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v_fst_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
v_fst_850_ = lean_ctor_get(v_a_849_, 0);
if (lean_obj_tag(v_fst_850_) == 0)
{
lean_dec(v_a_849_);
lean_dec_ref(v_body_847_);
lean_dec_ref(v_value_846_);
return v___x_848_;
}
else
{
lean_object* v_snd_851_; lean_object* v___x_852_; 
lean_dec_ref_known(v___x_848_, 1);
v_snd_851_ = lean_ctor_get(v_a_849_, 1);
lean_inc(v_snd_851_);
lean_dec(v_a_849_);
v___x_852_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_811_, v_value_846_, v_snd_851_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v_fst_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
v_fst_854_ = lean_ctor_get(v_a_853_, 0);
if (lean_obj_tag(v_fst_854_) == 0)
{
lean_dec(v_a_853_);
lean_dec_ref(v_body_847_);
return v___x_852_;
}
else
{
lean_object* v_snd_855_; 
lean_dec_ref_known(v___x_852_, 1);
v_snd_855_ = lean_ctor_get(v_a_853_, 1);
lean_inc(v_snd_855_);
lean_dec(v_a_853_);
v_e_812_ = v_body_847_;
v_a_813_ = v_snd_855_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_847_);
return v___x_852_;
}
}
}
else
{
lean_dec_ref(v_body_847_);
lean_dec_ref(v_value_846_);
return v___x_848_;
}
}
case 10:
{
lean_object* v_expr_857_; 
v_expr_857_ = lean_ctor_get(v_e_812_, 1);
lean_inc_ref(v_expr_857_);
lean_dec_ref_known(v_e_812_, 2);
v_e_812_ = v_expr_857_;
v_a_813_ = v___x_838_;
goto _start;
}
case 5:
{
lean_object* v_fn_859_; lean_object* v_arg_860_; lean_object* v___x_861_; 
v_fn_859_ = lean_ctor_get(v_e_812_, 0);
lean_inc_ref(v_fn_859_);
v_arg_860_ = lean_ctor_get(v_e_812_, 1);
lean_inc_ref(v_arg_860_);
lean_dec_ref_known(v_e_812_, 2);
v___x_861_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_811_, v_fn_859_, v___x_838_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v_fst_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
v_fst_863_ = lean_ctor_get(v_a_862_, 0);
if (lean_obj_tag(v_fst_863_) == 0)
{
lean_dec(v_a_862_);
lean_dec_ref(v_arg_860_);
return v___x_861_;
}
else
{
lean_object* v_snd_864_; 
lean_dec_ref_known(v___x_861_, 1);
v_snd_864_ = lean_ctor_get(v_a_862_, 1);
lean_inc(v_snd_864_);
lean_dec(v_a_862_);
v_e_812_ = v_arg_860_;
v_a_813_ = v_snd_864_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_860_);
return v___x_861_;
}
}
case 2:
{
lean_object* v_mvarId_866_; lean_object* v___x_867_; 
v_mvarId_866_ = lean_ctor_get(v_e_812_, 0);
lean_inc(v_mvarId_866_);
lean_dec_ref_known(v_e_812_, 1);
v___x_867_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_811_, v_mvarId_866_, v___x_838_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_867_;
}
default: 
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec_ref(v_e_812_);
v___x_868_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_838_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v_e_812_);
v___x_871_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v_a_813_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
v___jp_823_:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_811_, v_d_824_, v___y_826_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v_fst_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
v_fst_829_ = lean_ctor_get(v_a_828_, 0);
if (lean_obj_tag(v_fst_829_) == 0)
{
lean_dec(v_a_828_);
lean_dec_ref(v_b_825_);
return v___x_827_;
}
else
{
lean_object* v_snd_830_; 
lean_dec_ref_known(v___x_827_, 1);
v_snd_830_ = lean_ctor_get(v_a_828_, 1);
lean_inc(v_snd_830_);
lean_dec(v_a_828_);
v_e_812_ = v_b_825_;
v_a_813_ = v_snd_830_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_825_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object* v_mvarId_874_, lean_object* v_mvarId_x27_875_, lean_object* v_a_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = l_Lean_instBEqMVarId_beq(v_mvarId_874_, v_mvarId_x27_875_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_875_, v_a_876_, v___y_882_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_971_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_971_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_971_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_971_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_fst_892_; 
v_fst_892_ = lean_ctor_get(v_a_888_, 0);
lean_inc(v_fst_892_);
if (lean_obj_tag(v_fst_892_) == 0)
{
lean_object* v_snd_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_mvarId_x27_875_);
v_snd_893_ = lean_ctor_get(v_a_888_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v_a_888_, 0);
lean_dec(v_unused_912_);
v___x_895_ = v_a_888_;
v_isShared_896_ = v_isSharedCheck_911_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_snd_893_);
lean_dec(v_a_888_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_911_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_910_; 
v_a_897_ = lean_ctor_get(v_fst_892_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_fst_892_);
if (v_isSharedCheck_910_ == 0)
{
v___x_899_ = v_fst_892_;
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v_fst_892_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_910_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_909_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_902_);
v___x_904_ = v___x_895_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_snd_893_);
v___x_904_ = v_reuseFailAlloc_908_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_904_);
v___x_906_ = v___x_890_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
else
{
lean_object* v_a_913_; 
lean_del_object(v___x_890_);
v_a_913_ = lean_ctor_get(v_fst_892_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v_fst_892_, 1);
if (lean_obj_tag(v_a_913_) == 0)
{
lean_object* v_snd_914_; lean_object* v___x_915_; 
v_snd_914_ = lean_ctor_get(v_a_888_, 1);
lean_inc(v_snd_914_);
lean_dec(v_a_888_);
v___x_915_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_875_, v_snd_914_, v___y_882_);
lean_dec(v_mvarId_x27_875_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_959_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_959_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_959_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_959_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_fst_920_; 
v_fst_920_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_fst_920_);
if (lean_obj_tag(v_fst_920_) == 0)
{
lean_object* v_snd_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_939_; 
v_snd_921_ = lean_ctor_get(v_a_916_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v_a_916_, 0);
lean_dec(v_unused_940_);
v___x_923_ = v_a_916_;
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snd_921_);
lean_dec(v_a_916_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_939_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_938_; 
v_a_925_ = lean_ctor_get(v_fst_920_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_fst_920_);
if (v_isSharedCheck_938_ == 0)
{
v___x_927_ = v_fst_920_;
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v_fst_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_938_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_937_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_930_);
v___x_932_ = v___x_923_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_snd_921_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_932_);
v___x_934_ = v___x_918_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
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
else
{
lean_object* v_a_941_; 
v_a_941_ = lean_ctor_get(v_fst_920_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v_fst_920_, 1);
if (lean_obj_tag(v_a_941_) == 0)
{
lean_object* v_snd_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_953_; 
v_snd_942_ = lean_ctor_get(v_a_916_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_a_916_, 0);
lean_dec(v_unused_954_);
v___x_944_ = v_a_916_;
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_942_);
lean_dec(v_a_916_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_snd_942_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_948_);
v___x_950_ = v___x_918_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_val_955_; lean_object* v_snd_956_; lean_object* v_mvarIdPending_957_; 
lean_del_object(v___x_918_);
v_val_955_ = lean_ctor_get(v_a_941_, 0);
lean_inc(v_val_955_);
lean_dec_ref_known(v_a_941_, 1);
v_snd_956_ = lean_ctor_get(v_a_916_, 1);
lean_inc(v_snd_956_);
lean_dec(v_a_916_);
v_mvarIdPending_957_ = lean_ctor_get(v_val_955_, 1);
lean_inc(v_mvarIdPending_957_);
lean_dec(v_val_955_);
v_mvarId_x27_875_ = v_mvarIdPending_957_;
v_a_876_ = v_snd_956_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_a_960_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_915_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_915_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_snd_968_; lean_object* v_val_969_; lean_object* v___x_970_; 
lean_dec(v_mvarId_x27_875_);
v_snd_968_ = lean_ctor_get(v_a_888_, 1);
lean_inc(v_snd_968_);
lean_dec(v_a_888_);
v_val_969_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v_val_969_);
lean_dec_ref_known(v_a_913_, 1);
v___x_970_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_874_, v_val_969_, v_snd_968_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_970_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_mvarId_x27_875_);
v_a_972_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_887_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_887_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec(v_mvarId_x27_875_);
v___x_980_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1));
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v_a_876_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_983_, lean_object* v_mvarId_x27_984_, lean_object* v_a_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_983_, v_mvarId_x27_984_, v_a_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_mvarId_983_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_996_, lean_object* v_e_997_, lean_object* v_a_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_996_, v_e_997_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v_mvarId_996_);
return v_res_1008_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_unsigned_to_nat(16u);
v___x_1011_ = lean_mk_array(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1015_, lean_object* v_e_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v___x_1026_; 
v___x_1026_ = l_Lean_Expr_hasExprMVar(v_e_1016_);
if (v___x_1026_ == 0)
{
uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v_e_1016_);
v___x_1027_ = 1;
v___x_1028_ = lean_box(v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1031_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1015_, v_e_1016_, v___x_1030_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1046_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1046_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1046_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_fst_1036_; 
v_fst_1036_ = lean_ctor_get(v_a_1032_, 0);
lean_inc(v_fst_1036_);
lean_dec(v_a_1032_);
if (lean_obj_tag(v_fst_1036_) == 0)
{
uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_dec_ref_known(v_fst_1036_, 1);
v___x_1037_ = 0;
v___x_1038_ = lean_box(v___x_1037_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1038_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec_ref_known(v_fst_1036_, 1);
v___x_1042_ = lean_box(v___x_1026_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1042_);
v___x_1044_ = v___x_1034_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1047_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1031_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1031_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1055_, lean_object* v_e_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1055_, v_e_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v_mvarId_1055_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object* v_msgData_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_env_1074_; lean_object* v___x_1075_; lean_object* v_mctx_1076_; lean_object* v_lctx_1077_; lean_object* v_options_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1073_ = lean_st_ref_get(v___y_1071_);
v_env_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_env_1074_);
lean_dec(v___x_1073_);
v___x_1075_ = lean_st_ref_get(v___y_1069_);
v_mctx_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_mctx_1076_);
lean_dec(v___x_1075_);
v_lctx_1077_ = lean_ctor_get(v___y_1068_, 2);
v_options_1078_ = lean_ctor_get(v___y_1070_, 2);
lean_inc_ref(v_options_1078_);
lean_inc_ref(v_lctx_1077_);
v___x_1079_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1079_, 0, v_env_1074_);
lean_ctor_set(v___x_1079_, 1, v_mctx_1076_);
lean_ctor_set(v___x_1079_, 2, v_lctx_1077_);
lean_ctor_set(v___x_1079_, 3, v_options_1078_);
v___x_1080_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v_msgData_1067_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object* v_msgData_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msgData_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_ref_1095_; lean_object* v___x_1096_; lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1105_; 
v_ref_1095_ = lean_ctor_get(v___y_1092_, 5);
v___x_1096_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msg_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
lean_inc(v_ref_1095_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v_ref_1095_);
lean_ctor_set(v___x_1101_, 1, v_a_1097_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 1);
lean_ctor_set(v___x_1099_, 0, v___x_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v_msg_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_ks_1117_; lean_object* v_vs_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1142_; 
v_ks_1117_ = lean_ctor_get(v_x_1113_, 0);
v_vs_1118_ = lean_ctor_get(v_x_1113_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1113_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1120_ = v_x_1113_;
v_isShared_1121_ = v_isSharedCheck_1142_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_vs_1118_);
lean_inc(v_ks_1117_);
lean_dec(v_x_1113_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1142_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = lean_array_get_size(v_ks_1117_);
v___x_1123_ = lean_nat_dec_lt(v_x_1114_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_dec(v_x_1114_);
v___x_1124_ = lean_array_push(v_ks_1117_, v_x_1115_);
v___x_1125_ = lean_array_push(v_vs_1118_, v_x_1116_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1125_);
lean_ctor_set(v___x_1120_, 0, v___x_1124_);
v___x_1127_ = v___x_1120_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_object* v_k_x27_1129_; uint8_t v___x_1130_; 
v_k_x27_1129_ = lean_array_fget_borrowed(v_ks_1117_, v_x_1114_);
v___x_1130_ = l_Lean_instBEqMVarId_beq(v_x_1115_, v_k_x27_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1132_; 
if (v_isShared_1121_ == 0)
{
v___x_1132_ = v___x_1120_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_ks_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_vs_1118_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(1u);
v___x_1134_ = lean_nat_add(v_x_1114_, v___x_1133_);
lean_dec(v_x_1114_);
v_x_1113_ = v___x_1132_;
v_x_1114_ = v___x_1134_;
goto _start;
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1137_ = lean_array_fset(v_ks_1117_, v_x_1114_, v_x_1115_);
v___x_1138_ = lean_array_fset(v_vs_1118_, v_x_1114_, v_x_1116_);
lean_dec(v_x_1114_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1138_);
lean_ctor_set(v___x_1120_, 0, v___x_1137_);
v___x_1140_ = v___x_1120_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1143_, lean_object* v_k_1144_, lean_object* v_v_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1143_, v___x_1146_, v_k_1144_, v_v_1145_);
return v___x_1147_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; 
v___x_1148_ = ((size_t)5ULL);
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_shift_left(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; 
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1153_ = lean_usize_sub(v___x_1152_, v___x_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(lean_object* v_x_1155_, size_t v_x_1156_, size_t v_x_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_){
_start:
{
if (lean_obj_tag(v_x_1155_) == 0)
{
lean_object* v_es_1160_; size_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; lean_object* v_j_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_es_1160_ = lean_ctor_get(v_x_1155_, 0);
v___x_1161_ = ((size_t)5ULL);
v___x_1162_ = ((size_t)1ULL);
v___x_1163_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1);
v___x_1164_ = lean_usize_land(v_x_1156_, v___x_1163_);
v_j_1165_ = lean_usize_to_nat(v___x_1164_);
v___x_1166_ = lean_array_get_size(v_es_1160_);
v___x_1167_ = lean_nat_dec_lt(v_j_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec(v_j_1165_);
lean_dec(v_x_1159_);
lean_dec(v_x_1158_);
return v_x_1155_;
}
else
{
lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1204_; 
lean_inc_ref(v_es_1160_);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v_x_1155_, 0);
lean_dec(v_unused_1205_);
v___x_1169_ = v_x_1155_;
v_isShared_1170_ = v_isSharedCheck_1204_;
goto v_resetjp_1168_;
}
else
{
lean_dec(v_x_1155_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1204_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_v_1171_; lean_object* v___x_1172_; lean_object* v_xs_x27_1173_; lean_object* v___y_1175_; 
v_v_1171_ = lean_array_fget(v_es_1160_, v_j_1165_);
v___x_1172_ = lean_box(0);
v_xs_x27_1173_ = lean_array_fset(v_es_1160_, v_j_1165_, v___x_1172_);
switch(lean_obj_tag(v_v_1171_))
{
case 0:
{
lean_object* v_key_1180_; lean_object* v_val_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v_key_1180_ = lean_ctor_get(v_v_1171_, 0);
v_val_1181_ = lean_ctor_get(v_v_1171_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_v_1171_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1183_ = v_v_1171_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_val_1181_);
lean_inc(v_key_1180_);
lean_dec(v_v_1171_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Lean_instBEqMVarId_beq(v_x_1158_, v_key_1180_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_del_object(v___x_1183_);
v___x_1186_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1180_, v_val_1181_, v_x_1158_, v_x_1159_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
v___y_1175_ = v___x_1187_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1189_; 
lean_dec(v_val_1181_);
lean_dec(v_key_1180_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_x_1159_);
lean_ctor_set(v___x_1183_, 0, v_x_1158_);
v___x_1189_ = v___x_1183_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_x_1158_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_x_1159_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v___y_1175_ = v___x_1189_;
goto v___jp_1174_;
}
}
}
}
case 1:
{
lean_object* v_node_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1202_; 
v_node_1192_ = lean_ctor_get(v_v_1171_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_v_1171_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1194_ = v_v_1171_;
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_node_1192_);
lean_dec(v_v_1171_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1196_ = lean_usize_shift_right(v_x_1156_, v___x_1161_);
v___x_1197_ = lean_usize_add(v_x_1157_, v___x_1162_);
v___x_1198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_node_1192_, v___x_1196_, v___x_1197_, v_x_1158_, v_x_1159_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1198_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v___y_1175_ = v___x_1200_;
goto v___jp_1174_;
}
}
}
default: 
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_x_1158_);
lean_ctor_set(v___x_1203_, 1, v_x_1159_);
v___y_1175_ = v___x_1203_;
goto v___jp_1174_;
}
}
v___jp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_array_fset(v_xs_x27_1173_, v_j_1165_, v___y_1175_);
lean_dec(v_j_1165_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1176_);
v___x_1178_ = v___x_1169_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
else
{
lean_object* v_ks_1206_; lean_object* v_vs_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1227_; 
v_ks_1206_ = lean_ctor_get(v_x_1155_, 0);
v_vs_1207_ = lean_ctor_get(v_x_1155_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1209_ = v_x_1155_;
v_isShared_1210_ = v_isSharedCheck_1227_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_vs_1207_);
lean_inc(v_ks_1206_);
lean_dec(v_x_1155_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1227_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_ks_1206_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_vs_1207_);
v___x_1212_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v_newNode_1213_; uint8_t v___y_1215_; size_t v___x_1221_; uint8_t v___x_1222_; 
v_newNode_1213_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1212_, v_x_1158_, v_x_1159_);
v___x_1221_ = ((size_t)7ULL);
v___x_1222_ = lean_usize_dec_le(v___x_1221_, v_x_1157_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1223_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1213_);
v___x_1224_ = lean_unsigned_to_nat(4u);
v___x_1225_ = lean_nat_dec_lt(v___x_1223_, v___x_1224_);
lean_dec(v___x_1223_);
v___y_1215_ = v___x_1225_;
goto v___jp_1214_;
}
else
{
v___y_1215_ = v___x_1222_;
goto v___jp_1214_;
}
v___jp_1214_:
{
if (v___y_1215_ == 0)
{
lean_object* v_ks_1216_; lean_object* v_vs_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_ks_1216_ = lean_ctor_get(v_newNode_1213_, 0);
lean_inc_ref(v_ks_1216_);
v_vs_1217_ = lean_ctor_get(v_newNode_1213_, 1);
lean_inc_ref(v_vs_1217_);
lean_dec_ref(v_newNode_1213_);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2);
v___x_1220_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1157_, v_ks_1216_, v_vs_1217_, v___x_1218_, v___x_1219_);
lean_dec_ref(v_vs_1217_);
lean_dec_ref(v_ks_1216_);
return v___x_1220_;
}
else
{
return v_newNode_1213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1228_, lean_object* v_keys_1229_, lean_object* v_vals_1230_, lean_object* v_i_1231_, lean_object* v_entries_1232_){
_start:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v_keys_1229_);
v___x_1234_ = lean_nat_dec_lt(v_i_1231_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec(v_i_1231_);
return v_entries_1232_;
}
else
{
lean_object* v_k_1235_; lean_object* v_v_1236_; uint64_t v___x_1237_; size_t v_h_1238_; size_t v___x_1239_; lean_object* v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v_h_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_k_1235_ = lean_array_fget_borrowed(v_keys_1229_, v_i_1231_);
v_v_1236_ = lean_array_fget_borrowed(v_vals_1230_, v_i_1231_);
v___x_1237_ = l_Lean_instHashableMVarId_hash(v_k_1235_);
v_h_1238_ = lean_uint64_to_usize(v___x_1237_);
v___x_1239_ = ((size_t)5ULL);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_sub(v_depth_1228_, v___x_1241_);
v___x_1243_ = lean_usize_mul(v___x_1239_, v___x_1242_);
v_h_1244_ = lean_usize_shift_right(v_h_1238_, v___x_1243_);
v___x_1245_ = lean_nat_add(v_i_1231_, v___x_1240_);
lean_dec(v_i_1231_);
lean_inc(v_v_1236_);
lean_inc(v_k_1235_);
v___x_1246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_entries_1232_, v_h_1244_, v_depth_1228_, v_k_1235_, v_v_1236_);
v_i_1231_ = v___x_1245_;
v_entries_1232_ = v___x_1246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1248_, lean_object* v_keys_1249_, lean_object* v_vals_1250_, lean_object* v_i_1251_, lean_object* v_entries_1252_){
_start:
{
size_t v_depth_boxed_1253_; lean_object* v_res_1254_; 
v_depth_boxed_1253_ = lean_unbox_usize(v_depth_1248_);
lean_dec(v_depth_1248_);
v_res_1254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1253_, v_keys_1249_, v_vals_1250_, v_i_1251_, v_entries_1252_);
lean_dec_ref(v_vals_1250_);
lean_dec_ref(v_keys_1249_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
size_t v_x_94806__boxed_1260_; size_t v_x_94807__boxed_1261_; lean_object* v_res_1262_; 
v_x_94806__boxed_1260_ = lean_unbox_usize(v_x_1256_);
lean_dec(v_x_1256_);
v_x_94807__boxed_1261_ = lean_unbox_usize(v_x_1257_);
lean_dec(v_x_1257_);
v_res_1262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1255_, v_x_94806__boxed_1260_, v_x_94807__boxed_1261_, v_x_1258_, v_x_1259_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
uint64_t v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = l_Lean_instHashableMVarId_hash(v_x_1264_);
v___x_1267_ = lean_uint64_to_usize(v___x_1266_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1263_, v___x_1267_, v___x_1268_, v_x_1264_, v_x_1265_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_1270_, lean_object* v_val_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; lean_object* v_mctx_1275_; lean_object* v_cache_1276_; lean_object* v_zetaDeltaFVarIds_1277_; lean_object* v_postponed_1278_; lean_object* v_diag_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1307_; 
v___x_1274_ = lean_st_ref_take(v___y_1272_);
v_mctx_1275_ = lean_ctor_get(v___x_1274_, 0);
v_cache_1276_ = lean_ctor_get(v___x_1274_, 1);
v_zetaDeltaFVarIds_1277_ = lean_ctor_get(v___x_1274_, 2);
v_postponed_1278_ = lean_ctor_get(v___x_1274_, 3);
v_diag_1279_ = lean_ctor_get(v___x_1274_, 4);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1281_ = v___x_1274_;
v_isShared_1282_ = v_isSharedCheck_1307_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_diag_1279_);
lean_inc(v_postponed_1278_);
lean_inc(v_zetaDeltaFVarIds_1277_);
lean_inc(v_cache_1276_);
lean_inc(v_mctx_1275_);
lean_dec(v___x_1274_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1307_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_depth_1283_; lean_object* v_levelAssignDepth_1284_; lean_object* v_lmvarCounter_1285_; lean_object* v_mvarCounter_1286_; lean_object* v_lDecls_1287_; lean_object* v_decls_1288_; lean_object* v_userNames_1289_; lean_object* v_lAssignment_1290_; lean_object* v_eAssignment_1291_; lean_object* v_dAssignment_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1306_; 
v_depth_1283_ = lean_ctor_get(v_mctx_1275_, 0);
v_levelAssignDepth_1284_ = lean_ctor_get(v_mctx_1275_, 1);
v_lmvarCounter_1285_ = lean_ctor_get(v_mctx_1275_, 2);
v_mvarCounter_1286_ = lean_ctor_get(v_mctx_1275_, 3);
v_lDecls_1287_ = lean_ctor_get(v_mctx_1275_, 4);
v_decls_1288_ = lean_ctor_get(v_mctx_1275_, 5);
v_userNames_1289_ = lean_ctor_get(v_mctx_1275_, 6);
v_lAssignment_1290_ = lean_ctor_get(v_mctx_1275_, 7);
v_eAssignment_1291_ = lean_ctor_get(v_mctx_1275_, 8);
v_dAssignment_1292_ = lean_ctor_get(v_mctx_1275_, 9);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_mctx_1275_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1294_ = v_mctx_1275_;
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_dAssignment_1292_);
lean_inc(v_eAssignment_1291_);
lean_inc(v_lAssignment_1290_);
lean_inc(v_userNames_1289_);
lean_inc(v_decls_1288_);
lean_inc(v_lDecls_1287_);
lean_inc(v_mvarCounter_1286_);
lean_inc(v_lmvarCounter_1285_);
lean_inc(v_levelAssignDepth_1284_);
lean_inc(v_depth_1283_);
lean_dec(v_mctx_1275_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1306_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_1291_, v_mvarId_1270_, v_val_1271_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 8, v___x_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_depth_1283_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_levelAssignDepth_1284_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_lmvarCounter_1285_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_mvarCounter_1286_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_lDecls_1287_);
lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_decls_1288_);
lean_ctor_set(v_reuseFailAlloc_1305_, 6, v_userNames_1289_);
lean_ctor_set(v_reuseFailAlloc_1305_, 7, v_lAssignment_1290_);
lean_ctor_set(v_reuseFailAlloc_1305_, 8, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1305_, 9, v_dAssignment_1292_);
v___x_1298_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1298_);
v___x_1300_ = v___x_1281_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_cache_1276_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_zetaDeltaFVarIds_1277_);
lean_ctor_set(v_reuseFailAlloc_1304_, 3, v_postponed_1278_);
lean_ctor_set(v_reuseFailAlloc_1304_, 4, v_diag_1279_);
v___x_1300_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_st_ref_set(v___y_1272_, v___x_1300_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
return v___x_1303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_1308_, lean_object* v_val_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_1308_, v_val_1309_, v___y_1310_);
lean_dec(v___y_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1321_, uint8_t v_suppressElabErrors_1322_, lean_object* v_x_1323_){
_start:
{
if (lean_obj_tag(v_x_1323_) == 1)
{
lean_object* v_pre_1324_; 
v_pre_1324_ = lean_ctor_get(v_x_1323_, 0);
switch(lean_obj_tag(v_pre_1324_))
{
case 1:
{
lean_object* v_pre_1325_; 
v_pre_1325_ = lean_ctor_get(v_pre_1324_, 0);
switch(lean_obj_tag(v_pre_1325_))
{
case 0:
{
lean_object* v_str_1326_; lean_object* v_str_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_str_1326_ = lean_ctor_get(v_x_1323_, 1);
v_str_1327_ = lean_ctor_get(v_pre_1324_, 1);
v___x_1328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1329_ = lean_string_dec_eq(v_str_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1331_ = lean_string_dec_eq(v_str_1327_, v___x_1330_);
if (v___x_1331_ == 0)
{
return v___y_1321_;
}
else
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1333_ = lean_string_dec_eq(v_str_1326_, v___x_1332_);
if (v___x_1333_ == 0)
{
return v___y_1321_;
}
else
{
return v_suppressElabErrors_1322_;
}
}
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1335_ = lean_string_dec_eq(v_str_1326_, v___x_1334_);
if (v___x_1335_ == 0)
{
return v___y_1321_;
}
else
{
return v_suppressElabErrors_1322_;
}
}
}
case 1:
{
lean_object* v_pre_1336_; 
v_pre_1336_ = lean_ctor_get(v_pre_1325_, 0);
if (lean_obj_tag(v_pre_1336_) == 0)
{
lean_object* v_str_1337_; lean_object* v_str_1338_; lean_object* v_str_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v_str_1337_ = lean_ctor_get(v_x_1323_, 1);
v_str_1338_ = lean_ctor_get(v_pre_1324_, 1);
v_str_1339_ = lean_ctor_get(v_pre_1325_, 1);
v___x_1340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1341_ = lean_string_dec_eq(v_str_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
return v___y_1321_;
}
else
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1343_ = lean_string_dec_eq(v_str_1338_, v___x_1342_);
if (v___x_1343_ == 0)
{
return v___y_1321_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1345_ = lean_string_dec_eq(v_str_1337_, v___x_1344_);
if (v___x_1345_ == 0)
{
return v___y_1321_;
}
else
{
return v_suppressElabErrors_1322_;
}
}
}
}
else
{
return v___y_1321_;
}
}
default: 
{
return v___y_1321_;
}
}
}
case 0:
{
lean_object* v_str_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_str_1346_ = lean_ctor_get(v_x_1323_, 1);
v___x_1347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1348_ = lean_string_dec_eq(v_str_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
return v___y_1321_;
}
else
{
return v_suppressElabErrors_1322_;
}
}
default: 
{
return v___y_1321_;
}
}
}
else
{
return v___y_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1349_, lean_object* v_suppressElabErrors_1350_, lean_object* v_x_1351_){
_start:
{
uint8_t v___y_95041__boxed_1352_; uint8_t v_suppressElabErrors_boxed_1353_; uint8_t v_res_1354_; lean_object* v_r_1355_; 
v___y_95041__boxed_1352_ = lean_unbox(v___y_1349_);
v_suppressElabErrors_boxed_1353_ = lean_unbox(v_suppressElabErrors_1350_);
v_res_1354_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v___y_95041__boxed_1352_, v_suppressElabErrors_boxed_1353_, v_x_1351_);
lean_dec(v_x_1351_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1357_, lean_object* v_msgData_1358_, uint8_t v_severity_1359_, uint8_t v_isSilent_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; uint8_t v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; uint8_t v___y_1433_; uint8_t v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1439_; lean_object* v___y_1440_; uint8_t v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; uint8_t v___y_1444_; uint8_t v___y_1445_; uint8_t v___x_1450_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; uint8_t v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1458_; uint8_t v___y_1460_; uint8_t v___x_1475_; 
v___x_1450_ = 2;
v___x_1475_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1359_, v___x_1450_);
if (v___x_1475_ == 0)
{
v___y_1460_ = v___x_1475_;
goto v___jp_1459_;
}
else
{
uint8_t v___x_1476_; 
lean_inc_ref(v_msgData_1358_);
v___x_1476_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1358_);
v___y_1460_ = v___x_1476_;
goto v___jp_1459_;
}
v___jp_1366_:
{
lean_object* v___x_1376_; lean_object* v_currNamespace_1377_; lean_object* v_openDecls_1378_; lean_object* v_env_1379_; lean_object* v_nextMacroScope_1380_; lean_object* v_ngen_1381_; lean_object* v_auxDeclNGen_1382_; lean_object* v_traceState_1383_; lean_object* v_cache_1384_; lean_object* v_messages_1385_; lean_object* v_infoState_1386_; lean_object* v_snapshotTasks_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1401_; 
v___x_1376_ = lean_st_ref_take(v___y_1375_);
v_currNamespace_1377_ = lean_ctor_get(v___y_1374_, 6);
v_openDecls_1378_ = lean_ctor_get(v___y_1374_, 7);
v_env_1379_ = lean_ctor_get(v___x_1376_, 0);
v_nextMacroScope_1380_ = lean_ctor_get(v___x_1376_, 1);
v_ngen_1381_ = lean_ctor_get(v___x_1376_, 2);
v_auxDeclNGen_1382_ = lean_ctor_get(v___x_1376_, 3);
v_traceState_1383_ = lean_ctor_get(v___x_1376_, 4);
v_cache_1384_ = lean_ctor_get(v___x_1376_, 5);
v_messages_1385_ = lean_ctor_get(v___x_1376_, 6);
v_infoState_1386_ = lean_ctor_get(v___x_1376_, 7);
v_snapshotTasks_1387_ = lean_ctor_get(v___x_1376_, 8);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1389_ = v___x_1376_;
v_isShared_1390_ = v_isSharedCheck_1401_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_snapshotTasks_1387_);
lean_inc(v_infoState_1386_);
lean_inc(v_messages_1385_);
lean_inc(v_cache_1384_);
lean_inc(v_traceState_1383_);
lean_inc(v_auxDeclNGen_1382_);
lean_inc(v_ngen_1381_);
lean_inc(v_nextMacroScope_1380_);
lean_inc(v_env_1379_);
lean_dec(v___x_1376_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1401_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_inc(v_openDecls_1378_);
lean_inc(v_currNamespace_1377_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_currNamespace_1377_);
lean_ctor_set(v___x_1391_, 1, v_openDecls_1378_);
v___x_1392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v___y_1368_);
lean_inc_ref(v___y_1373_);
lean_inc_ref(v___y_1370_);
v___x_1393_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1393_, 0, v___y_1370_);
lean_ctor_set(v___x_1393_, 1, v___y_1367_);
lean_ctor_set(v___x_1393_, 2, v___y_1371_);
lean_ctor_set(v___x_1393_, 3, v___y_1373_);
lean_ctor_set(v___x_1393_, 4, v___x_1392_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*5, v___y_1369_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*5 + 1, v___y_1372_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*5 + 2, v_isSilent_1360_);
v___x_1394_ = l_Lean_MessageLog_add(v___x_1393_, v_messages_1385_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 6, v___x_1394_);
v___x_1396_ = v___x_1389_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_env_1379_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_nextMacroScope_1380_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_ngen_1381_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_auxDeclNGen_1382_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_traceState_1383_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_cache_1384_);
lean_ctor_set(v_reuseFailAlloc_1400_, 6, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1400_, 7, v_infoState_1386_);
lean_ctor_set(v_reuseFailAlloc_1400_, 8, v_snapshotTasks_1387_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_st_ref_set(v___y_1375_, v___x_1396_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
}
v___jp_1402_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1426_; 
v___x_1411_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1358_);
v___x_1412_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v___x_1411_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1426_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1426_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_inc_ref_n(v___y_1406_, 2);
v___x_1417_ = l_Lean_FileMap_toPosition(v___y_1406_, v___y_1408_);
lean_dec(v___y_1408_);
v___x_1418_ = l_Lean_FileMap_toPosition(v___y_1406_, v___y_1410_);
lean_dec(v___y_1410_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1409_ == 0)
{
lean_del_object(v___x_1415_);
lean_dec_ref(v___y_1403_);
v___y_1367_ = v___x_1417_;
v___y_1368_ = v_a_1413_;
v___y_1369_ = v___y_1405_;
v___y_1370_ = v___y_1404_;
v___y_1371_ = v___x_1419_;
v___y_1372_ = v___y_1407_;
v___y_1373_ = v___x_1420_;
v___y_1374_ = v___y_1363_;
v___y_1375_ = v___y_1364_;
goto v___jp_1366_;
}
else
{
uint8_t v___x_1421_; 
lean_inc(v_a_1413_);
v___x_1421_ = l_Lean_MessageData_hasTag(v___y_1403_, v_a_1413_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec_ref_known(v___x_1419_, 1);
lean_dec_ref(v___x_1417_);
lean_dec(v_a_1413_);
v___x_1422_ = lean_box(0);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1422_);
v___x_1424_ = v___x_1415_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
lean_del_object(v___x_1415_);
v___y_1367_ = v___x_1417_;
v___y_1368_ = v_a_1413_;
v___y_1369_ = v___y_1405_;
v___y_1370_ = v___y_1404_;
v___y_1371_ = v___x_1419_;
v___y_1372_ = v___y_1407_;
v___y_1373_ = v___x_1420_;
v___y_1374_ = v___y_1363_;
v___y_1375_ = v___y_1364_;
goto v___jp_1366_;
}
}
}
}
v___jp_1427_:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Syntax_getTailPos_x3f(v___y_1429_, v___y_1430_);
lean_dec(v___y_1429_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_inc(v___y_1435_);
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1431_;
v___y_1405_ = v___y_1430_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1435_;
v___y_1409_ = v___y_1434_;
v___y_1410_ = v___y_1435_;
goto v___jp_1402_;
}
else
{
lean_object* v_val_1437_; 
v_val_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_val_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1431_;
v___y_1405_ = v___y_1430_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1435_;
v___y_1409_ = v___y_1434_;
v___y_1410_ = v_val_1437_;
goto v___jp_1402_;
}
}
v___jp_1438_:
{
lean_object* v_ref_1446_; lean_object* v___x_1447_; 
v_ref_1446_ = l_Lean_replaceRef(v_ref_1357_, v___y_1442_);
v___x_1447_ = l_Lean_Syntax_getPos_x3f(v_ref_1446_, v___y_1441_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___y_1428_ = v___y_1439_;
v___y_1429_ = v_ref_1446_;
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___y_1440_;
v___y_1432_ = v___y_1443_;
v___y_1433_ = v___y_1445_;
v___y_1434_ = v___y_1444_;
v___y_1435_ = v___x_1448_;
goto v___jp_1427_;
}
else
{
lean_object* v_val_1449_; 
v_val_1449_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_val_1449_);
lean_dec_ref_known(v___x_1447_, 1);
v___y_1428_ = v___y_1439_;
v___y_1429_ = v_ref_1446_;
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___y_1440_;
v___y_1432_ = v___y_1443_;
v___y_1433_ = v___y_1445_;
v___y_1434_ = v___y_1444_;
v___y_1435_ = v_val_1449_;
goto v___jp_1427_;
}
}
v___jp_1451_:
{
if (v___y_1458_ == 0)
{
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1452_;
v___y_1441_ = v___y_1457_;
v___y_1442_ = v___y_1454_;
v___y_1443_ = v___y_1455_;
v___y_1444_ = v___y_1456_;
v___y_1445_ = v_severity_1359_;
goto v___jp_1438_;
}
else
{
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1452_;
v___y_1441_ = v___y_1457_;
v___y_1442_ = v___y_1454_;
v___y_1443_ = v___y_1455_;
v___y_1444_ = v___y_1456_;
v___y_1445_ = v___x_1450_;
goto v___jp_1438_;
}
}
v___jp_1459_:
{
if (v___y_1460_ == 0)
{
lean_object* v_fileName_1461_; lean_object* v_fileMap_1462_; lean_object* v_options_1463_; lean_object* v_ref_1464_; uint8_t v_suppressElabErrors_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___f_1468_; uint8_t v___x_1469_; uint8_t v___x_1470_; 
v_fileName_1461_ = lean_ctor_get(v___y_1363_, 0);
v_fileMap_1462_ = lean_ctor_get(v___y_1363_, 1);
v_options_1463_ = lean_ctor_get(v___y_1363_, 2);
v_ref_1464_ = lean_ctor_get(v___y_1363_, 5);
v_suppressElabErrors_1465_ = lean_ctor_get_uint8(v___y_1363_, sizeof(void*)*14 + 1);
v___x_1466_ = lean_box(v___y_1460_);
v___x_1467_ = lean_box(v_suppressElabErrors_1465_);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1468_, 0, v___x_1466_);
lean_closure_set(v___f_1468_, 1, v___x_1467_);
v___x_1469_ = 1;
v___x_1470_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1359_, v___x_1469_);
if (v___x_1470_ == 0)
{
v___y_1452_ = v_fileName_1461_;
v___y_1453_ = v___f_1468_;
v___y_1454_ = v_ref_1464_;
v___y_1455_ = v_fileMap_1462_;
v___y_1456_ = v_suppressElabErrors_1465_;
v___y_1457_ = v___y_1460_;
v___y_1458_ = v___x_1470_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = l_Lean_warningAsError;
v___x_1472_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_1463_, v___x_1471_);
v___y_1452_ = v_fileName_1461_;
v___y_1453_ = v___f_1468_;
v___y_1454_ = v_ref_1464_;
v___y_1455_ = v_fileMap_1462_;
v___y_1456_ = v_suppressElabErrors_1465_;
v___y_1457_ = v___y_1460_;
v___y_1458_ = v___x_1472_;
goto v___jp_1451_;
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v_msgData_1358_);
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1477_, lean_object* v_msgData_1478_, lean_object* v_severity_1479_, lean_object* v_isSilent_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
uint8_t v_severity_boxed_1486_; uint8_t v_isSilent_boxed_1487_; lean_object* v_res_1488_; 
v_severity_boxed_1486_ = lean_unbox(v_severity_1479_);
v_isSilent_boxed_1487_ = lean_unbox(v_isSilent_1480_);
v_res_1488_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1477_, v_msgData_1478_, v_severity_boxed_1486_, v_isSilent_boxed_1487_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v_ref_1477_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(lean_object* v_ref_1489_, lean_object* v_msgData_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v___x_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = 1;
v___x_1501_ = 0;
v___x_1502_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1489_, v_msgData_1490_, v___x_1500_, v___x_1501_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(lean_object* v_ref_1503_, lean_object* v_msgData_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_ref_1503_, v_msgData_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_ref_1503_);
return v_res_1514_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2));
v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_linterOption_1521_, lean_object* v_stx_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_name_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1550_; 
v_name_1533_ = lean_ctor_get(v_linterOption_1521_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_linterOption_1521_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_linterOption_1521_, 1);
lean_dec(v_unused_1551_);
v___x_1535_ = v_linterOption_1521_;
v_isShared_1536_ = v_isSharedCheck_1550_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_name_1533_);
lean_dec(v_linterOption_1521_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1550_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1537_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
lean_inc(v_name_1533_);
v___x_1538_ = l_Lean_MessageData_ofName(v_name_1533_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 7);
lean_ctor_set(v___x_1535_, 1, v___x_1538_);
lean_ctor_set(v___x_1535_, 0, v___x_1537_);
v___x_1540_ = v___x_1535_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v_disable_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1541_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v_disable_1543_ = l_Lean_MessageData_note(v___x_1542_);
v___x_1544_ = l_Lean_Linter_linterMessageTag;
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_msg_1523_);
lean_ctor_set(v___x_1545_, 1, v_disable_1543_);
v___x_1546_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_name_1533_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_stx_1522_, v___x_1547_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_linterOption_1552_, lean_object* v_stx_1553_, lean_object* v_msg_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_linterOption_1552_, v_stx_1553_, v_msg_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v_stx_1553_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object* v___y_1565_, lean_object* v_mkInfoTree_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v_a_1574_, lean_object* v_a_x3f_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_infoState_1578_; lean_object* v_trees_1579_; lean_object* v___x_1580_; 
v___x_1577_ = lean_st_ref_get(v___y_1565_);
v_infoState_1578_ = lean_ctor_get(v___x_1577_, 7);
lean_inc_ref(v_infoState_1578_);
lean_dec(v___x_1577_);
v_trees_1579_ = lean_ctor_get(v_infoState_1578_, 2);
lean_inc_ref(v_trees_1579_);
lean_dec_ref(v_infoState_1578_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1572_);
lean_inc_ref(v___y_1571_);
lean_inc(v___y_1570_);
lean_inc_ref(v___y_1569_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
v___x_1580_ = lean_apply_10(v_mkInfoTree_1566_, v_trees_1579_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1565_, lean_box(0));
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1619_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1619_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1619_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v_infoState_1586_; lean_object* v_env_1587_; lean_object* v_nextMacroScope_1588_; lean_object* v_ngen_1589_; lean_object* v_auxDeclNGen_1590_; lean_object* v_traceState_1591_; lean_object* v_cache_1592_; lean_object* v_messages_1593_; lean_object* v_snapshotTasks_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1618_; 
v___x_1585_ = lean_st_ref_take(v___y_1565_);
v_infoState_1586_ = lean_ctor_get(v___x_1585_, 7);
v_env_1587_ = lean_ctor_get(v___x_1585_, 0);
v_nextMacroScope_1588_ = lean_ctor_get(v___x_1585_, 1);
v_ngen_1589_ = lean_ctor_get(v___x_1585_, 2);
v_auxDeclNGen_1590_ = lean_ctor_get(v___x_1585_, 3);
v_traceState_1591_ = lean_ctor_get(v___x_1585_, 4);
v_cache_1592_ = lean_ctor_get(v___x_1585_, 5);
v_messages_1593_ = lean_ctor_get(v___x_1585_, 6);
v_snapshotTasks_1594_ = lean_ctor_get(v___x_1585_, 8);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1596_ = v___x_1585_;
v_isShared_1597_ = v_isSharedCheck_1618_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_snapshotTasks_1594_);
lean_inc(v_infoState_1586_);
lean_inc(v_messages_1593_);
lean_inc(v_cache_1592_);
lean_inc(v_traceState_1591_);
lean_inc(v_auxDeclNGen_1590_);
lean_inc(v_ngen_1589_);
lean_inc(v_nextMacroScope_1588_);
lean_inc(v_env_1587_);
lean_dec(v___x_1585_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1618_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
uint8_t v_enabled_1598_; lean_object* v_assignment_1599_; lean_object* v_lazyAssignment_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1616_; 
v_enabled_1598_ = lean_ctor_get_uint8(v_infoState_1586_, sizeof(void*)*3);
v_assignment_1599_ = lean_ctor_get(v_infoState_1586_, 0);
v_lazyAssignment_1600_ = lean_ctor_get(v_infoState_1586_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_infoState_1586_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v_infoState_1586_, 2);
lean_dec(v_unused_1617_);
v___x_1602_ = v_infoState_1586_;
v_isShared_1603_ = v_isSharedCheck_1616_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_lazyAssignment_1600_);
lean_inc(v_assignment_1599_);
lean_dec(v_infoState_1586_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1616_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = l_Lean_PersistentArray_push___redArg(v_a_1574_, v_a_1581_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 2, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_assignment_1599_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_lazyAssignment_1600_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v___x_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*3, v_enabled_1598_);
v___x_1606_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 7, v___x_1606_);
v___x_1608_ = v___x_1596_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_env_1587_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_nextMacroScope_1588_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_ngen_1589_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_auxDeclNGen_1590_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_traceState_1591_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v_cache_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_messages_1593_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_snapshotTasks_1594_);
v___x_1608_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1609_ = lean_st_ref_set(v___y_1565_, v___x_1608_);
v___x_1610_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1610_);
v___x_1612_ = v___x_1583_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_a_1574_);
v_a_1620_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1580_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1580_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object* v___y_1628_, lean_object* v_mkInfoTree_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v_a_1637_, lean_object* v_a_x3f_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1628_, v_mkInfoTree_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v_a_1637_, v_a_x3f_1638_);
lean_dec(v_a_x3f_1638_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1628_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object* v_x_1641_, lean_object* v_mkInfoTree_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v_infoState_1653_; uint8_t v_enabled_1654_; 
v___x_1652_ = lean_st_ref_get(v___y_1650_);
v_infoState_1653_ = lean_ctor_get(v___x_1652_, 7);
lean_inc_ref(v_infoState_1653_);
lean_dec(v___x_1652_);
v_enabled_1654_ = lean_ctor_get_uint8(v_infoState_1653_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1653_);
if (v_enabled_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_dec_ref(v_mkInfoTree_1642_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
v___x_1655_ = lean_apply_9(v_x_1641_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, lean_box(0));
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v_a_1657_; lean_object* v_r_1658_; 
v___x_1656_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1650_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
v_r_1658_ = lean_apply_9(v_x_1641_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, lean_box(0));
if (lean_obj_tag(v_r_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1683_; 
v_a_1659_ = lean_ctor_get(v_r_1658_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_r_1658_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1661_ = v_r_1658_;
v_isShared_1662_ = v_isSharedCheck_1683_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v_r_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1683_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
lean_inc(v_a_1659_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 1);
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1650_, v_mkInfoTree_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v_a_1657_, v___x_1664_);
lean_dec_ref(v___x_1664_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; 
v_unused_1673_ = lean_ctor_get(v___x_1665_, 0);
lean_dec(v_unused_1673_);
v___x_1667_ = v___x_1665_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_dec(v___x_1665_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v_a_1659_);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1659_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_a_1659_);
v_a_1674_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1665_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1665_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_a_1684_ = lean_ctor_get(v_r_1658_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v_r_1658_, 1);
v___x_1685_ = lean_box(0);
v___x_1686_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1650_, v_mkInfoTree_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v_a_1657_, v___x_1685_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1686_, 0);
lean_dec(v_unused_1694_);
v___x_1688_ = v___x_1686_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_dec(v___x_1686_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 1);
lean_ctor_set(v___x_1688_, 0, v_a_1684_);
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1684_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_a_1684_);
v_a_1695_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1686_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1686_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object* v_x_1703_, lean_object* v_mkInfoTree_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_1703_, v_mkInfoTree_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v_env_1719_; lean_object* v___x_1720_; lean_object* v_toEnvExtension_1721_; lean_object* v_asyncMode_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_merged_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v___x_1718_ = lean_st_ref_get(v___y_1716_);
v_env_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc_ref(v_env_1719_);
lean_dec(v___x_1718_);
v___x_1720_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1721_ = lean_ctor_get(v___x_1720_, 0);
v_asyncMode_1722_ = lean_ctor_get(v_toEnvExtension_1721_, 2);
v___x_1723_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1724_ = lean_box(0);
v___x_1725_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1723_, v___x_1720_, v_env_1719_, v_asyncMode_1722_, v___x_1724_);
v_merged_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v___x_1725_, 1);
lean_dec(v_unused_1735_);
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_merged_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v_merged_1726_);
lean_ctor_set(v___x_1728_, 0, v_o_1715_);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_o_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_merged_1726_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_1736_, v___y_1737_);
lean_dec(v___y_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_options_1749_; lean_object* v___x_1750_; 
v_options_1749_ = lean_ctor_get(v___y_1746_, 2);
lean_inc_ref(v_options_1749_);
v___x_1750_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_1749_, v___y_1747_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1760_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2));
v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
return v___x_1766_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4));
v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_usingArg_1782_, lean_object* v_snd_1783_, uint8_t v___x_1784_, uint8_t v___x_1785_, lean_object* v___x_1786_, uint8_t v_useReducible_1787_, uint8_t v___x_1788_, lean_object* v___x_1789_, lean_object* v___x_1790_, lean_object* v_simprocs_1791_, lean_object* v_discharge_x3f_1792_, lean_object* v_snd_1793_, lean_object* v___x_1794_, lean_object* v___f_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; 
if (lean_obj_tag(v_usingArg_1782_) == 1)
{
lean_object* v_val_1986_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___x_2038_; lean_object* v_infoState_2039_; uint8_t v_enabled_2040_; 
v_val_1986_ = lean_ctor_get(v_usingArg_1782_, 0);
lean_inc(v_val_1986_);
lean_dec_ref_known(v_usingArg_1782_, 1);
v___x_2038_ = lean_st_ref_get(v___y_1803_);
v_infoState_2039_ = lean_ctor_get(v___x_2038_, 7);
lean_inc_ref(v_infoState_2039_);
lean_dec(v___x_2038_);
v_enabled_2040_ = lean_ctor_get_uint8(v_infoState_2039_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2039_);
if (v_enabled_2040_ == 0)
{
lean_dec_ref(v___f_1795_);
v___y_1988_ = v___y_1796_;
v___y_1989_ = v___y_1797_;
v___y_1990_ = v___y_1798_;
v___y_1991_ = v___y_1799_;
v___y_1992_ = v___y_1800_;
v___y_1993_ = v___y_1801_;
v___y_1994_ = v___y_1802_;
v___y_1995_ = v___y_1803_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2041_; lean_object* v_a_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; 
v___x_2041_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1803_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
v___f_2043_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2043_, 0, v_a_2042_);
v___x_2044_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_2043_, v___f_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_dec_ref_known(v___x_2044_, 1);
v___y_1988_ = v___y_1796_;
v___y_1989_ = v___y_1797_;
v___y_1990_ = v___y_1798_;
v___y_1991_ = v___y_1799_;
v___y_1992_ = v___y_1800_;
v___y_1993_ = v___y_1801_;
v___y_1994_ = v___y_1802_;
v___y_1995_ = v___y_1803_;
goto v___jp_1987_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_val_1986_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
v___jp_1987_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = lean_st_ref_get(v___y_1993_);
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Lean_Elab_Tactic_elabTerm(v_val_1986_, v___x_1997_, v___x_1784_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc_n(v_a_1999_, 2);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_1783_, v_a_1999_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_mctx_2001_; lean_object* v_a_2002_; uint8_t v___x_2003_; 
v_mctx_2001_ = lean_ctor_get(v___x_1996_, 0);
lean_inc_ref(v_mctx_2001_);
lean_dec(v___x_1996_);
v_a_2002_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2003_ = lean_unbox(v_a_2002_);
lean_dec(v_a_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_mctx_2001_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
v___x_2004_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
v___x_2005_ = l_Lean_indentExpr(v_a_1999_);
v___x_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_Lean_Expr_mvar___override(v_snd_1783_);
v___x_2010_ = l_Lean_MessageData_ofExpr(v___x_2009_);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2008_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_2011_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
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
else
{
lean_object* v_mvarCounter_2021_; 
v_mvarCounter_2021_ = lean_ctor_get(v_mctx_2001_, 3);
lean_inc(v_mvarCounter_2021_);
lean_dec_ref(v_mctx_2001_);
lean_inc(v_a_1999_);
v___y_1870_ = v_mvarCounter_2021_;
v___y_1871_ = v_a_1999_;
v___y_1872_ = v___x_1997_;
v___y_1873_ = v_a_1999_;
v___y_1874_ = v___x_1997_;
v___y_1875_ = v___y_1988_;
v___y_1876_ = v___y_1989_;
v___y_1877_ = v___y_1990_;
v___y_1878_ = v___y_1991_;
v___y_1879_ = v___y_1992_;
v___y_1880_ = v___y_1993_;
v___y_1881_ = v___y_1994_;
v___y_1882_ = v___y_1995_;
goto v___jp_1869_;
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_a_1999_);
lean_dec(v___x_1996_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_2022_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2000_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2000_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v___x_1996_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_2030_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1998_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1998_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
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
lean_object* v_lctx_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec_ref(v___f_1795_);
lean_dec_ref(v___x_1786_);
lean_dec(v_usingArg_1782_);
v_lctx_2053_ = lean_ctor_get(v___y_1800_, 2);
v___x_2054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13));
v___x_2055_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2053_, v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 1)
{
lean_object* v_val_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_val_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_val_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = l_Lean_LocalDecl_fvarId(v_val_2056_);
lean_dec(v_val_2056_);
v___x_2058_ = lean_mk_empty_array_with_capacity(v___x_1789_);
v___x_2059_ = lean_array_push(v___x_2058_, v___x_2057_);
lean_inc_ref(v_snd_1793_);
v___x_2060_ = l_Lean_Meta_simpGoal(v_snd_1783_, v___x_1790_, v_simprocs_1791_, v_discharge_x3f_1792_, v___x_1785_, v___x_2059_, v_snd_1793_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2089_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2089_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2089_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_fst_2065_; 
v_fst_2065_ = lean_ctor_get(v_a_2061_, 0);
if (lean_obj_tag(v_fst_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v_snd_2067_; lean_object* v_snd_2068_; lean_object* v___x_2069_; 
lean_del_object(v___x_2063_);
lean_dec_ref(v_snd_1793_);
v_val_2066_ = lean_ctor_get(v_fst_2065_, 0);
lean_inc(v_val_2066_);
v_snd_2067_ = lean_ctor_get(v_a_2061_, 1);
lean_inc(v_snd_2067_);
lean_dec(v_a_2061_);
v_snd_2068_ = lean_ctor_get(v_val_2066_, 1);
lean_inc(v_snd_2068_);
lean_dec(v_val_2066_);
v___x_2069_ = l_Lean_MVarId_assumption(v_snd_2068_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v___x_2069_, 0);
lean_dec(v_unused_2077_);
v___x_2071_ = v___x_2069_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v___x_2069_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v_snd_2067_);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_snd_2067_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_snd_2067_);
v_a_2078_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2069_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2069_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v___x_2087_; 
lean_dec(v_a_2061_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v_snd_1793_);
v___x_2087_ = v___x_2063_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_snd_1793_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_snd_1793_);
v_a_2090_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2060_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2060_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v___x_2055_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
v___x_2098_ = l_Lean_MVarId_assumption(v_snd_1783_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v___x_2098_, 0);
lean_dec(v_unused_2106_);
v___x_2100_ = v___x_2098_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_dec(v___x_2098_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v_snd_1793_);
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_snd_1793_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v_snd_1793_);
v_a_2107_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2098_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2098_);
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
}
v___jp_1805_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v___x_1809_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_1783_, v___y_1806_, v___y_1808_);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1817_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___y_1807_);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___y_1807_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
v___jp_1818_:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_Core_mkFreshUserName(v___y_1831_, v___y_1833_, v___y_1823_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_n(v_a_1836_, 2);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = l_Lean_MVarId_rename(v___y_1830_, v___y_1834_, v_a_1836_, v___y_1828_, v___y_1827_, v___y_1833_, v___y_1823_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_n(v_a_1838_, 2);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = lean_box(v___x_1784_);
v___x_1840_ = lean_box(v___x_1785_);
v___x_1841_ = lean_box(v_useReducible_1787_);
v___x_1842_ = lean_box(v___x_1788_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 19, 10);
lean_closure_set(v___f_1843_, 0, v_a_1838_);
lean_closure_set(v___f_1843_, 1, v_a_1836_);
lean_closure_set(v___f_1843_, 2, v___x_1839_);
lean_closure_set(v___f_1843_, 3, v___x_1840_);
lean_closure_set(v___f_1843_, 4, v___y_1820_);
lean_closure_set(v___f_1843_, 5, v___y_1819_);
lean_closure_set(v___f_1843_, 6, v___x_1786_);
lean_closure_set(v___f_1843_, 7, v___y_1821_);
lean_closure_set(v___f_1843_, 8, v___x_1841_);
lean_closure_set(v___f_1843_, 9, v___x_1842_);
v___x_1844_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1838_, v___f_1843_, v___y_1824_, v___y_1826_, v___y_1825_, v___y_1832_, v___y_1828_, v___y_1827_, v___y_1833_, v___y_1823_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_dec_ref_known(v___x_1844_, 1);
v___y_1806_ = v___y_1822_;
v___y_1807_ = v___y_1829_;
v___y_1808_ = v___y_1827_;
goto v___jp_1805_;
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___y_1822_);
lean_dec(v_snd_1783_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_a_1836_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_1853_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1837_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1837_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v___y_1834_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_1861_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1835_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1835_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
v___jp_1869_:
{
lean_object* v___x_1883_; 
lean_inc(v_snd_1783_);
v___x_1883_ = l_Lean_MVarId_getType(v_snd_1783_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
lean_inc(v_snd_1783_);
v___x_1885_ = l_Lean_MVarId_getTag(v_snd_1783_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1884_, v_a_1886_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = l_Lean_Expr_mvarId_x21(v_a_1888_);
v___x_1890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1));
lean_inc_ref(v___y_1873_);
v___x_1891_ = l_Lean_MVarId_note(v___x_1889_, v___x_1890_, v___y_1873_, v___y_1874_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1953_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v_fst_1893_ = lean_ctor_get(v_a_1892_, 0);
v_snd_1894_ = lean_ctor_get(v_a_1892_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_a_1892_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1896_ = v_a_1892_;
v_isShared_1897_ = v_isSharedCheck_1953_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snd_1894_);
lean_inc(v_fst_1893_);
lean_dec(v_a_1892_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1953_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_mk_empty_array_with_capacity(v___x_1789_);
lean_inc(v_fst_1893_);
v___x_1899_ = lean_array_push(v___x_1898_, v_fst_1893_);
v___x_1900_ = l_Lean_Meta_simpGoal(v_snd_1894_, v___x_1790_, v_simprocs_1791_, v_discharge_x3f_1792_, v___x_1785_, v___x_1899_, v_snd_1793_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v_fst_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v_fst_1902_ = lean_ctor_get(v_a_1901_, 0);
if (lean_obj_tag(v_fst_1902_) == 0)
{
lean_object* v_snd_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_fst_1893_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___x_1786_);
v_snd_1903_ = lean_ctor_get(v_a_1901_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_a_1901_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_a_1901_, 0);
lean_dec(v_unused_1937_);
v___x_1905_ = v_a_1901_;
v_isShared_1906_ = v_isSharedCheck_1936_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_snd_1903_);
lean_dec(v_a_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1936_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v_a_1908_; uint8_t v___x_1909_; 
v___x_1907_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1907_);
v___x_1909_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1908_);
lean_dec(v_a_1908_);
if (v___x_1909_ == 0)
{
lean_del_object(v___x_1905_);
lean_del_object(v___x_1896_);
lean_dec_ref(v___y_1873_);
v___y_1806_ = v_a_1888_;
v___y_1807_ = v_snd_1903_;
v___y_1808_ = v___y_1880_;
goto v___jp_1805_;
}
else
{
if (lean_obj_tag(v___y_1873_) == 1)
{
lean_object* v_fvarId_1910_; lean_object* v_lctx_1911_; lean_object* v___x_1912_; 
v_fvarId_1910_ = lean_ctor_get(v___y_1873_, 0);
v_lctx_1911_ = lean_ctor_get(v___y_1879_, 2);
lean_inc(v_fvarId_1910_);
lean_inc_ref(v_lctx_1911_);
v___x_1912_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1911_, v_fvarId_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_dec_ref_known(v___y_1873_, 1);
lean_del_object(v___x_1905_);
lean_del_object(v___x_1896_);
v___y_1806_ = v_a_1888_;
v___y_1807_ = v_snd_1903_;
v___y_1808_ = v___y_1880_;
goto v___jp_1805_;
}
else
{
lean_dec_ref_known(v___x_1912_, 1);
if (v___x_1788_ == 0)
{
lean_dec_ref_known(v___y_1873_, 1);
lean_del_object(v___x_1905_);
lean_del_object(v___x_1896_);
v___y_1806_ = v_a_1888_;
v___y_1807_ = v_snd_1903_;
v___y_1808_ = v___y_1880_;
goto v___jp_1805_;
}
else
{
lean_object* v_ref_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v_ref_1913_ = lean_ctor_get(v___y_1881_, 5);
v___x_1914_ = l_linter_unnecessarySimpa;
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_1916_ = l_Lean_MessageData_ofExpr(v___y_1873_);
lean_inc_ref(v___x_1916_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 7);
lean_ctor_set(v___x_1905_, 1, v___x_1916_);
lean_ctor_set(v___x_1905_, 0, v___x_1915_);
v___x_1918_ = v___x_1905_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 7);
lean_ctor_set(v___x_1896_, 1, v___x_1919_);
lean_ctor_set(v___x_1896_, 0, v___x_1918_);
v___x_1921_ = v___x_1896_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v___x_1916_);
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_1914_, v_ref_1913_, v___x_1924_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_dec_ref_known(v___x_1925_, 1);
v___y_1806_ = v_a_1888_;
v___y_1807_ = v_snd_1903_;
v___y_1808_ = v___y_1880_;
goto v___jp_1805_;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_snd_1903_);
lean_dec(v_a_1888_);
lean_dec(v_snd_1783_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
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
lean_del_object(v___x_1905_);
lean_del_object(v___x_1896_);
lean_dec_ref(v___y_1873_);
v___y_1806_ = v_a_1888_;
v___y_1807_ = v_snd_1903_;
v___y_1808_ = v___y_1880_;
goto v___jp_1805_;
}
}
}
}
else
{
lean_object* v_val_1938_; lean_object* v_snd_1939_; lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
lean_del_object(v___x_1896_);
lean_dec_ref(v___y_1873_);
v_val_1938_ = lean_ctor_get(v_fst_1902_, 0);
lean_inc(v_val_1938_);
v_snd_1939_ = lean_ctor_get(v_a_1901_, 1);
lean_inc(v_snd_1939_);
lean_dec(v_a_1901_);
v_fst_1940_ = lean_ctor_get(v_val_1938_, 0);
lean_inc(v_fst_1940_);
v_snd_1941_ = lean_ctor_get(v_val_1938_, 1);
lean_inc(v_snd_1941_);
lean_dec(v_val_1938_);
v___x_1942_ = lean_array_get_size(v_fst_1940_);
v___x_1943_ = lean_nat_dec_lt(v___x_1794_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_dec(v_fst_1940_);
v___y_1819_ = v___y_1870_;
v___y_1820_ = v___y_1871_;
v___y_1821_ = v___y_1872_;
v___y_1822_ = v_a_1888_;
v___y_1823_ = v___y_1882_;
v___y_1824_ = v___y_1875_;
v___y_1825_ = v___y_1877_;
v___y_1826_ = v___y_1876_;
v___y_1827_ = v___y_1880_;
v___y_1828_ = v___y_1879_;
v___y_1829_ = v_snd_1939_;
v___y_1830_ = v_snd_1941_;
v___y_1831_ = v___x_1890_;
v___y_1832_ = v___y_1878_;
v___y_1833_ = v___y_1881_;
v___y_1834_ = v_fst_1893_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1944_; 
lean_dec(v_fst_1893_);
v___x_1944_ = lean_array_fget(v_fst_1940_, v___x_1794_);
lean_dec(v_fst_1940_);
v___y_1819_ = v___y_1870_;
v___y_1820_ = v___y_1871_;
v___y_1821_ = v___y_1872_;
v___y_1822_ = v_a_1888_;
v___y_1823_ = v___y_1882_;
v___y_1824_ = v___y_1875_;
v___y_1825_ = v___y_1877_;
v___y_1826_ = v___y_1876_;
v___y_1827_ = v___y_1880_;
v___y_1828_ = v___y_1879_;
v___y_1829_ = v_snd_1939_;
v___y_1830_ = v_snd_1941_;
v___y_1831_ = v___x_1890_;
v___y_1832_ = v___y_1878_;
v___y_1833_ = v___y_1881_;
v___y_1834_ = v___x_1944_;
goto v___jp_1818_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1896_);
lean_dec(v_fst_1893_);
lean_dec(v_a_1888_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_1945_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1900_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1900_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_a_1888_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_1954_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1891_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1891_);
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
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_1962_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1887_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1887_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v_a_1884_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_1970_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1885_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1885_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v_snd_1793_);
lean_dec(v_discharge_x3f_1792_);
lean_dec_ref(v_simprocs_1791_);
lean_dec_ref(v___x_1790_);
lean_dec_ref(v___x_1786_);
lean_dec(v_snd_1783_);
v_a_1978_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1883_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1883_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2115_ = _args[0];
lean_object* v_snd_2116_ = _args[1];
lean_object* v___x_2117_ = _args[2];
lean_object* v___x_2118_ = _args[3];
lean_object* v___x_2119_ = _args[4];
lean_object* v_useReducible_2120_ = _args[5];
lean_object* v___x_2121_ = _args[6];
lean_object* v___x_2122_ = _args[7];
lean_object* v___x_2123_ = _args[8];
lean_object* v_simprocs_2124_ = _args[9];
lean_object* v_discharge_x3f_2125_ = _args[10];
lean_object* v_snd_2126_ = _args[11];
lean_object* v___x_2127_ = _args[12];
lean_object* v___f_2128_ = _args[13];
lean_object* v___y_2129_ = _args[14];
lean_object* v___y_2130_ = _args[15];
lean_object* v___y_2131_ = _args[16];
lean_object* v___y_2132_ = _args[17];
lean_object* v___y_2133_ = _args[18];
lean_object* v___y_2134_ = _args[19];
lean_object* v___y_2135_ = _args[20];
lean_object* v___y_2136_ = _args[21];
lean_object* v___y_2137_ = _args[22];
_start:
{
uint8_t v___x_95774__boxed_2138_; uint8_t v___x_95775__boxed_2139_; uint8_t v_useReducible_boxed_2140_; uint8_t v___x_95777__boxed_2141_; lean_object* v_res_2142_; 
v___x_95774__boxed_2138_ = lean_unbox(v___x_2117_);
v___x_95775__boxed_2139_ = lean_unbox(v___x_2118_);
v_useReducible_boxed_2140_ = lean_unbox(v_useReducible_2120_);
v___x_95777__boxed_2141_ = lean_unbox(v___x_2121_);
v_res_2142_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2115_, v_snd_2116_, v___x_95774__boxed_2138_, v___x_95775__boxed_2139_, v___x_2119_, v_useReducible_boxed_2140_, v___x_95777__boxed_2141_, v___x_2122_, v___x_2123_, v_simprocs_2124_, v_discharge_x3f_2125_, v_snd_2126_, v___x_2127_, v___f_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___x_2127_);
lean_dec(v___x_2122_);
return v_res_2142_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2143_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_unsigned_to_nat(32u);
v___x_2147_ = lean_mk_empty_array_with_capacity(v___x_2146_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2153_ = l_Lean_MessageData_ofFormat(v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v___x_2154_, lean_object* v_tk_2155_, lean_object* v___x_2156_, lean_object* v___x_2157_, lean_object* v___x_2158_, lean_object* v_simprocs_2159_, uint8_t v___x_2160_, lean_object* v_usingArg_2161_, uint8_t v___x_2162_, lean_object* v___x_2163_, uint8_t v_useReducible_2164_, uint8_t v___x_2165_, lean_object* v___x_2166_, lean_object* v_usingTk_x3f_2167_, lean_object* v_discharge_x3f_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___y_2179_; 
if (lean_obj_tag(v_usingTk_x3f_2167_) == 0)
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_box(0);
v___y_2179_ = v___x_2284_;
goto v___jp_2178_;
}
else
{
lean_object* v_val_2285_; 
v_val_2285_ = lean_ctor_get(v_usingTk_x3f_2167_, 0);
lean_inc(v_val_2285_);
lean_dec_ref_known(v_usingTk_x3f_2167_, 1);
v___y_2179_ = v_val_2285_;
goto v___jp_2178_;
}
v___jp_2178_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2180_ = lean_mk_empty_array_with_capacity(v___x_2154_);
v___x_2181_ = lean_array_push(v___x_2180_, v_tk_2155_);
v___x_2182_ = lean_array_push(v___x_2181_, v___y_2179_);
v___x_2183_ = lean_box(2);
v___x_2184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v___x_2156_);
lean_ctor_set(v___x_2184_, 2, v___x_2182_);
v___x_2185_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2184_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2170_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; size_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = lean_mk_empty_array_with_capacity(v___x_2157_);
v___x_2190_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
lean_inc_n(v___x_2157_, 3);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___x_2157_);
v___x_2192_ = lean_unsigned_to_nat(32u);
v___x_2193_ = lean_mk_empty_array_with_capacity(v___x_2192_);
v___x_2194_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
v___x_2195_ = ((size_t)5ULL);
v___x_2196_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2193_);
lean_ctor_set(v___x_2196_, 2, v___x_2157_);
lean_ctor_set(v___x_2196_, 3, v___x_2157_);
lean_ctor_set_usize(v___x_2196_, 4, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2190_);
lean_ctor_set(v___x_2197_, 1, v___x_2190_);
lean_ctor_set(v___x_2197_, 2, v___x_2190_);
lean_ctor_set(v___x_2197_, 3, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2191_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
lean_inc_ref(v___x_2198_);
lean_inc(v_discharge_x3f_2168_);
lean_inc_ref(v_simprocs_2159_);
lean_inc_ref(v___x_2158_);
v___x_2199_ = l_Lean_Meta_simpGoal(v_a_2188_, v___x_2158_, v_simprocs_2159_, v_discharge_x3f_2168_, v___x_2160_, v___x_2189_, v___x_2198_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v_fst_2201_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v_fst_2201_ = lean_ctor_get(v_a_2200_, 0);
if (lean_obj_tag(v_fst_2201_) == 1)
{
lean_object* v_val_2202_; lean_object* v_snd_2203_; lean_object* v_snd_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref_known(v___x_2198_, 2);
v_val_2202_ = lean_ctor_get(v_fst_2201_, 0);
lean_inc(v_val_2202_);
v_snd_2203_ = lean_ctor_get(v_a_2200_, 1);
lean_inc(v_snd_2203_);
lean_dec(v_a_2200_);
v_snd_2204_ = lean_ctor_get(v_val_2202_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_val_2202_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v_val_2202_, 0);
lean_dec(v_unused_2229_);
v___x_2206_ = v_val_2202_;
v_isShared_2207_ = v_isSharedCheck_2228_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_snd_2204_);
lean_dec(v_val_2202_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2228_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_box(0);
lean_inc(v_snd_2204_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set_tag(v___x_2206_, 1);
lean_ctor_set(v___x_2206_, 1, v___x_2208_);
lean_ctor_set(v___x_2206_, 0, v_snd_2204_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_snd_2204_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2210_, v___y_2170_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v___f_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___y_2217_; lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2211_, 1);
v___f_2212_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2212_, 0, v_a_2186_);
v___x_2213_ = lean_box(v___x_2160_);
v___x_2214_ = lean_box(v___x_2162_);
v___x_2215_ = lean_box(v_useReducible_2164_);
v___x_2216_ = lean_box(v___x_2165_);
lean_inc(v_snd_2204_);
v___y_2217_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 23, 14);
lean_closure_set(v___y_2217_, 0, v_usingArg_2161_);
lean_closure_set(v___y_2217_, 1, v_snd_2204_);
lean_closure_set(v___y_2217_, 2, v___x_2213_);
lean_closure_set(v___y_2217_, 3, v___x_2214_);
lean_closure_set(v___y_2217_, 4, v___x_2163_);
lean_closure_set(v___y_2217_, 5, v___x_2215_);
lean_closure_set(v___y_2217_, 6, v___x_2216_);
lean_closure_set(v___y_2217_, 7, v___x_2166_);
lean_closure_set(v___y_2217_, 8, v___x_2158_);
lean_closure_set(v___y_2217_, 9, v_simprocs_2159_);
lean_closure_set(v___y_2217_, 10, v_discharge_x3f_2168_);
lean_closure_set(v___y_2217_, 11, v_snd_2203_);
lean_closure_set(v___y_2217_, 12, v___x_2157_);
lean_closure_set(v___y_2217_, 13, v___f_2212_);
v___x_2218_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_2204_, v___y_2217_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2218_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_snd_2204_);
lean_dec(v_snd_2203_);
lean_dec(v_a_2186_);
lean_dec(v_discharge_x3f_2168_);
lean_dec(v___x_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_usingArg_2161_);
lean_dec_ref(v_simprocs_2159_);
lean_dec_ref(v___x_2158_);
lean_dec(v___x_2157_);
v_a_2219_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2211_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2211_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_a_2200_);
lean_dec(v_a_2186_);
lean_dec(v_discharge_x3f_2168_);
lean_dec(v___x_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_usingArg_2161_);
lean_dec_ref(v_simprocs_2159_);
lean_dec_ref(v___x_2158_);
lean_dec(v___x_2157_);
v___x_2230_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2233_ = v___x_2230_;
v_isShared_2234_ = v_isSharedCheck_2259_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2259_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
uint8_t v___x_2235_; 
v___x_2235_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2231_);
lean_dec(v_a_2231_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2237_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2198_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2198_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
else
{
lean_object* v_ref_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_del_object(v___x_2233_);
v_ref_2239_ = lean_ctor_get(v___y_2175_, 5);
v___x_2240_ = l_linter_unnecessarySimpa;
v___x_2241_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
v___x_2242_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2240_, v_ref_2239_, v___x_2241_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2242_, 0);
lean_dec(v_unused_2250_);
v___x_2244_ = v___x_2242_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_dec(v___x_2242_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2198_);
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2198_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref_known(v___x_2198_, 2);
v_a_2251_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2242_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2242_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec_ref_known(v___x_2198_, 2);
lean_dec(v_a_2186_);
lean_dec(v_discharge_x3f_2168_);
lean_dec(v___x_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_usingArg_2161_);
lean_dec_ref(v_simprocs_2159_);
lean_dec_ref(v___x_2158_);
lean_dec(v___x_2157_);
v_a_2260_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2199_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2199_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_a_2186_);
lean_dec(v_discharge_x3f_2168_);
lean_dec(v___x_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_usingArg_2161_);
lean_dec_ref(v_simprocs_2159_);
lean_dec_ref(v___x_2158_);
lean_dec(v___x_2157_);
v_a_2268_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2187_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2187_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
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
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_discharge_x3f_2168_);
lean_dec(v___x_2166_);
lean_dec_ref(v___x_2163_);
lean_dec(v_usingArg_2161_);
lean_dec_ref(v_simprocs_2159_);
lean_dec_ref(v___x_2158_);
lean_dec(v___x_2157_);
v_a_2276_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2185_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2185_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v___x_2286_ = _args[0];
lean_object* v_tk_2287_ = _args[1];
lean_object* v___x_2288_ = _args[2];
lean_object* v___x_2289_ = _args[3];
lean_object* v___x_2290_ = _args[4];
lean_object* v_simprocs_2291_ = _args[5];
lean_object* v___x_2292_ = _args[6];
lean_object* v_usingArg_2293_ = _args[7];
lean_object* v___x_2294_ = _args[8];
lean_object* v___x_2295_ = _args[9];
lean_object* v_useReducible_2296_ = _args[10];
lean_object* v___x_2297_ = _args[11];
lean_object* v___x_2298_ = _args[12];
lean_object* v_usingTk_x3f_2299_ = _args[13];
lean_object* v_discharge_x3f_2300_ = _args[14];
lean_object* v___y_2301_ = _args[15];
lean_object* v___y_2302_ = _args[16];
lean_object* v___y_2303_ = _args[17];
lean_object* v___y_2304_ = _args[18];
lean_object* v___y_2305_ = _args[19];
lean_object* v___y_2306_ = _args[20];
lean_object* v___y_2307_ = _args[21];
lean_object* v___y_2308_ = _args[22];
lean_object* v___y_2309_ = _args[23];
_start:
{
uint8_t v___x_96498__boxed_2310_; uint8_t v___x_96499__boxed_2311_; uint8_t v_useReducible_boxed_2312_; uint8_t v___x_96501__boxed_2313_; lean_object* v_res_2314_; 
v___x_96498__boxed_2310_ = lean_unbox(v___x_2292_);
v___x_96499__boxed_2311_ = lean_unbox(v___x_2294_);
v_useReducible_boxed_2312_ = lean_unbox(v_useReducible_2296_);
v___x_96501__boxed_2313_ = lean_unbox(v___x_2297_);
v_res_2314_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2286_, v_tk_2287_, v___x_2288_, v___x_2289_, v___x_2290_, v_simprocs_2291_, v___x_96498__boxed_2310_, v_usingArg_2293_, v___x_96499__boxed_2311_, v___x_2295_, v_useReducible_boxed_2312_, v___x_96501__boxed_2313_, v___x_2298_, v_usingTk_x3f_2299_, v_discharge_x3f_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___x_2286_);
return v_res_2314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2323_ = lean_unsigned_to_nat(38u);
v___x_2324_ = lean_unsigned_to_nat(126u);
v___x_2325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2327_ = l_mkPanicMessageWithDecl(v___x_2326_, v___x_2325_, v___x_2324_, v___x_2323_, v___x_2322_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Array_mkArray0(lean_box(0));
return v___x_2332_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2345_ = lean_unsigned_to_nat(15u);
v___x_2346_ = lean_unsigned_to_nat(127u);
v___x_2347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2349_ = l_mkPanicMessageWithDecl(v___x_2348_, v___x_2347_, v___x_2346_, v___x_2345_, v___x_2344_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v___x_2354_, lean_object* v___x_2355_, uint8_t v___x_2356_, lean_object* v___x_2357_, lean_object* v___x_2358_, uint8_t v_useReducible_2359_, lean_object* v___f_2360_, lean_object* v___x_2361_, lean_object* v___x_2362_, lean_object* v___x_2363_, lean_object* v___x_2364_, lean_object* v___x_2365_, lean_object* v___x_2366_, lean_object* v_usingArg_2367_, lean_object* v___x_2368_, uint8_t v___x_2369_, lean_object* v_usingTk_x3f_2370_, lean_object* v_squeeze_2371_, lean_object* v_unfold_2372_, lean_object* v_args_2373_, lean_object* v_only_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___y_2386_; lean_object* v___y_2390_; lean_object* v_stx_2391_; lean_object* v___y_2392_; lean_object* v_ref_2393_; lean_object* v___y_2394_; lean_object* v___y_2413_; lean_object* v_stx_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v_options_2439_; lean_object* v_ref_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; uint8_t v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2849_; uint8_t v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v_args_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2890_; uint8_t v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v_only_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; uint8_t v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; uint8_t v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; uint8_t v___y_3000_; lean_object* v___y_3002_; uint8_t v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3074_; 
v_options_2439_ = lean_ctor_get(v___y_2382_, 2);
v_ref_2440_ = lean_ctor_get(v___y_2382_, 5);
v___x_2441_ = 0;
v___x_2442_ = l_Lean_SourceInfo_fromRef(v_ref_2440_, v___x_2441_);
v___x_2443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7));
lean_inc_ref(v___x_2354_);
lean_inc_ref(v___x_2353_);
lean_inc_ref(v___x_2352_);
v___x_2444_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2443_);
lean_inc(v___x_2442_);
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2442_);
lean_ctor_set(v___x_2445_, 1, v___x_2443_);
v___x_2446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_2447_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_2375_) == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_3074_ = v___x_3083_;
goto v___jp_3073_;
}
else
{
lean_object* v_val_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_val_3084_ = lean_ctor_get(v___y_2375_, 0);
lean_inc(v_val_3084_);
lean_dec_ref_known(v___y_2375_, 1);
v___x_3085_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_3086_ = lean_array_push(v___x_3085_, v_val_3084_);
v___y_3074_ = v___x_3086_;
goto v___jp_3073_;
}
v___jp_2385_:
{
lean_object* v_diag_2387_; lean_object* v___x_2388_; 
v_diag_2387_ = lean_ctor_get(v___y_2386_, 1);
lean_inc_ref(v_diag_2387_);
lean_dec_ref(v___y_2386_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_diag_2387_);
return v___x_2388_;
}
v___jp_2389_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1));
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v_stx_2391_);
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
lean_ctor_set(v___x_2398_, 2, v___x_2397_);
lean_ctor_set(v___x_2398_, 3, v___x_2397_);
lean_ctor_set(v___x_2398_, 4, v___x_2397_);
lean_ctor_set(v___x_2398_, 5, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_ref_2393_);
v___x_2400_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2));
v___x_2401_ = 4;
v___x_2402_ = l_Lean_MessageData_nil;
v___x_2403_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2351_, v___x_2398_, v___x_2399_, v___x_2400_, v___x_2397_, v___x_2401_, v___x_2402_, v___y_2392_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2392_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_dec_ref_known(v___x_2403_, 1);
v___y_2386_ = v___y_2390_;
goto v___jp_2385_;
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v___y_2390_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
v___jp_2412_:
{
lean_object* v_ref_2417_; 
v_ref_2417_ = lean_ctor_get(v___y_2415_, 5);
lean_inc(v_ref_2417_);
v___y_2390_ = v___y_2413_;
v_stx_2391_ = v_stx_2414_;
v___y_2392_ = v___y_2415_;
v_ref_2393_ = v_ref_2417_;
v___y_2394_ = v___y_2416_;
goto v___jp_2389_;
}
v___jp_2418_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
v___x_2429_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2428_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___y_2413_ = v___y_2419_;
v_stx_2414_ = v_a_2430_;
v___y_2415_ = v___y_2426_;
v___y_2416_ = v___y_2427_;
goto v___jp_2412_;
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v___y_2419_);
lean_dec(v_tk_2351_);
v_a_2431_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2429_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2429_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
v___jp_2448_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = l_Array_append___redArg(v___x_2447_, v___y_2459_);
lean_dec_ref(v___y_2459_);
lean_inc_n(v___y_2457_, 2);
v___x_2461_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2461_, 0, v___y_2457_);
lean_ctor_set(v___x_2461_, 1, v___x_2446_);
lean_ctor_set(v___x_2461_, 2, v___x_2460_);
v___x_2462_ = l_Lean_Syntax_node5(v___y_2457_, v___x_2357_, v___y_2449_, v___y_2455_, v___y_2450_, v___y_2456_, v___x_2461_);
v___x_2463_ = l_Lean_Syntax_node2(v___y_2457_, v___y_2458_, v___y_2454_, v___x_2462_);
v___y_2413_ = v___y_2453_;
v_stx_2414_ = v___x_2463_;
v___y_2415_ = v___y_2452_;
v___y_2416_ = v___y_2451_;
goto v___jp_2412_;
}
v___jp_2464_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = l_Array_append___redArg(v___x_2447_, v___y_2475_);
lean_dec_ref(v___y_2475_);
lean_inc(v___y_2473_);
v___x_2477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2477_, 0, v___y_2473_);
lean_ctor_set(v___x_2477_, 1, v___x_2446_);
lean_ctor_set(v___x_2477_, 2, v___x_2476_);
if (lean_obj_tag(v___y_2469_) == 1)
{
lean_object* v_val_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v___x_2355_);
v_val_2478_ = lean_ctor_get(v___y_2469_, 0);
lean_inc(v_val_2478_);
lean_dec_ref_known(v___y_2469_, 1);
v___x_2479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2473_);
v___x_2480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___y_2473_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_Array_mkArray2___redArg(v___x_2480_, v_val_2478_);
v___y_2449_ = v___y_2465_;
v___y_2450_ = v___y_2466_;
v___y_2451_ = v___y_2467_;
v___y_2452_ = v___y_2468_;
v___y_2453_ = v___y_2472_;
v___y_2454_ = v___y_2471_;
v___y_2455_ = v___y_2470_;
v___y_2456_ = v___x_2477_;
v___y_2457_ = v___y_2473_;
v___y_2458_ = v___y_2474_;
v___y_2459_ = v___x_2481_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2482_; 
lean_dec(v___y_2469_);
v___x_2482_ = lean_mk_empty_array_with_capacity(v___x_2355_);
lean_dec(v___x_2355_);
v___y_2449_ = v___y_2465_;
v___y_2450_ = v___y_2466_;
v___y_2451_ = v___y_2467_;
v___y_2452_ = v___y_2468_;
v___y_2453_ = v___y_2472_;
v___y_2454_ = v___y_2471_;
v___y_2455_ = v___y_2470_;
v___y_2456_ = v___x_2477_;
v___y_2457_ = v___y_2473_;
v___y_2458_ = v___y_2474_;
v___y_2459_ = v___x_2482_;
goto v___jp_2448_;
}
}
v___jp_2483_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = l_Array_append___redArg(v___x_2447_, v___y_2494_);
lean_dec_ref(v___y_2494_);
lean_inc(v___y_2492_);
v___x_2496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2496_, 0, v___y_2492_);
lean_ctor_set(v___x_2496_, 1, v___x_2446_);
lean_ctor_set(v___x_2496_, 2, v___x_2495_);
if (lean_obj_tag(v___y_2491_) == 1)
{
lean_object* v_val_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_val_2497_ = lean_ctor_get(v___y_2491_, 0);
lean_inc(v_val_2497_);
lean_dec_ref_known(v___y_2491_, 1);
v___x_2498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2499_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2498_);
v___x_2500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2492_, 4);
v___x_2501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___y_2492_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Array_append___redArg(v___x_2447_, v_val_2497_);
lean_dec(v_val_2497_);
v___x_2503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2503_, 0, v___y_2492_);
lean_ctor_set(v___x_2503_, 1, v___x_2446_);
lean_ctor_set(v___x_2503_, 2, v___x_2502_);
v___x_2504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___y_2492_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l_Lean_Syntax_node3(v___y_2492_, v___x_2499_, v___x_2501_, v___x_2503_, v___x_2505_);
v___x_2507_ = l_Array_mkArray1___redArg(v___x_2506_);
v___y_2465_ = v___y_2484_;
v___y_2466_ = v___x_2496_;
v___y_2467_ = v___y_2485_;
v___y_2468_ = v___y_2486_;
v___y_2469_ = v___y_2490_;
v___y_2470_ = v___y_2489_;
v___y_2471_ = v___y_2488_;
v___y_2472_ = v___y_2487_;
v___y_2473_ = v___y_2492_;
v___y_2474_ = v___y_2493_;
v___y_2475_ = v___x_2507_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2508_; 
lean_dec(v___y_2491_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2508_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2465_ = v___y_2484_;
v___y_2466_ = v___x_2496_;
v___y_2467_ = v___y_2485_;
v___y_2468_ = v___y_2486_;
v___y_2469_ = v___y_2490_;
v___y_2470_ = v___y_2489_;
v___y_2471_ = v___y_2488_;
v___y_2472_ = v___y_2487_;
v___y_2473_ = v___y_2492_;
v___y_2474_ = v___y_2493_;
v___y_2475_ = v___x_2508_;
goto v___jp_2464_;
}
}
v___jp_2509_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = l_Array_append___redArg(v___x_2447_, v___y_2520_);
lean_dec_ref(v___y_2520_);
lean_inc(v___y_2518_);
v___x_2522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___y_2518_);
lean_ctor_set(v___x_2522_, 1, v___x_2446_);
lean_ctor_set(v___x_2522_, 2, v___x_2521_);
if (lean_obj_tag(v___y_2512_) == 1)
{
lean_object* v_val_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_val_2523_ = lean_ctor_get(v___y_2512_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v___y_2512_, 1);
v___x_2524_ = l_Lean_SourceInfo_fromRef(v_val_2523_, v___x_2356_);
lean_dec(v_val_2523_);
v___x_2525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = l_Array_mkArray1___redArg(v___x_2526_);
v___y_2484_ = v___y_2510_;
v___y_2485_ = v___y_2511_;
v___y_2486_ = v___y_2513_;
v___y_2487_ = v___y_2516_;
v___y_2488_ = v___y_2515_;
v___y_2489_ = v___x_2522_;
v___y_2490_ = v___y_2514_;
v___y_2491_ = v___y_2517_;
v___y_2492_ = v___y_2518_;
v___y_2493_ = v___y_2519_;
v___y_2494_ = v___x_2527_;
goto v___jp_2483_;
}
else
{
lean_object* v___x_2528_; 
lean_dec(v___y_2512_);
v___x_2528_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2484_ = v___y_2510_;
v___y_2485_ = v___y_2511_;
v___y_2486_ = v___y_2513_;
v___y_2487_ = v___y_2516_;
v___y_2488_ = v___y_2515_;
v___y_2489_ = v___x_2522_;
v___y_2490_ = v___y_2514_;
v___y_2491_ = v___y_2517_;
v___y_2492_ = v___y_2518_;
v___y_2493_ = v___y_2519_;
v___y_2494_ = v___x_2528_;
goto v___jp_2483_;
}
}
v___jp_2529_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2544_ = l_Array_append___redArg(v___x_2447_, v___y_2543_);
lean_dec_ref(v___y_2543_);
lean_inc_n(v___y_2542_, 3);
v___x_2545_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2545_, 0, v___y_2542_);
lean_ctor_set(v___x_2545_, 1, v___x_2446_);
lean_ctor_set(v___x_2545_, 2, v___x_2544_);
v___x_2546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___y_2542_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = l_Lean_Syntax_node6(v___y_2542_, v___y_2541_, v___y_2537_, v___y_2536_, v___y_2530_, v___x_2545_, v___x_2547_, v___y_2539_);
v___x_2549_ = l_Lean_Syntax_node4(v___y_2542_, v___y_2534_, v___y_2535_, v___y_2531_, v___y_2532_, v___x_2548_);
v___y_2413_ = v___y_2540_;
v_stx_2414_ = v___x_2549_;
v___y_2415_ = v___y_2538_;
v___y_2416_ = v___y_2533_;
goto v___jp_2412_;
}
v___jp_2550_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = l_Array_append___redArg(v___x_2447_, v___y_2564_);
lean_dec_ref(v___y_2564_);
lean_inc(v___y_2563_);
v___x_2566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2566_, 0, v___y_2563_);
lean_ctor_set(v___x_2566_, 1, v___x_2446_);
lean_ctor_set(v___x_2566_, 2, v___x_2565_);
if (lean_obj_tag(v___y_2556_) == 1)
{
lean_object* v_val_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v___x_2355_);
v_val_2567_ = lean_ctor_get(v___y_2556_, 0);
lean_inc(v_val_2567_);
lean_dec_ref_known(v___y_2556_, 1);
v___x_2568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2569_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2563_, 4);
v___x_2571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2563_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = l_Array_append___redArg(v___x_2447_, v_val_2567_);
lean_dec(v_val_2567_);
v___x_2573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2563_);
lean_ctor_set(v___x_2573_, 1, v___x_2446_);
lean_ctor_set(v___x_2573_, 2, v___x_2572_);
v___x_2574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___y_2563_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l_Lean_Syntax_node3(v___y_2563_, v___x_2569_, v___x_2571_, v___x_2573_, v___x_2575_);
v___x_2577_ = l_Array_mkArray1___redArg(v___x_2576_);
v___y_2530_ = v___x_2566_;
v___y_2531_ = v___y_2551_;
v___y_2532_ = v___y_2552_;
v___y_2533_ = v___y_2553_;
v___y_2534_ = v___y_2554_;
v___y_2535_ = v___y_2555_;
v___y_2536_ = v___y_2557_;
v___y_2537_ = v___y_2558_;
v___y_2538_ = v___y_2559_;
v___y_2539_ = v___y_2560_;
v___y_2540_ = v___y_2561_;
v___y_2541_ = v___y_2562_;
v___y_2542_ = v___y_2563_;
v___y_2543_ = v___x_2577_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2578_; 
lean_dec(v___y_2556_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2578_ = lean_mk_empty_array_with_capacity(v___x_2355_);
lean_dec(v___x_2355_);
v___y_2530_ = v___x_2566_;
v___y_2531_ = v___y_2551_;
v___y_2532_ = v___y_2552_;
v___y_2533_ = v___y_2553_;
v___y_2534_ = v___y_2554_;
v___y_2535_ = v___y_2555_;
v___y_2536_ = v___y_2557_;
v___y_2537_ = v___y_2558_;
v___y_2538_ = v___y_2559_;
v___y_2539_ = v___y_2560_;
v___y_2540_ = v___y_2561_;
v___y_2541_ = v___y_2562_;
v___y_2542_ = v___y_2563_;
v___y_2543_ = v___x_2578_;
goto v___jp_2529_;
}
}
v___jp_2579_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = l_Array_append___redArg(v___x_2447_, v___y_2593_);
lean_dec_ref(v___y_2593_);
lean_inc(v___y_2592_);
v___x_2595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2595_, 0, v___y_2592_);
lean_ctor_set(v___x_2595_, 1, v___x_2446_);
lean_ctor_set(v___x_2595_, 2, v___x_2594_);
if (lean_obj_tag(v___y_2587_) == 1)
{
lean_object* v_val_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_val_2596_ = lean_ctor_get(v___y_2587_, 0);
lean_inc(v_val_2596_);
lean_dec_ref_known(v___y_2587_, 1);
v___x_2597_ = l_Lean_SourceInfo_fromRef(v_val_2596_, v___x_2356_);
lean_dec(v_val_2596_);
v___x_2598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = l_Array_mkArray1___redArg(v___x_2599_);
v___y_2551_ = v___y_2580_;
v___y_2552_ = v___y_2581_;
v___y_2553_ = v___y_2582_;
v___y_2554_ = v___y_2583_;
v___y_2555_ = v___y_2584_;
v___y_2556_ = v___y_2585_;
v___y_2557_ = v___x_2595_;
v___y_2558_ = v___y_2586_;
v___y_2559_ = v___y_2588_;
v___y_2560_ = v___y_2589_;
v___y_2561_ = v___y_2590_;
v___y_2562_ = v___y_2591_;
v___y_2563_ = v___y_2592_;
v___y_2564_ = v___x_2600_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2601_; 
lean_dec(v___y_2587_);
v___x_2601_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2551_ = v___y_2580_;
v___y_2552_ = v___y_2581_;
v___y_2553_ = v___y_2582_;
v___y_2554_ = v___y_2583_;
v___y_2555_ = v___y_2584_;
v___y_2556_ = v___y_2585_;
v___y_2557_ = v___x_2595_;
v___y_2558_ = v___y_2586_;
v___y_2559_ = v___y_2588_;
v___y_2560_ = v___y_2589_;
v___y_2561_ = v___y_2590_;
v___y_2562_ = v___y_2591_;
v___y_2563_ = v___y_2592_;
v___y_2564_ = v___x_2601_;
goto v___jp_2550_;
}
}
v___jp_2602_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2614_ = l_Array_append___redArg(v___x_2447_, v___y_2613_);
lean_dec_ref(v___y_2613_);
lean_inc_n(v___y_2611_, 2);
v___x_2615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2615_, 0, v___y_2611_);
lean_ctor_set(v___x_2615_, 1, v___x_2446_);
lean_ctor_set(v___x_2615_, 2, v___x_2614_);
v___x_2616_ = l_Lean_Syntax_node5(v___y_2611_, v___x_2357_, v___y_2605_, v___y_2606_, v___y_2612_, v___y_2604_, v___x_2615_);
lean_inc(v___y_2610_);
v___x_2617_ = l_Lean_Syntax_node4(v___y_2611_, v___x_2358_, v___y_2603_, v___y_2610_, v___y_2610_, v___x_2616_);
v___y_2413_ = v___y_2609_;
v_stx_2414_ = v___x_2617_;
v___y_2415_ = v___y_2608_;
v___y_2416_ = v___y_2607_;
goto v___jp_2412_;
}
v___jp_2618_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = l_Array_append___redArg(v___x_2447_, v___y_2629_);
lean_dec_ref(v___y_2629_);
lean_inc(v___y_2627_);
v___x_2631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2631_, 0, v___y_2627_);
lean_ctor_set(v___x_2631_, 1, v___x_2446_);
lean_ctor_set(v___x_2631_, 2, v___x_2630_);
if (lean_obj_tag(v___y_2624_) == 1)
{
lean_object* v_val_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec(v___x_2355_);
v_val_2632_ = lean_ctor_get(v___y_2624_, 0);
lean_inc(v_val_2632_);
lean_dec_ref_known(v___y_2624_, 1);
v___x_2633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2627_);
v___x_2634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___y_2627_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = l_Array_mkArray2___redArg(v___x_2634_, v_val_2632_);
v___y_2603_ = v___y_2620_;
v___y_2604_ = v___x_2631_;
v___y_2605_ = v___y_2619_;
v___y_2606_ = v___y_2621_;
v___y_2607_ = v___y_2622_;
v___y_2608_ = v___y_2623_;
v___y_2609_ = v___y_2625_;
v___y_2610_ = v___y_2626_;
v___y_2611_ = v___y_2627_;
v___y_2612_ = v___y_2628_;
v___y_2613_ = v___x_2635_;
goto v___jp_2602_;
}
else
{
lean_object* v___x_2636_; 
lean_dec(v___y_2624_);
v___x_2636_ = lean_mk_empty_array_with_capacity(v___x_2355_);
lean_dec(v___x_2355_);
v___y_2603_ = v___y_2620_;
v___y_2604_ = v___x_2631_;
v___y_2605_ = v___y_2619_;
v___y_2606_ = v___y_2621_;
v___y_2607_ = v___y_2622_;
v___y_2608_ = v___y_2623_;
v___y_2609_ = v___y_2625_;
v___y_2610_ = v___y_2626_;
v___y_2611_ = v___y_2627_;
v___y_2612_ = v___y_2628_;
v___y_2613_ = v___x_2636_;
goto v___jp_2602_;
}
}
v___jp_2637_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = l_Array_append___redArg(v___x_2447_, v___y_2648_);
lean_dec_ref(v___y_2648_);
lean_inc(v___y_2647_);
v___x_2650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2650_, 0, v___y_2647_);
lean_ctor_set(v___x_2650_, 1, v___x_2446_);
lean_ctor_set(v___x_2650_, 2, v___x_2649_);
if (lean_obj_tag(v___y_2645_) == 1)
{
lean_object* v_val_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_val_2651_ = lean_ctor_get(v___y_2645_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v___y_2645_, 1);
v___x_2652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2653_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2652_);
v___x_2654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2647_, 4);
v___x_2655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___y_2647_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = l_Array_append___redArg(v___x_2447_, v_val_2651_);
lean_dec(v_val_2651_);
v___x_2657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2647_);
lean_ctor_set(v___x_2657_, 1, v___x_2446_);
lean_ctor_set(v___x_2657_, 2, v___x_2656_);
v___x_2658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___y_2647_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = l_Lean_Syntax_node3(v___y_2647_, v___x_2653_, v___x_2655_, v___x_2657_, v___x_2659_);
v___x_2661_ = l_Array_mkArray1___redArg(v___x_2660_);
v___y_2619_ = v___y_2639_;
v___y_2620_ = v___y_2638_;
v___y_2621_ = v___y_2640_;
v___y_2622_ = v___y_2641_;
v___y_2623_ = v___y_2642_;
v___y_2624_ = v___y_2644_;
v___y_2625_ = v___y_2643_;
v___y_2626_ = v___y_2646_;
v___y_2627_ = v___y_2647_;
v___y_2628_ = v___x_2650_;
v___y_2629_ = v___x_2661_;
goto v___jp_2618_;
}
else
{
lean_object* v___x_2662_; 
lean_dec(v___y_2645_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2662_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2619_ = v___y_2639_;
v___y_2620_ = v___y_2638_;
v___y_2621_ = v___y_2640_;
v___y_2622_ = v___y_2641_;
v___y_2623_ = v___y_2642_;
v___y_2624_ = v___y_2644_;
v___y_2625_ = v___y_2643_;
v___y_2626_ = v___y_2646_;
v___y_2627_ = v___y_2647_;
v___y_2628_ = v___x_2650_;
v___y_2629_ = v___x_2662_;
goto v___jp_2618_;
}
}
v___jp_2663_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = l_Array_append___redArg(v___x_2447_, v___y_2674_);
lean_dec_ref(v___y_2674_);
lean_inc(v___y_2673_);
v___x_2676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2676_, 0, v___y_2673_);
lean_ctor_set(v___x_2676_, 1, v___x_2446_);
lean_ctor_set(v___x_2676_, 2, v___x_2675_);
if (lean_obj_tag(v___y_2667_) == 1)
{
lean_object* v_val_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_val_2677_ = lean_ctor_get(v___y_2667_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v___y_2667_, 1);
v___x_2678_ = l_Lean_SourceInfo_fromRef(v_val_2677_, v___x_2356_);
lean_dec(v_val_2677_);
v___x_2679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Array_mkArray1___redArg(v___x_2680_);
v___y_2638_ = v___y_2665_;
v___y_2639_ = v___y_2664_;
v___y_2640_ = v___x_2676_;
v___y_2641_ = v___y_2666_;
v___y_2642_ = v___y_2668_;
v___y_2643_ = v___y_2670_;
v___y_2644_ = v___y_2669_;
v___y_2645_ = v___y_2672_;
v___y_2646_ = v___y_2671_;
v___y_2647_ = v___y_2673_;
v___y_2648_ = v___x_2681_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2682_; 
lean_dec(v___y_2667_);
v___x_2682_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2638_ = v___y_2665_;
v___y_2639_ = v___y_2664_;
v___y_2640_ = v___x_2676_;
v___y_2641_ = v___y_2666_;
v___y_2642_ = v___y_2668_;
v___y_2643_ = v___y_2670_;
v___y_2644_ = v___y_2669_;
v___y_2645_ = v___y_2672_;
v___y_2646_ = v___y_2671_;
v___y_2647_ = v___y_2673_;
v___y_2648_ = v___x_2682_;
goto v___jp_2637_;
}
}
v___jp_2683_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2697_ = l_Array_append___redArg(v___x_2447_, v___y_2696_);
lean_dec_ref(v___y_2696_);
lean_inc_n(v___y_2693_, 3);
v___x_2698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2698_, 0, v___y_2693_);
lean_ctor_set(v___x_2698_, 1, v___x_2446_);
lean_ctor_set(v___x_2698_, 2, v___x_2697_);
v___x_2699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___y_2693_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_Syntax_node6(v___y_2693_, v___y_2694_, v___y_2689_, v___y_2685_, v___y_2686_, v___x_2698_, v___x_2700_, v___y_2692_);
lean_inc(v___y_2684_);
v___x_2702_ = l_Lean_Syntax_node4(v___y_2693_, v___y_2688_, v___y_2695_, v___y_2684_, v___y_2684_, v___x_2701_);
v___y_2413_ = v___y_2691_;
v_stx_2414_ = v___x_2702_;
v___y_2415_ = v___y_2690_;
v___y_2416_ = v___y_2687_;
goto v___jp_2412_;
}
v___jp_2703_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = l_Array_append___redArg(v___x_2447_, v___y_2716_);
lean_dec_ref(v___y_2716_);
lean_inc(v___y_2713_);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___y_2713_);
lean_ctor_set(v___x_2718_, 1, v___x_2446_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
if (lean_obj_tag(v___y_2708_) == 1)
{
lean_object* v_val_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec(v___x_2355_);
v_val_2719_ = lean_ctor_get(v___y_2708_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v___y_2708_, 1);
v___x_2720_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2721_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2720_);
v___x_2722_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2713_, 4);
v___x_2723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___y_2713_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = l_Array_append___redArg(v___x_2447_, v_val_2719_);
lean_dec(v_val_2719_);
v___x_2725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2713_);
lean_ctor_set(v___x_2725_, 1, v___x_2446_);
lean_ctor_set(v___x_2725_, 2, v___x_2724_);
v___x_2726_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___y_2713_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = l_Lean_Syntax_node3(v___y_2713_, v___x_2721_, v___x_2723_, v___x_2725_, v___x_2727_);
v___x_2729_ = l_Array_mkArray1___redArg(v___x_2728_);
v___y_2684_ = v___y_2704_;
v___y_2685_ = v___y_2705_;
v___y_2686_ = v___x_2718_;
v___y_2687_ = v___y_2706_;
v___y_2688_ = v___y_2707_;
v___y_2689_ = v___y_2709_;
v___y_2690_ = v___y_2710_;
v___y_2691_ = v___y_2711_;
v___y_2692_ = v___y_2712_;
v___y_2693_ = v___y_2713_;
v___y_2694_ = v___y_2714_;
v___y_2695_ = v___y_2715_;
v___y_2696_ = v___x_2729_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v___y_2708_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2730_ = lean_mk_empty_array_with_capacity(v___x_2355_);
lean_dec(v___x_2355_);
v___y_2684_ = v___y_2704_;
v___y_2685_ = v___y_2705_;
v___y_2686_ = v___x_2718_;
v___y_2687_ = v___y_2706_;
v___y_2688_ = v___y_2707_;
v___y_2689_ = v___y_2709_;
v___y_2690_ = v___y_2710_;
v___y_2691_ = v___y_2711_;
v___y_2692_ = v___y_2712_;
v___y_2693_ = v___y_2713_;
v___y_2694_ = v___y_2714_;
v___y_2695_ = v___y_2715_;
v___y_2696_ = v___x_2730_;
goto v___jp_2683_;
}
}
v___jp_2731_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = l_Array_append___redArg(v___x_2447_, v___y_2744_);
lean_dec_ref(v___y_2744_);
lean_inc(v___y_2741_);
v___x_2746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2746_, 0, v___y_2741_);
lean_ctor_set(v___x_2746_, 1, v___x_2446_);
lean_ctor_set(v___x_2746_, 2, v___x_2745_);
if (lean_obj_tag(v___y_2737_) == 1)
{
lean_object* v_val_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_val_2747_ = lean_ctor_get(v___y_2737_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v___y_2737_, 1);
v___x_2748_ = l_Lean_SourceInfo_fromRef(v_val_2747_, v___x_2356_);
lean_dec(v_val_2747_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = l_Array_mkArray1___redArg(v___x_2750_);
v___y_2704_ = v___y_2732_;
v___y_2705_ = v___x_2746_;
v___y_2706_ = v___y_2733_;
v___y_2707_ = v___y_2734_;
v___y_2708_ = v___y_2735_;
v___y_2709_ = v___y_2736_;
v___y_2710_ = v___y_2738_;
v___y_2711_ = v___y_2739_;
v___y_2712_ = v___y_2740_;
v___y_2713_ = v___y_2741_;
v___y_2714_ = v___y_2742_;
v___y_2715_ = v___y_2743_;
v___y_2716_ = v___x_2751_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2752_; 
lean_dec(v___y_2737_);
v___x_2752_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2704_ = v___y_2732_;
v___y_2705_ = v___x_2746_;
v___y_2706_ = v___y_2733_;
v___y_2707_ = v___y_2734_;
v___y_2708_ = v___y_2735_;
v___y_2709_ = v___y_2736_;
v___y_2710_ = v___y_2738_;
v___y_2711_ = v___y_2739_;
v___y_2712_ = v___y_2740_;
v___y_2713_ = v___y_2741_;
v___y_2714_ = v___y_2742_;
v___y_2715_ = v___y_2743_;
v___y_2716_ = v___x_2752_;
goto v___jp_2703_;
}
}
v___jp_2753_:
{
if (v___y_2760_ == 0)
{
if (v_useReducible_2359_ == 0)
{
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
if (lean_obj_tag(v___y_2756_) == 0)
{
lean_dec(v___y_2768_);
lean_dec(v___y_2764_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___y_2419_ = v___y_2767_;
v___y_2420_ = v___y_2754_;
v___y_2421_ = v___y_2762_;
v___y_2422_ = v___y_2765_;
v___y_2423_ = v___y_2763_;
v___y_2424_ = v___y_2759_;
v___y_2425_ = v___y_2761_;
v___y_2426_ = v___y_2766_;
v___y_2427_ = v___y_2755_;
goto v___jp_2418_;
}
else
{
lean_object* v_val_2769_; lean_object* v___x_2770_; 
v_val_2769_ = lean_ctor_get(v___y_2756_, 0);
lean_inc(v_val_2769_);
lean_dec_ref_known(v___y_2756_, 1);
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2766_);
v___x_2770_ = lean_apply_9(v___f_2360_, v___y_2754_, v___y_2762_, v___y_2765_, v___y_2763_, v___y_2759_, v___y_2761_, v___y_2766_, v___y_2755_, lean_box(0));
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc_n(v_a_2771_, 3);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2354_, 2);
lean_inc_ref_n(v___x_2353_, 2);
lean_inc_ref_n(v___x_2352_, 2);
v___x_2773_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2774_, 0, v_a_2771_);
lean_ctor_set(v___x_2774_, 1, v___x_2361_);
v___x_2775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2771_);
lean_ctor_set(v___x_2775_, 1, v___x_2446_);
lean_ctor_set(v___x_2775_, 2, v___x_2447_);
v___x_2776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2777_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2776_);
if (lean_obj_tag(v___y_2768_) == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2732_ = v___x_2775_;
v___y_2733_ = v___y_2755_;
v___y_2734_ = v___x_2773_;
v___y_2735_ = v___y_2757_;
v___y_2736_ = v___y_2758_;
v___y_2737_ = v___y_2764_;
v___y_2738_ = v___y_2766_;
v___y_2739_ = v___y_2767_;
v___y_2740_ = v_val_2769_;
v___y_2741_ = v_a_2771_;
v___y_2742_ = v___x_2777_;
v___y_2743_ = v___x_2774_;
v___y_2744_ = v___x_2778_;
goto v___jp_2731_;
}
else
{
lean_object* v_val_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_val_2779_ = lean_ctor_get(v___y_2768_, 0);
lean_inc(v_val_2779_);
lean_dec_ref_known(v___y_2768_, 1);
v___x_2780_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2781_ = lean_array_push(v___x_2780_, v_val_2779_);
v___y_2732_ = v___x_2775_;
v___y_2733_ = v___y_2755_;
v___y_2734_ = v___x_2773_;
v___y_2735_ = v___y_2757_;
v___y_2736_ = v___y_2758_;
v___y_2737_ = v___y_2764_;
v___y_2738_ = v___y_2766_;
v___y_2739_ = v___y_2767_;
v___y_2740_ = v_val_2769_;
v___y_2741_ = v_a_2771_;
v___y_2742_ = v___x_2777_;
v___y_2743_ = v___x_2774_;
v___y_2744_ = v___x_2781_;
goto v___jp_2731_;
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_val_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2764_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2755_);
lean_dec_ref(v___x_2361_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v_a_2782_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2770_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2770_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
else
{
lean_object* v___x_2790_; 
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2766_);
v___x_2790_ = lean_apply_9(v___f_2360_, v___y_2754_, v___y_2762_, v___y_2765_, v___y_2763_, v___y_2759_, v___y_2761_, v___y_2766_, v___y_2755_, lean_box(0));
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc_n(v_a_2791_, 3);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_a_2791_);
lean_ctor_set(v___x_2792_, 1, v___x_2361_);
v___x_2793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2793_, 0, v_a_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2446_);
lean_ctor_set(v___x_2793_, 2, v___x_2447_);
if (lean_obj_tag(v___y_2768_) == 0)
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2664_ = v___y_2758_;
v___y_2665_ = v___x_2792_;
v___y_2666_ = v___y_2755_;
v___y_2667_ = v___y_2764_;
v___y_2668_ = v___y_2766_;
v___y_2669_ = v___y_2756_;
v___y_2670_ = v___y_2767_;
v___y_2671_ = v___x_2793_;
v___y_2672_ = v___y_2757_;
v___y_2673_ = v_a_2791_;
v___y_2674_ = v___x_2794_;
goto v___jp_2663_;
}
else
{
lean_object* v_val_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_val_2795_ = lean_ctor_get(v___y_2768_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v___y_2768_, 1);
v___x_2796_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2797_ = lean_array_push(v___x_2796_, v_val_2795_);
v___y_2664_ = v___y_2758_;
v___y_2665_ = v___x_2792_;
v___y_2666_ = v___y_2755_;
v___y_2667_ = v___y_2764_;
v___y_2668_ = v___y_2766_;
v___y_2669_ = v___y_2756_;
v___y_2670_ = v___y_2767_;
v___y_2671_ = v___x_2793_;
v___y_2672_ = v___y_2757_;
v___y_2673_ = v_a_2791_;
v___y_2674_ = v___x_2797_;
goto v___jp_2663_;
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2764_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___x_2361_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v_a_2798_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2790_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2790_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
else
{
lean_dec(v___x_2358_);
if (v_useReducible_2359_ == 0)
{
lean_dec(v___x_2357_);
if (lean_obj_tag(v___y_2756_) == 0)
{
lean_dec(v___y_2768_);
lean_dec(v___y_2764_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___y_2419_ = v___y_2767_;
v___y_2420_ = v___y_2754_;
v___y_2421_ = v___y_2762_;
v___y_2422_ = v___y_2765_;
v___y_2423_ = v___y_2763_;
v___y_2424_ = v___y_2759_;
v___y_2425_ = v___y_2761_;
v___y_2426_ = v___y_2766_;
v___y_2427_ = v___y_2755_;
goto v___jp_2418_;
}
else
{
lean_object* v_val_2806_; lean_object* v___x_2807_; 
v_val_2806_ = lean_ctor_get(v___y_2756_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v___y_2756_, 1);
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2766_);
v___x_2807_ = lean_apply_9(v___f_2360_, v___y_2754_, v___y_2762_, v___y_2765_, v___y_2763_, v___y_2759_, v___y_2761_, v___y_2766_, v___y_2755_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc_n(v_a_2808_, 5);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2354_, 2);
lean_inc_ref_n(v___x_2353_, 2);
lean_inc_ref_n(v___x_2352_, 2);
v___x_2810_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2809_);
v___x_2811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2808_);
lean_ctor_set(v___x_2811_, 1, v___x_2361_);
v___x_2812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2812_, 0, v_a_2808_);
lean_ctor_set(v___x_2812_, 1, v___x_2446_);
lean_ctor_set(v___x_2812_, 2, v___x_2447_);
v___x_2813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_2814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2814_, 0, v_a_2808_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = l_Lean_Syntax_node1(v_a_2808_, v___x_2446_, v___x_2814_);
v___x_2816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2817_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2816_);
if (lean_obj_tag(v___y_2768_) == 0)
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2580_ = v___x_2812_;
v___y_2581_ = v___x_2815_;
v___y_2582_ = v___y_2755_;
v___y_2583_ = v___x_2810_;
v___y_2584_ = v___x_2811_;
v___y_2585_ = v___y_2757_;
v___y_2586_ = v___y_2758_;
v___y_2587_ = v___y_2764_;
v___y_2588_ = v___y_2766_;
v___y_2589_ = v_val_2806_;
v___y_2590_ = v___y_2767_;
v___y_2591_ = v___x_2817_;
v___y_2592_ = v_a_2808_;
v___y_2593_ = v___x_2818_;
goto v___jp_2579_;
}
else
{
lean_object* v_val_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_val_2819_ = lean_ctor_get(v___y_2768_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v___y_2768_, 1);
v___x_2820_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2821_ = lean_array_push(v___x_2820_, v_val_2819_);
v___y_2580_ = v___x_2812_;
v___y_2581_ = v___x_2815_;
v___y_2582_ = v___y_2755_;
v___y_2583_ = v___x_2810_;
v___y_2584_ = v___x_2811_;
v___y_2585_ = v___y_2757_;
v___y_2586_ = v___y_2758_;
v___y_2587_ = v___y_2764_;
v___y_2588_ = v___y_2766_;
v___y_2589_ = v_val_2806_;
v___y_2590_ = v___y_2767_;
v___y_2591_ = v___x_2817_;
v___y_2592_ = v_a_2808_;
v___y_2593_ = v___x_2821_;
goto v___jp_2579_;
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_val_2806_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2764_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2755_);
lean_dec_ref(v___x_2361_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v_a_2822_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2807_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2807_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
else
{
lean_object* v___x_2830_; 
lean_dec_ref(v___x_2361_);
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2766_);
v___x_2830_ = lean_apply_9(v___f_2360_, v___y_2754_, v___y_2762_, v___y_2765_, v___y_2763_, v___y_2759_, v___y_2761_, v___y_2766_, v___y_2755_, lean_box(0));
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc_n(v_a_2831_, 2);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20));
lean_inc_ref(v___x_2354_);
lean_inc_ref(v___x_2353_);
lean_inc_ref(v___x_2352_);
v___x_2833_ = l_Lean_Name_mkStr4(v___x_2352_, v___x_2353_, v___x_2354_, v___x_2832_);
v___x_2834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21));
v___x_2835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2835_, 0, v_a_2831_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
if (lean_obj_tag(v___y_2768_) == 0)
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_2510_ = v___y_2758_;
v___y_2511_ = v___y_2755_;
v___y_2512_ = v___y_2764_;
v___y_2513_ = v___y_2766_;
v___y_2514_ = v___y_2756_;
v___y_2515_ = v___x_2835_;
v___y_2516_ = v___y_2767_;
v___y_2517_ = v___y_2757_;
v___y_2518_ = v_a_2831_;
v___y_2519_ = v___x_2833_;
v___y_2520_ = v___x_2836_;
goto v___jp_2509_;
}
else
{
lean_object* v_val_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_val_2837_ = lean_ctor_get(v___y_2768_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v___y_2768_, 1);
v___x_2838_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2839_ = lean_array_push(v___x_2838_, v_val_2837_);
v___y_2510_ = v___y_2758_;
v___y_2511_ = v___y_2755_;
v___y_2512_ = v___y_2764_;
v___y_2513_ = v___y_2766_;
v___y_2514_ = v___y_2756_;
v___y_2515_ = v___x_2835_;
v___y_2516_ = v___y_2767_;
v___y_2517_ = v___y_2757_;
v___y_2518_ = v_a_2831_;
v___y_2519_ = v___x_2833_;
v___y_2520_ = v___x_2839_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2764_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v_a_2840_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2830_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2830_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
}
}
v___jp_2848_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v___x_2865_ = lean_unsigned_to_nat(5u);
v___x_2866_ = l_Lean_Syntax_getArg(v___y_2855_, v___x_2865_);
lean_dec(v___y_2855_);
v___x_2867_ = l_Lean_Syntax_matchesNull(v___x_2866_, v___x_2355_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec(v_args_2856_);
lean_dec(v___y_2854_);
lean_dec(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec(v___y_2849_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2868_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2869_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2868_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___y_2413_ = v___y_2853_;
v_stx_2414_ = v_a_2870_;
v___y_2415_ = v___y_2863_;
v___y_2416_ = v___y_2864_;
goto v___jp_2412_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v___y_2853_);
lean_dec(v_tk_2351_);
v_a_2871_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2869_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Syntax_getOptional_x3f(v___y_2851_);
lean_dec(v___y_2851_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_box(0);
v___y_2754_ = v___y_2857_;
v___y_2755_ = v___y_2864_;
v___y_2756_ = v___y_2854_;
v___y_2757_ = v_args_2856_;
v___y_2758_ = v___y_2849_;
v___y_2759_ = v___y_2861_;
v___y_2760_ = v___y_2850_;
v___y_2761_ = v___y_2862_;
v___y_2762_ = v___y_2858_;
v___y_2763_ = v___y_2860_;
v___y_2764_ = v___y_2852_;
v___y_2765_ = v___y_2859_;
v___y_2766_ = v___y_2863_;
v___y_2767_ = v___y_2853_;
v___y_2768_ = v___x_2880_;
goto v___jp_2753_;
}
else
{
lean_object* v_val_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
v_val_2881_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2879_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_val_2881_);
lean_dec(v___x_2879_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_val_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
v___y_2754_ = v___y_2857_;
v___y_2755_ = v___y_2864_;
v___y_2756_ = v___y_2854_;
v___y_2757_ = v_args_2856_;
v___y_2758_ = v___y_2849_;
v___y_2759_ = v___y_2861_;
v___y_2760_ = v___y_2850_;
v___y_2761_ = v___y_2862_;
v___y_2762_ = v___y_2858_;
v___y_2763_ = v___y_2860_;
v___y_2764_ = v___y_2852_;
v___y_2765_ = v___y_2859_;
v___y_2766_ = v___y_2863_;
v___y_2767_ = v___y_2853_;
v___y_2768_ = v___x_2886_;
goto v___jp_2753_;
}
}
}
}
}
v___jp_2889_:
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = l_Lean_Syntax_getArg(v___y_2895_, v___x_2362_);
v___x_2906_ = l_Lean_Syntax_isNone(v___x_2905_);
if (v___x_2906_ == 0)
{
uint8_t v___x_2907_; 
lean_inc(v___x_2905_);
v___x_2907_ = l_Lean_Syntax_matchesNull(v___x_2905_, v___x_2363_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v___x_2905_);
lean_dec(v_only_2896_);
lean_dec(v___y_2895_);
lean_dec(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec(v___y_2890_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2908_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2909_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2908_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
v___y_2413_ = v___y_2894_;
v_stx_2414_ = v_a_2910_;
v___y_2415_ = v___y_2903_;
v___y_2416_ = v___y_2904_;
goto v___jp_2412_;
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec_ref(v___y_2894_);
lean_dec(v_tk_2351_);
v_a_2911_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2909_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
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
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = l_Lean_Syntax_getArg(v___x_2905_, v___x_2364_);
lean_dec(v___x_2364_);
lean_dec(v___x_2905_);
v___x_2920_ = l_Lean_Syntax_getArgs(v___x_2919_);
lean_dec(v___x_2919_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
v___y_2849_ = v___y_2890_;
v___y_2850_ = v___y_2891_;
v___y_2851_ = v___y_2892_;
v___y_2852_ = v_only_2896_;
v___y_2853_ = v___y_2894_;
v___y_2854_ = v___y_2893_;
v___y_2855_ = v___y_2895_;
v_args_2856_ = v___x_2921_;
v___y_2857_ = v___y_2897_;
v___y_2858_ = v___y_2898_;
v___y_2859_ = v___y_2899_;
v___y_2860_ = v___y_2900_;
v___y_2861_ = v___y_2901_;
v___y_2862_ = v___y_2902_;
v___y_2863_ = v___y_2903_;
v___y_2864_ = v___y_2904_;
goto v___jp_2848_;
}
}
else
{
lean_object* v___x_2922_; 
lean_dec(v___x_2905_);
lean_dec(v___x_2364_);
v___x_2922_ = lean_box(0);
v___y_2849_ = v___y_2890_;
v___y_2850_ = v___y_2891_;
v___y_2851_ = v___y_2892_;
v___y_2852_ = v_only_2896_;
v___y_2853_ = v___y_2894_;
v___y_2854_ = v___y_2893_;
v___y_2855_ = v___y_2895_;
v_args_2856_ = v___x_2922_;
v___y_2857_ = v___y_2897_;
v___y_2858_ = v___y_2898_;
v___y_2859_ = v___y_2899_;
v___y_2860_ = v___y_2900_;
v___y_2861_ = v___y_2901_;
v___y_2862_ = v___y_2902_;
v___y_2863_ = v___y_2903_;
v___y_2864_ = v___y_2904_;
goto v___jp_2848_;
}
}
v___jp_2923_:
{
lean_object* v_usedTheorems_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_usedTheorems_2928_ = lean_ctor_get(v___y_2925_, 0);
v___x_2929_ = l_Lean_Syntax_unsetTrailing(v___y_2926_);
v___x_2930_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2929_, v_usedTheorems_2928_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; uint8_t v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_n(v_a_2931_, 2);
lean_dec_ref_known(v___x_2930_, 1);
v___x_2932_ = l_Lean_Syntax_isOfKind(v_a_2931_, v___x_2444_);
lean_dec(v___x_2444_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_inc(v_ref_2440_);
lean_dec(v_a_2931_);
lean_dec(v___y_2927_);
lean_dec(v___x_2366_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2933_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2934_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2933_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___y_2390_ = v___y_2925_;
v_stx_2391_ = v_a_2935_;
v___y_2392_ = v___y_2382_;
v_ref_2393_ = v_ref_2440_;
v___y_2394_ = v___y_2383_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec_ref(v___y_2925_);
lean_dec(v_ref_2440_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v_tk_2351_);
v_a_2936_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2934_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = l_Lean_Syntax_getArg(v_a_2931_, v___x_2364_);
lean_inc(v___x_2944_);
v___x_2945_ = l_Lean_Syntax_isOfKind(v___x_2944_, v___x_2365_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_inc(v_ref_2440_);
lean_dec(v___x_2944_);
lean_dec(v_a_2931_);
lean_dec(v___y_2927_);
lean_dec(v___x_2366_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2946_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2947_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2946_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___y_2390_ = v___y_2925_;
v_stx_2391_ = v_a_2948_;
v___y_2392_ = v___y_2382_;
v_ref_2393_ = v_ref_2440_;
v___y_2394_ = v___y_2383_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v___y_2925_);
lean_dec(v_ref_2440_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v_tk_2351_);
v_a_2949_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2947_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2947_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
else
{
lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2957_ = l_Lean_Syntax_getArg(v_a_2931_, v___x_2366_);
lean_dec(v___x_2366_);
v___x_2958_ = l_Lean_Syntax_getArg(v_a_2931_, v___x_2363_);
v___x_2959_ = l_Lean_Syntax_isNone(v___x_2958_);
if (v___x_2959_ == 0)
{
uint8_t v___x_2960_; 
lean_inc(v___x_2958_);
v___x_2960_ = l_Lean_Syntax_matchesNull(v___x_2958_, v___x_2364_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_inc(v_ref_2440_);
lean_dec(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec(v___x_2944_);
lean_dec(v_a_2931_);
lean_dec(v___y_2927_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
v___x_2961_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2962_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2961_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___y_2390_ = v___y_2925_;
v_stx_2391_ = v_a_2963_;
v___y_2392_ = v___y_2382_;
v_ref_2393_ = v_ref_2440_;
v___y_2394_ = v___y_2383_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref(v___y_2925_);
lean_dec(v_ref_2440_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v_tk_2351_);
v_a_2964_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2962_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2962_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = l_Lean_Syntax_getArg(v___x_2958_, v___x_2355_);
lean_dec(v___x_2958_);
v___x_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
v___y_2890_ = v___x_2944_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___x_2957_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v___y_2925_;
v___y_2895_ = v_a_2931_;
v_only_2896_ = v___x_2973_;
v___y_2897_ = v___y_2376_;
v___y_2898_ = v___y_2377_;
v___y_2899_ = v___y_2378_;
v___y_2900_ = v___y_2379_;
v___y_2901_ = v___y_2380_;
v___y_2902_ = v___y_2381_;
v___y_2903_ = v___y_2382_;
v___y_2904_ = v___y_2383_;
goto v___jp_2889_;
}
}
else
{
lean_object* v___x_2974_; 
lean_dec(v___x_2958_);
v___x_2974_ = lean_box(0);
v___y_2890_ = v___x_2944_;
v___y_2891_ = v___y_2924_;
v___y_2892_ = v___x_2957_;
v___y_2893_ = v___y_2927_;
v___y_2894_ = v___y_2925_;
v___y_2895_ = v_a_2931_;
v_only_2896_ = v___x_2974_;
v___y_2897_ = v___y_2376_;
v___y_2898_ = v___y_2377_;
v___y_2899_ = v___y_2378_;
v___y_2900_ = v___y_2379_;
v___y_2901_ = v___y_2380_;
v___y_2902_ = v___y_2381_;
v___y_2903_ = v___y_2382_;
v___y_2904_ = v___y_2383_;
goto v___jp_2889_;
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2925_);
lean_dec(v___x_2444_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___x_2366_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v_a_2975_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2930_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2930_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
v___jp_2983_:
{
if (lean_obj_tag(v_usingArg_2367_) == 0)
{
v___y_2924_ = v___y_2984_;
v___y_2925_ = v___y_2985_;
v___y_2926_ = v___y_2986_;
v___y_2927_ = v_usingArg_2367_;
goto v___jp_2923_;
}
else
{
lean_object* v_val_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2995_; 
v_val_2987_ = lean_ctor_get(v_usingArg_2367_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_usingArg_2367_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2989_ = v_usingArg_2367_;
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_val_2987_);
lean_dec(v_usingArg_2367_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2995_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = l_Lean_Syntax_unsetTrailing(v_val_2987_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2991_);
v___x_2993_ = v___x_2989_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
v___y_2924_ = v___y_2984_;
v___y_2925_ = v___y_2985_;
v___y_2926_ = v___y_2986_;
v___y_2927_ = v___x_2993_;
goto v___jp_2923_;
}
}
}
}
v___jp_2996_:
{
if (v___y_3000_ == 0)
{
lean_dec(v___y_2999_);
lean_dec(v___x_2444_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_usingArg_2367_);
lean_dec(v___x_2366_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v___y_2386_ = v___y_2998_;
goto v___jp_2385_;
}
else
{
v___y_2984_ = v___y_2997_;
v___y_2985_ = v___y_2998_;
v___y_2986_ = v___y_2999_;
goto v___jp_2983_;
}
}
v___jp_3001_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___f_3012_; lean_object* v___x_3013_; 
v___x_3007_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3006_, v___x_2441_);
v___x_3008_ = lean_box(v___x_2356_);
v___x_3009_ = lean_box(v___x_2441_);
v___x_3010_ = lean_box(v_useReducible_2359_);
v___x_3011_ = lean_box(v___x_2369_);
lean_inc(v___x_2364_);
lean_inc_ref(v___x_2361_);
lean_inc(v_usingArg_2367_);
lean_inc(v___x_2355_);
lean_inc(v_tk_2351_);
lean_inc(v___x_2366_);
v___f_3012_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 24, 14);
lean_closure_set(v___f_3012_, 0, v___x_2366_);
lean_closure_set(v___f_3012_, 1, v_tk_2351_);
lean_closure_set(v___f_3012_, 2, v___x_2446_);
lean_closure_set(v___f_3012_, 3, v___x_2355_);
lean_closure_set(v___f_3012_, 4, v___x_3007_);
lean_closure_set(v___f_3012_, 5, v___y_3002_);
lean_closure_set(v___f_3012_, 6, v___x_3008_);
lean_closure_set(v___f_3012_, 7, v_usingArg_2367_);
lean_closure_set(v___f_3012_, 8, v___x_3009_);
lean_closure_set(v___f_3012_, 9, v___x_2361_);
lean_closure_set(v___f_3012_, 10, v___x_3010_);
lean_closure_set(v___f_3012_, 11, v___x_3011_);
lean_closure_set(v___f_3012_, 12, v___x_2364_);
lean_closure_set(v___f_3012_, 13, v_usingTk_x3f_2370_);
v___x_3013_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3004_, v___f_3012_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_3004_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3016_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_2439_, v___x_3015_);
if (v___x_3016_ == 0)
{
if (lean_obj_tag(v_squeeze_2371_) == 0)
{
v___y_2997_ = v___y_3003_;
v___y_2998_ = v_a_3014_;
v___y_2999_ = v___y_3005_;
v___y_3000_ = v___x_3016_;
goto v___jp_2996_;
}
else
{
v___y_2997_ = v___y_3003_;
v___y_2998_ = v_a_3014_;
v___y_2999_ = v___y_3005_;
v___y_3000_ = v___x_2369_;
goto v___jp_2996_;
}
}
else
{
v___y_2984_ = v___y_3003_;
v___y_2985_ = v_a_3014_;
v___y_2986_ = v___y_3005_;
goto v___jp_2983_;
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v___y_3005_);
lean_dec(v___x_2444_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_usingArg_2367_);
lean_dec(v___x_2366_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v_a_3017_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3013_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3013_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
v___jp_3025_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3029_ = l_Array_append___redArg(v___x_2447_, v___y_3028_);
lean_dec_ref(v___y_3028_);
lean_inc_n(v___x_2442_, 2);
v___x_3030_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3030_, 0, v___x_2442_);
lean_ctor_set(v___x_3030_, 1, v___x_2446_);
lean_ctor_set(v___x_3030_, 2, v___x_3029_);
v___x_3031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3031_, 0, v___x_2442_);
lean_ctor_set(v___x_3031_, 1, v___x_2446_);
lean_ctor_set(v___x_3031_, 2, v___x_2447_);
lean_inc(v___x_2444_);
v___x_3032_ = l_Lean_Syntax_node6(v___x_2442_, v___x_2444_, v___x_2445_, v___x_2368_, v___y_3027_, v___y_3026_, v___x_3030_, v___x_3031_);
v___x_3033_ = 0;
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23));
v___x_3035_ = lean_box(v___x_2441_);
v___x_3036_ = lean_box(v___x_3033_);
v___x_3037_ = lean_box(v___x_2441_);
lean_inc(v___x_3032_);
v___x_3038_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3038_, 0, v___x_3032_);
lean_closure_set(v___x_3038_, 1, v___x_3035_);
lean_closure_set(v___x_3038_, 2, v___x_3036_);
lean_closure_set(v___x_3038_, 3, v___x_3037_);
lean_closure_set(v___x_3038_, 4, v___x_3034_);
v___x_3039_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3038_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
if (lean_obj_tag(v_unfold_2372_) == 0)
{
lean_object* v_ctx_3041_; lean_object* v_simprocs_3042_; lean_object* v_dischargeWrapper_3043_; 
v_ctx_3041_ = lean_ctor_get(v_a_3040_, 0);
lean_inc_ref(v_ctx_3041_);
v_simprocs_3042_ = lean_ctor_get(v_a_3040_, 1);
lean_inc_ref(v_simprocs_3042_);
v_dischargeWrapper_3043_ = lean_ctor_get(v_a_3040_, 2);
lean_inc(v_dischargeWrapper_3043_);
lean_dec(v_a_3040_);
v___y_3002_ = v_simprocs_3042_;
v___y_3003_ = v___x_2441_;
v___y_3004_ = v_dischargeWrapper_3043_;
v___y_3005_ = v___x_3032_;
v___y_3006_ = v_ctx_3041_;
goto v___jp_3001_;
}
else
{
if (v___x_2369_ == 0)
{
lean_object* v_ctx_3044_; lean_object* v_simprocs_3045_; lean_object* v_dischargeWrapper_3046_; 
v_ctx_3044_ = lean_ctor_get(v_a_3040_, 0);
lean_inc_ref(v_ctx_3044_);
v_simprocs_3045_ = lean_ctor_get(v_a_3040_, 1);
lean_inc_ref(v_simprocs_3045_);
v_dischargeWrapper_3046_ = lean_ctor_get(v_a_3040_, 2);
lean_inc(v_dischargeWrapper_3046_);
lean_dec(v_a_3040_);
v___y_3002_ = v_simprocs_3045_;
v___y_3003_ = v___x_2369_;
v___y_3004_ = v_dischargeWrapper_3046_;
v___y_3005_ = v___x_3032_;
v___y_3006_ = v_ctx_3044_;
goto v___jp_3001_;
}
else
{
lean_object* v_ctx_3047_; lean_object* v_simprocs_3048_; lean_object* v_dischargeWrapper_3049_; lean_object* v___x_3050_; 
v_ctx_3047_ = lean_ctor_get(v_a_3040_, 0);
lean_inc_ref(v_ctx_3047_);
v_simprocs_3048_ = lean_ctor_get(v_a_3040_, 1);
lean_inc_ref(v_simprocs_3048_);
v_dischargeWrapper_3049_ = lean_ctor_get(v_a_3040_, 2);
lean_inc(v_dischargeWrapper_3049_);
lean_dec(v_a_3040_);
v___x_3050_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3047_);
v___y_3002_ = v_simprocs_3048_;
v___y_3003_ = v___x_2369_;
v___y_3004_ = v_dischargeWrapper_3049_;
v___y_3005_ = v___x_3032_;
v___y_3006_ = v___x_3050_;
goto v___jp_3001_;
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec(v___x_3032_);
lean_dec(v___x_2444_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_usingTk_x3f_2370_);
lean_dec(v_usingArg_2367_);
lean_dec(v___x_2366_);
lean_dec(v___x_2364_);
lean_dec_ref(v___x_2361_);
lean_dec_ref(v___f_2360_);
lean_dec(v___x_2358_);
lean_dec(v___x_2357_);
lean_dec(v___x_2355_);
lean_dec_ref(v___x_2354_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___x_2352_);
lean_dec(v_tk_2351_);
v_a_3051_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3039_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3039_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
v___jp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = l_Array_append___redArg(v___x_2447_, v___y_3061_);
lean_dec_ref(v___y_3061_);
lean_inc(v___x_2442_);
v___x_3063_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3063_, 0, v___x_2442_);
lean_ctor_set(v___x_3063_, 1, v___x_2446_);
lean_ctor_set(v___x_3063_, 2, v___x_3062_);
if (lean_obj_tag(v_args_2373_) == 1)
{
lean_object* v_val_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_val_3064_ = lean_ctor_get(v_args_2373_, 0);
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___x_2442_, 3);
v___x_3066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_2442_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Array_append___redArg(v___x_2447_, v_val_3064_);
v___x_3068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3068_, 0, v___x_2442_);
lean_ctor_set(v___x_3068_, 1, v___x_2446_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
v___x_3069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_2442_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = l_Array_mkArray3___redArg(v___x_3066_, v___x_3068_, v___x_3070_);
v___y_3026_ = v___x_3063_;
v___y_3027_ = v___y_3060_;
v___y_3028_ = v___x_3071_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_3026_ = v___x_3063_;
v___y_3027_ = v___y_3060_;
v___y_3028_ = v___x_3072_;
goto v___jp_3025_;
}
}
v___jp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = l_Array_append___redArg(v___x_2447_, v___y_3074_);
lean_dec_ref(v___y_3074_);
lean_inc(v___x_2442_);
v___x_3076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3076_, 0, v___x_2442_);
lean_ctor_set(v___x_3076_, 1, v___x_2446_);
lean_ctor_set(v___x_3076_, 2, v___x_3075_);
if (lean_obj_tag(v_only_2374_) == 1)
{
lean_object* v_val_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v_val_3077_ = lean_ctor_get(v_only_2374_, 0);
v___x_3078_ = l_Lean_SourceInfo_fromRef(v_val_3077_, v___x_2356_);
v___x_3079_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Array_mkArray1___redArg(v___x_3080_);
v___y_3060_ = v___x_3076_;
v___y_3061_ = v___x_3081_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___y_3060_ = v___x_3076_;
v___y_3061_ = v___x_3082_;
goto v___jp_3059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v_tk_3087_ = _args[0];
lean_object* v___x_3088_ = _args[1];
lean_object* v___x_3089_ = _args[2];
lean_object* v___x_3090_ = _args[3];
lean_object* v___x_3091_ = _args[4];
lean_object* v___x_3092_ = _args[5];
lean_object* v___x_3093_ = _args[6];
lean_object* v___x_3094_ = _args[7];
lean_object* v_useReducible_3095_ = _args[8];
lean_object* v___f_3096_ = _args[9];
lean_object* v___x_3097_ = _args[10];
lean_object* v___x_3098_ = _args[11];
lean_object* v___x_3099_ = _args[12];
lean_object* v___x_3100_ = _args[13];
lean_object* v___x_3101_ = _args[14];
lean_object* v___x_3102_ = _args[15];
lean_object* v_usingArg_3103_ = _args[16];
lean_object* v___x_3104_ = _args[17];
lean_object* v___x_3105_ = _args[18];
lean_object* v_usingTk_x3f_3106_ = _args[19];
lean_object* v_squeeze_3107_ = _args[20];
lean_object* v_unfold_3108_ = _args[21];
lean_object* v_args_3109_ = _args[22];
lean_object* v_only_3110_ = _args[23];
lean_object* v___y_3111_ = _args[24];
lean_object* v___y_3112_ = _args[25];
lean_object* v___y_3113_ = _args[26];
lean_object* v___y_3114_ = _args[27];
lean_object* v___y_3115_ = _args[28];
lean_object* v___y_3116_ = _args[29];
lean_object* v___y_3117_ = _args[30];
lean_object* v___y_3118_ = _args[31];
lean_object* v___y_3119_ = _args[32];
lean_object* v___y_3120_ = _args[33];
_start:
{
uint8_t v___x_96914__boxed_3121_; uint8_t v_useReducible_boxed_3122_; uint8_t v___x_96925__boxed_3123_; lean_object* v_res_3124_; 
v___x_96914__boxed_3121_ = lean_unbox(v___x_3092_);
v_useReducible_boxed_3122_ = lean_unbox(v_useReducible_3095_);
v___x_96925__boxed_3123_ = lean_unbox(v___x_3105_);
v_res_3124_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3087_, v___x_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_96914__boxed_3121_, v___x_3093_, v___x_3094_, v_useReducible_boxed_3122_, v___f_3096_, v___x_3097_, v___x_3098_, v___x_3099_, v___x_3100_, v___x_3101_, v___x_3102_, v_usingArg_3103_, v___x_3104_, v___x_96925__boxed_3123_, v_usingTk_x3f_3106_, v_squeeze_3107_, v_unfold_3108_, v_args_3109_, v_only_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v_only_3110_);
lean_dec(v_args_3109_);
lean_dec(v_unfold_3108_);
lean_dec(v_squeeze_3107_);
lean_dec(v___x_3101_);
lean_dec(v___x_3099_);
lean_dec(v___x_3098_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3151_, lean_object* v_stx_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3162_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3164_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_3165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
lean_inc(v_stx_3152_);
v___x_3167_ = l_Lean_Syntax_isOfKind(v_stx_3152_, v___x_3166_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; 
lean_dec(v_stx_3152_);
v___x_3168_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3168_;
}
else
{
lean_object* v___f_3169_; lean_object* v___x_3170_; lean_object* v_tk_3171_; lean_object* v___x_3172_; lean_object* v___y_3174_; uint8_t v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3203_; uint8_t v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v_usingTk_x3f_3223_; lean_object* v_usingArg_3224_; lean_object* v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v_args_3256_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v_only_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v_unfold_3312_; lean_object* v_squeeze_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___f_3169_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3170_ = lean_unsigned_to_nat(0u);
v_tk_3171_ = l_Lean_Syntax_getArg(v_stx_3152_, v___x_3170_);
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3348_ = l_Lean_Syntax_getArg(v_stx_3152_, v___x_3172_);
v___x_3349_ = l_Lean_Syntax_isNone(v___x_3348_);
if (v___x_3349_ == 0)
{
uint8_t v___x_3350_; 
lean_inc(v___x_3348_);
v___x_3350_ = l_Lean_Syntax_matchesNull(v___x_3348_, v___x_3172_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; 
lean_dec(v___x_3348_);
lean_dec(v_tk_3171_);
lean_dec(v_stx_3152_);
v___x_3351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3351_;
}
else
{
lean_object* v_squeeze_3352_; lean_object* v___x_3353_; 
v_squeeze_3352_ = l_Lean_Syntax_getArg(v___x_3348_, v___x_3170_);
lean_dec(v___x_3348_);
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_squeeze_3352_);
v_squeeze_3331_ = v___x_3353_;
v___y_3332_ = v_a_3153_;
v___y_3333_ = v_a_3154_;
v___y_3334_ = v_a_3155_;
v___y_3335_ = v_a_3156_;
v___y_3336_ = v_a_3157_;
v___y_3337_ = v_a_3158_;
v___y_3338_ = v_a_3159_;
v___y_3339_ = v_a_3160_;
goto v___jp_3330_;
}
}
else
{
lean_object* v___x_3354_; 
lean_dec(v___x_3348_);
v___x_3354_ = lean_box(0);
v_squeeze_3331_ = v___x_3354_;
v___y_3332_ = v_a_3153_;
v___y_3333_ = v_a_3154_;
v___y_3334_ = v_a_3155_;
v___y_3335_ = v_a_3156_;
v___y_3336_ = v_a_3157_;
v___y_3337_ = v_a_3158_;
v___y_3338_ = v_a_3159_;
v___y_3339_ = v_a_3160_;
goto v___jp_3330_;
}
v___jp_3173_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___f_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3196_ = lean_box(v___x_3167_);
v___x_3197_ = lean_box(v_useReducible_3151_);
v___x_3198_ = lean_box(v___y_3175_);
lean_inc(v___y_3191_);
lean_inc(v___y_3178_);
v___f_3199_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3199_, 0, v_tk_3171_);
lean_closure_set(v___f_3199_, 1, v___x_3162_);
lean_closure_set(v___f_3199_, 2, v___x_3163_);
lean_closure_set(v___f_3199_, 3, v___x_3164_);
lean_closure_set(v___f_3199_, 4, v___x_3170_);
lean_closure_set(v___f_3199_, 5, v___x_3196_);
lean_closure_set(v___f_3199_, 6, v___y_3178_);
lean_closure_set(v___f_3199_, 7, v___x_3166_);
lean_closure_set(v___f_3199_, 8, v___x_3197_);
lean_closure_set(v___f_3199_, 9, v___f_3169_);
lean_closure_set(v___f_3199_, 10, v___x_3165_);
lean_closure_set(v___f_3199_, 11, v___y_3184_);
lean_closure_set(v___f_3199_, 12, v___y_3193_);
lean_closure_set(v___f_3199_, 13, v___x_3172_);
lean_closure_set(v___f_3199_, 14, v___y_3191_);
lean_closure_set(v___f_3199_, 15, v___y_3188_);
lean_closure_set(v___f_3199_, 16, v___y_3187_);
lean_closure_set(v___f_3199_, 17, v___y_3179_);
lean_closure_set(v___f_3199_, 18, v___x_3198_);
lean_closure_set(v___f_3199_, 19, v___y_3189_);
lean_closure_set(v___f_3199_, 20, v___y_3185_);
lean_closure_set(v___f_3199_, 21, v___y_3180_);
lean_closure_set(v___f_3199_, 22, v___y_3192_);
lean_closure_set(v___f_3199_, 23, v___y_3182_);
lean_closure_set(v___f_3199_, 24, v___y_3195_);
v___x_3200_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3200_, 0, v___f_3199_);
v___x_3201_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3200_, v___y_3194_, v___y_3186_, v___y_3181_, v___y_3183_, v___y_3190_, v___y_3176_, v___y_3174_, v___y_3177_);
return v___x_3201_;
}
v___jp_3202_:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Syntax_getOptional_x3f(v___y_3206_);
lean_dec(v___y_3206_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_box(0);
v___y_3174_ = v___y_3203_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v___y_3205_;
v___y_3177_ = v___y_3207_;
v___y_3178_ = v___y_3208_;
v___y_3179_ = v___y_3209_;
v___y_3180_ = v___y_3210_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v___y_3212_;
v___y_3183_ = v___y_3213_;
v___y_3184_ = v___y_3214_;
v___y_3185_ = v___y_3215_;
v___y_3186_ = v___y_3216_;
v___y_3187_ = v_usingArg_3224_;
v___y_3188_ = v___y_3217_;
v___y_3189_ = v_usingTk_x3f_3223_;
v___y_3190_ = v___y_3220_;
v___y_3191_ = v___y_3219_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3221_;
v___y_3194_ = v___y_3222_;
v___y_3195_ = v___x_3226_;
goto v___jp_3173_;
}
else
{
lean_object* v_val_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
v_val_3227_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3225_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_val_3227_);
lean_dec(v___x_3225_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_val_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
v___y_3174_ = v___y_3203_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v___y_3205_;
v___y_3177_ = v___y_3207_;
v___y_3178_ = v___y_3208_;
v___y_3179_ = v___y_3209_;
v___y_3180_ = v___y_3210_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v___y_3212_;
v___y_3183_ = v___y_3213_;
v___y_3184_ = v___y_3214_;
v___y_3185_ = v___y_3215_;
v___y_3186_ = v___y_3216_;
v___y_3187_ = v_usingArg_3224_;
v___y_3188_ = v___y_3217_;
v___y_3189_ = v_usingTk_x3f_3223_;
v___y_3190_ = v___y_3220_;
v___y_3191_ = v___y_3219_;
v___y_3192_ = v___y_3218_;
v___y_3193_ = v___y_3221_;
v___y_3194_ = v___y_3222_;
v___y_3195_ = v___x_3232_;
goto v___jp_3173_;
}
}
}
}
v___jp_3235_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3257_ = lean_unsigned_to_nat(4u);
v___x_3258_ = l_Lean_Syntax_getArg(v___y_3236_, v___x_3257_);
lean_dec(v___y_3236_);
v___x_3259_ = l_Lean_Syntax_isNone(v___x_3258_);
if (v___x_3259_ == 0)
{
uint8_t v___x_3260_; 
lean_inc(v___x_3258_);
v___x_3260_ = l_Lean_Syntax_matchesNull(v___x_3258_, v___y_3240_);
lean_dec(v___y_3240_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
lean_dec(v___x_3258_);
lean_dec(v_args_3256_);
lean_dec(v___y_3254_);
lean_dec(v___y_3251_);
lean_dec(v___y_3249_);
lean_dec(v___y_3247_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec(v___y_3241_);
lean_dec(v_tk_3171_);
v___x_3261_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3261_;
}
else
{
lean_object* v_usingTk_x3f_3262_; lean_object* v_usingArg_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_usingTk_x3f_3262_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_3170_);
v_usingArg_3263_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_3172_);
lean_dec(v___x_3258_);
v___x_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_usingTk_x3f_3262_);
v___x_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_usingArg_3263_);
v___y_3203_ = v___y_3237_;
v___y_3204_ = v___y_3238_;
v___y_3205_ = v___y_3239_;
v___y_3206_ = v___y_3241_;
v___y_3207_ = v___y_3242_;
v___y_3208_ = v___y_3243_;
v___y_3209_ = v___y_3244_;
v___y_3210_ = v___y_3245_;
v___y_3211_ = v___y_3246_;
v___y_3212_ = v___y_3247_;
v___y_3213_ = v___y_3248_;
v___y_3214_ = v___x_3257_;
v___y_3215_ = v___y_3249_;
v___y_3216_ = v___y_3250_;
v___y_3217_ = v___y_3251_;
v___y_3218_ = v_args_3256_;
v___y_3219_ = v___y_3253_;
v___y_3220_ = v___y_3252_;
v___y_3221_ = v___y_3254_;
v___y_3222_ = v___y_3255_;
v_usingTk_x3f_3223_ = v___x_3264_;
v_usingArg_3224_ = v___x_3265_;
goto v___jp_3202_;
}
}
else
{
lean_object* v___x_3266_; 
lean_dec(v___x_3258_);
lean_dec(v___y_3240_);
v___x_3266_ = lean_box(0);
v___y_3203_ = v___y_3237_;
v___y_3204_ = v___y_3238_;
v___y_3205_ = v___y_3239_;
v___y_3206_ = v___y_3241_;
v___y_3207_ = v___y_3242_;
v___y_3208_ = v___y_3243_;
v___y_3209_ = v___y_3244_;
v___y_3210_ = v___y_3245_;
v___y_3211_ = v___y_3246_;
v___y_3212_ = v___y_3247_;
v___y_3213_ = v___y_3248_;
v___y_3214_ = v___x_3257_;
v___y_3215_ = v___y_3249_;
v___y_3216_ = v___y_3250_;
v___y_3217_ = v___y_3251_;
v___y_3218_ = v_args_3256_;
v___y_3219_ = v___y_3253_;
v___y_3220_ = v___y_3252_;
v___y_3221_ = v___y_3254_;
v___y_3222_ = v___y_3255_;
v_usingTk_x3f_3223_ = v___x_3266_;
v_usingArg_3224_ = v___x_3266_;
goto v___jp_3202_;
}
}
v___jp_3267_:
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = l_Lean_Syntax_getArg(v___y_3276_, v___y_3278_);
lean_dec(v___y_3278_);
v___x_3290_ = l_Lean_Syntax_isNone(v___x_3289_);
if (v___x_3290_ == 0)
{
uint8_t v___x_3291_; 
lean_inc(v___x_3289_);
v___x_3291_ = l_Lean_Syntax_matchesNull(v___x_3289_, v___x_3172_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; 
lean_dec(v___x_3289_);
lean_dec(v_only_3280_);
lean_dec(v___y_3279_);
lean_dec(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v_tk_3171_);
v___x_3292_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3292_;
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; 
v___x_3293_ = l_Lean_Syntax_getArg(v___x_3289_, v___x_3170_);
lean_dec(v___x_3289_);
v___x_3294_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
lean_inc(v___x_3293_);
v___x_3295_ = l_Lean_Syntax_isOfKind(v___x_3293_, v___x_3294_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; 
lean_dec(v___x_3293_);
lean_dec(v_only_3280_);
lean_dec(v___y_3279_);
lean_dec(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v_tk_3171_);
v___x_3296_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3296_;
}
else
{
lean_object* v___x_3297_; lean_object* v_args_3298_; lean_object* v___x_3299_; 
v___x_3297_ = l_Lean_Syntax_getArg(v___x_3293_, v___x_3172_);
lean_dec(v___x_3293_);
v_args_3298_ = l_Lean_Syntax_getArgs(v___x_3297_);
lean_dec(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_args_3298_);
v___y_3236_ = v___y_3276_;
v___y_3237_ = v___y_3287_;
v___y_3238_ = v___y_3268_;
v___y_3239_ = v___y_3286_;
v___y_3240_ = v___y_3277_;
v___y_3241_ = v___y_3279_;
v___y_3242_ = v___y_3288_;
v___y_3243_ = v___y_3273_;
v___y_3244_ = v___y_3272_;
v___y_3245_ = v___y_3271_;
v___y_3246_ = v___y_3283_;
v___y_3247_ = v_only_3280_;
v___y_3248_ = v___y_3284_;
v___y_3249_ = v___y_3269_;
v___y_3250_ = v___y_3282_;
v___y_3251_ = v___y_3270_;
v___y_3252_ = v___y_3285_;
v___y_3253_ = v___y_3274_;
v___y_3254_ = v___y_3275_;
v___y_3255_ = v___y_3281_;
v_args_3256_ = v___x_3299_;
goto v___jp_3235_;
}
}
}
else
{
lean_object* v___x_3300_; 
lean_dec(v___x_3289_);
v___x_3300_ = lean_box(0);
v___y_3236_ = v___y_3276_;
v___y_3237_ = v___y_3287_;
v___y_3238_ = v___y_3268_;
v___y_3239_ = v___y_3286_;
v___y_3240_ = v___y_3277_;
v___y_3241_ = v___y_3279_;
v___y_3242_ = v___y_3288_;
v___y_3243_ = v___y_3273_;
v___y_3244_ = v___y_3272_;
v___y_3245_ = v___y_3271_;
v___y_3246_ = v___y_3283_;
v___y_3247_ = v_only_3280_;
v___y_3248_ = v___y_3284_;
v___y_3249_ = v___y_3269_;
v___y_3250_ = v___y_3282_;
v___y_3251_ = v___y_3270_;
v___y_3252_ = v___y_3285_;
v___y_3253_ = v___y_3274_;
v___y_3254_ = v___y_3275_;
v___y_3255_ = v___y_3281_;
v_args_3256_ = v___x_3300_;
goto v___jp_3235_;
}
}
v___jp_3301_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3313_ = lean_unsigned_to_nat(3u);
v___x_3314_ = l_Lean_Syntax_getArg(v_stx_3152_, v___x_3313_);
lean_dec(v_stx_3152_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7));
lean_inc(v___x_3314_);
v___x_3316_ = l_Lean_Syntax_isOfKind(v___x_3314_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; 
lean_dec(v___x_3314_);
lean_dec(v_unfold_3312_);
lean_dec(v___y_3308_);
lean_dec(v___y_3306_);
lean_dec(v_tk_3171_);
v___x_3317_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3317_;
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3318_ = l_Lean_Syntax_getArg(v___x_3314_, v___x_3170_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9));
lean_inc(v___x_3318_);
v___x_3320_ = l_Lean_Syntax_isOfKind(v___x_3318_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_dec(v___x_3318_);
lean_dec(v___x_3314_);
lean_dec(v_unfold_3312_);
lean_dec(v___y_3308_);
lean_dec(v___y_3306_);
lean_dec(v_tk_3171_);
v___x_3321_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3321_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3322_ = l_Lean_Syntax_getArg(v___x_3314_, v___x_3172_);
v___x_3323_ = l_Lean_Syntax_getArg(v___x_3314_, v___y_3308_);
v___x_3324_ = l_Lean_Syntax_isNone(v___x_3323_);
if (v___x_3324_ == 0)
{
uint8_t v___x_3325_; 
lean_inc(v___x_3323_);
v___x_3325_ = l_Lean_Syntax_matchesNull(v___x_3323_, v___x_3172_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_dec(v___x_3323_);
lean_dec(v___x_3322_);
lean_dec(v___x_3318_);
lean_dec(v___x_3314_);
lean_dec(v_unfold_3312_);
lean_dec(v___y_3308_);
lean_dec(v___y_3306_);
lean_dec(v_tk_3171_);
v___x_3326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3326_;
}
else
{
lean_object* v_only_3327_; lean_object* v___x_3328_; 
v_only_3327_ = l_Lean_Syntax_getArg(v___x_3323_, v___x_3170_);
lean_dec(v___x_3323_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_only_3327_);
lean_inc(v___y_3308_);
v___y_3268_ = v___x_3320_;
v___y_3269_ = v___y_3306_;
v___y_3270_ = v___y_3308_;
v___y_3271_ = v_unfold_3312_;
v___y_3272_ = v___x_3318_;
v___y_3273_ = v___x_3315_;
v___y_3274_ = v___x_3319_;
v___y_3275_ = v___x_3313_;
v___y_3276_ = v___x_3314_;
v___y_3277_ = v___y_3308_;
v___y_3278_ = v___x_3313_;
v___y_3279_ = v___x_3322_;
v_only_3280_ = v___x_3328_;
v___y_3281_ = v___y_3302_;
v___y_3282_ = v___y_3310_;
v___y_3283_ = v___y_3304_;
v___y_3284_ = v___y_3309_;
v___y_3285_ = v___y_3307_;
v___y_3286_ = v___y_3311_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___y_3305_;
goto v___jp_3267_;
}
}
else
{
lean_object* v___x_3329_; 
lean_dec(v___x_3323_);
v___x_3329_ = lean_box(0);
lean_inc(v___y_3308_);
v___y_3268_ = v___x_3320_;
v___y_3269_ = v___y_3306_;
v___y_3270_ = v___y_3308_;
v___y_3271_ = v_unfold_3312_;
v___y_3272_ = v___x_3318_;
v___y_3273_ = v___x_3315_;
v___y_3274_ = v___x_3319_;
v___y_3275_ = v___x_3313_;
v___y_3276_ = v___x_3314_;
v___y_3277_ = v___y_3308_;
v___y_3278_ = v___x_3313_;
v___y_3279_ = v___x_3322_;
v_only_3280_ = v___x_3329_;
v___y_3281_ = v___y_3302_;
v___y_3282_ = v___y_3310_;
v___y_3283_ = v___y_3304_;
v___y_3284_ = v___y_3309_;
v___y_3285_ = v___y_3307_;
v___y_3286_ = v___y_3311_;
v___y_3287_ = v___y_3303_;
v___y_3288_ = v___y_3305_;
goto v___jp_3267_;
}
}
}
}
v___jp_3330_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3340_ = lean_unsigned_to_nat(2u);
v___x_3341_ = l_Lean_Syntax_getArg(v_stx_3152_, v___x_3340_);
v___x_3342_ = l_Lean_Syntax_isNone(v___x_3341_);
if (v___x_3342_ == 0)
{
uint8_t v___x_3343_; 
lean_inc(v___x_3341_);
v___x_3343_ = l_Lean_Syntax_matchesNull(v___x_3341_, v___x_3172_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; 
lean_dec(v___x_3341_);
lean_dec(v_squeeze_3331_);
lean_dec(v_tk_3171_);
lean_dec(v_stx_3152_);
v___x_3344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3344_;
}
else
{
lean_object* v_unfold_3345_; lean_object* v___x_3346_; 
v_unfold_3345_ = l_Lean_Syntax_getArg(v___x_3341_, v___x_3170_);
lean_dec(v___x_3341_);
v___x_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_unfold_3345_);
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3338_;
v___y_3304_ = v___y_3334_;
v___y_3305_ = v___y_3339_;
v___y_3306_ = v_squeeze_3331_;
v___y_3307_ = v___y_3336_;
v___y_3308_ = v___x_3340_;
v___y_3309_ = v___y_3335_;
v___y_3310_ = v___y_3333_;
v___y_3311_ = v___y_3337_;
v_unfold_3312_ = v___x_3346_;
goto v___jp_3301_;
}
}
else
{
lean_object* v___x_3347_; 
lean_dec(v___x_3341_);
v___x_3347_ = lean_box(0);
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3338_;
v___y_3304_ = v___y_3334_;
v___y_3305_ = v___y_3339_;
v___y_3306_ = v_squeeze_3331_;
v___y_3307_ = v___y_3336_;
v___y_3308_ = v___x_3340_;
v___y_3309_ = v___y_3335_;
v___y_3310_ = v___y_3333_;
v___y_3311_ = v___y_3337_;
v_unfold_3312_ = v___x_3347_;
goto v___jp_3301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3355_, lean_object* v_stx_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
uint8_t v_useReducible_boxed_3366_; lean_object* v_res_3367_; 
v_useReducible_boxed_3366_ = lean_unbox(v_useReducible_3355_);
v_res_3367_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3366_, v_stx_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3368_, lean_object* v_val_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3368_, v_val_3369_, v___y_3375_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3380_, lean_object* v_val_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3380_, v_val_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3392_, v___y_3400_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v_00_u03b1_3414_, lean_object* v_msg_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_3415_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v_00_u03b1_3426_, lean_object* v_msg_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_3426_, v_msg_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_00_u03b1_3438_, lean_object* v_x_3439_, lean_object* v_mkInfoTree_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_3439_, v_mkInfoTree_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_00_u03b1_3451_, lean_object* v_x_3452_, lean_object* v_mkInfoTree_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_3451_, v_x_3452_, v_mkInfoTree_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3464_, lean_object* v_x_3465_, lean_object* v_x_3466_, lean_object* v_x_3467_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3465_, v_x_3466_, v_x_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3469_, lean_object* v_m_3470_, lean_object* v_a_3471_){
_start:
{
uint8_t v___x_3472_; 
v___x_3472_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3470_, v_a_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3473_, lean_object* v_m_3474_, lean_object* v_a_3475_){
_start:
{
uint8_t v_res_3476_; lean_object* v_r_3477_; 
v_res_3476_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_3473_, v_m_3474_, v_a_3475_);
lean_dec_ref(v_a_3475_);
lean_dec_ref(v_m_3474_);
v_r_3477_ = lean_box(v_res_3476_);
return v_r_3477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3478_, lean_object* v_m_3479_, lean_object* v_a_3480_, lean_object* v_b_3481_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_m_3479_, v_a_3480_, v_b_3481_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3483_, v___y_3484_, v___y_3490_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(v_mvarId_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v_mvarId_3495_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3507_, v___y_3508_, v___y_3514_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_mvarId_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v_mvarId_3519_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3531_, lean_object* v_x_3532_, size_t v_x_3533_, size_t v_x_3534_, lean_object* v_x_3535_, lean_object* v_x_3536_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_3532_, v_x_3533_, v_x_3534_, v_x_3535_, v_x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_, lean_object* v_x_3542_, lean_object* v_x_3543_){
_start:
{
size_t v_x_99129__boxed_3544_; size_t v_x_99130__boxed_3545_; lean_object* v_res_3546_; 
v_x_99129__boxed_3544_ = lean_unbox_usize(v_x_3540_);
lean_dec(v_x_3540_);
v_x_99130__boxed_3545_ = lean_unbox_usize(v_x_3541_);
lean_dec(v_x_3541_);
v_res_3546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_3538_, v_x_3539_, v_x_99129__boxed_3544_, v_x_99130__boxed_3545_, v_x_3542_, v_x_3543_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(lean_object* v_ref_3547_, lean_object* v_msgData_3548_, uint8_t v_severity_3549_, uint8_t v_isSilent_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_3547_, v_msgData_3548_, v_severity_3549_, v_isSilent_3550_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3561_, lean_object* v_msgData_3562_, lean_object* v_severity_3563_, lean_object* v_isSilent_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
uint8_t v_severity_boxed_3574_; uint8_t v_isSilent_boxed_3575_; lean_object* v_res_3576_; 
v_severity_boxed_3574_ = lean_unbox(v_severity_3563_);
v_isSilent_boxed_3575_ = lean_unbox(v_isSilent_3564_);
v_res_3576_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(v_ref_3561_, v_msgData_3562_, v_severity_boxed_3574_, v_isSilent_boxed_3575_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v_ref_3561_);
return v_res_3576_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3577_, lean_object* v_a_3578_, lean_object* v_x_3579_){
_start:
{
uint8_t v___x_3580_; 
v___x_3580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3578_, v_x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3581_, lean_object* v_a_3582_, lean_object* v_x_3583_){
_start:
{
uint8_t v_res_3584_; lean_object* v_r_3585_; 
v_res_3584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3581_, v_a_3582_, v_x_3583_);
lean_dec(v_x_3583_);
lean_dec_ref(v_a_3582_);
v_r_3585_ = lean_box(v_res_3584_);
return v_r_3585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3586_, lean_object* v_data_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3589_, lean_object* v_n_3590_, lean_object* v_k_3591_, lean_object* v_v_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3590_, v_k_3591_, v_v_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3594_, size_t v_depth_3595_, lean_object* v_keys_3596_, lean_object* v_vals_3597_, lean_object* v_heq_3598_, lean_object* v_i_3599_, lean_object* v_entries_3600_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3595_, v_keys_3596_, v_vals_3597_, v_i_3599_, v_entries_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3602_, lean_object* v_depth_3603_, lean_object* v_keys_3604_, lean_object* v_vals_3605_, lean_object* v_heq_3606_, lean_object* v_i_3607_, lean_object* v_entries_3608_){
_start:
{
size_t v_depth_boxed_3609_; lean_object* v_res_3610_; 
v_depth_boxed_3609_ = lean_unbox_usize(v_depth_3603_);
lean_dec(v_depth_3603_);
v_res_3610_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3602_, v_depth_boxed_3609_, v_keys_3604_, v_vals_3605_, v_heq_3606_, v_i_3607_, v_entries_3608_);
lean_dec_ref(v_vals_3605_);
lean_dec_ref(v_keys_3604_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3611_, lean_object* v_i_3612_, lean_object* v_source_3613_, lean_object* v_target_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3612_, v_source_3613_, v_target_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3617_, v_x_3618_, v_x_3619_, v_x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3623_, v_x_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
uint8_t v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = 1;
v___x_3637_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_3636_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3658_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3661_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3662_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3658_, v___x_3659_, v___x_3660_, v___x_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3693_ = l_Lean_addBuiltinDeclarationRanges(v___x_3691_, v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_3700_);
lean_dec(v_x_3700_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___y_3724_; uint8_t v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_3713_);
v___x_3755_ = l_Lean_Syntax_isOfKind(v_stx_3713_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; 
lean_dec(v_stx_3713_);
v___x_3756_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3756_;
}
else
{
lean_object* v___x_3757_; lean_object* v___y_3759_; uint8_t v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3826_; uint8_t v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3855_; uint8_t v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v_tk_3884_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v_args_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___x_3944_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v_only_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v_unfold_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v_squeeze_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_3757_ = lean_unsigned_to_nat(0u);
v_tk_3884_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_3757_);
v___x_3944_ = lean_unsigned_to_nat(1u);
v___x_4020_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_3944_);
v___x_4021_ = l_Lean_Syntax_isNone(v___x_4020_);
if (v___x_4021_ == 0)
{
uint8_t v___x_4022_; 
lean_inc(v___x_4020_);
v___x_4022_ = l_Lean_Syntax_matchesNull(v___x_4020_, v___x_3944_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; 
lean_dec(v___x_4020_);
lean_dec(v_tk_3884_);
lean_dec(v_stx_3713_);
v___x_4023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4023_;
}
else
{
lean_object* v_squeeze_4024_; lean_object* v___x_4025_; 
v_squeeze_4024_ = l_Lean_Syntax_getArg(v___x_4020_, v___x_3757_);
lean_dec(v___x_4020_);
v___x_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4025_, 0, v_squeeze_4024_);
v_squeeze_4003_ = v___x_4025_;
v___y_4004_ = v_a_3714_;
v___y_4005_ = v_a_3715_;
v___y_4006_ = v_a_3716_;
v___y_4007_ = v_a_3717_;
v___y_4008_ = v_a_3718_;
v___y_4009_ = v_a_3719_;
v___y_4010_ = v_a_3720_;
v___y_4011_ = v_a_3721_;
goto v___jp_4002_;
}
}
else
{
lean_object* v___x_4026_; 
lean_dec(v___x_4020_);
v___x_4026_ = lean_box(0);
v_squeeze_4003_ = v___x_4026_;
v___y_4004_ = v_a_3714_;
v___y_4005_ = v_a_3715_;
v___y_4006_ = v_a_3716_;
v___y_4007_ = v_a_3717_;
v___y_4008_ = v_a_3718_;
v___y_4009_ = v_a_3719_;
v___y_4010_ = v_a_3720_;
v___y_4011_ = v_a_3721_;
goto v___jp_4002_;
}
v___jp_3758_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
lean_inc_ref(v___y_3776_);
v___x_3781_ = l_Array_append___redArg(v___y_3776_, v___y_3780_);
lean_dec_ref(v___y_3780_);
lean_inc(v___y_3765_);
lean_inc(v___y_3770_);
v___x_3782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3782_, 0, v___y_3770_);
lean_ctor_set(v___x_3782_, 1, v___y_3765_);
lean_ctor_set(v___x_3782_, 2, v___x_3781_);
if (lean_obj_tag(v___y_3761_) == 1)
{
lean_object* v_val_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_val_3783_ = lean_ctor_get(v___y_3761_, 0);
lean_inc(v_val_3783_);
lean_dec_ref_known(v___y_3761_, 1);
v___x_3784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
v___x_3785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3770_, 4);
v___x_3786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___y_3770_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
lean_inc_ref(v___y_3776_);
v___x_3787_ = l_Array_append___redArg(v___y_3776_, v_val_3783_);
lean_dec(v_val_3783_);
lean_inc(v___y_3765_);
v___x_3788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3788_, 0, v___y_3770_);
lean_ctor_set(v___x_3788_, 1, v___y_3765_);
lean_ctor_set(v___x_3788_, 2, v___x_3787_);
v___x_3789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___y_3770_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = l_Lean_Syntax_node3(v___y_3770_, v___x_3784_, v___x_3786_, v___x_3788_, v___x_3790_);
v___x_3792_ = l_Array_mkArray1___redArg(v___x_3791_);
v___y_3724_ = v___y_3759_;
v___y_3725_ = v___y_3760_;
v___y_3726_ = v___x_3782_;
v___y_3727_ = v___y_3762_;
v___y_3728_ = v___y_3763_;
v___y_3729_ = v___y_3764_;
v___y_3730_ = v___y_3765_;
v___y_3731_ = v___y_3766_;
v___y_3732_ = v___y_3767_;
v___y_3733_ = v___y_3768_;
v___y_3734_ = v___y_3769_;
v___y_3735_ = v___y_3770_;
v___y_3736_ = v___y_3771_;
v___y_3737_ = v___y_3772_;
v___y_3738_ = v___y_3773_;
v___y_3739_ = v___y_3774_;
v___y_3740_ = v___y_3775_;
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3777_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___x_3792_;
goto v___jp_3723_;
}
else
{
lean_object* v___x_3793_; 
lean_dec(v___y_3761_);
v___x_3793_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3724_ = v___y_3759_;
v___y_3725_ = v___y_3760_;
v___y_3726_ = v___x_3782_;
v___y_3727_ = v___y_3762_;
v___y_3728_ = v___y_3763_;
v___y_3729_ = v___y_3764_;
v___y_3730_ = v___y_3765_;
v___y_3731_ = v___y_3766_;
v___y_3732_ = v___y_3767_;
v___y_3733_ = v___y_3768_;
v___y_3734_ = v___y_3769_;
v___y_3735_ = v___y_3770_;
v___y_3736_ = v___y_3771_;
v___y_3737_ = v___y_3772_;
v___y_3738_ = v___y_3773_;
v___y_3739_ = v___y_3774_;
v___y_3740_ = v___y_3775_;
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3777_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___x_3793_;
goto v___jp_3723_;
}
}
v___jp_3794_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_inc_ref(v___y_3812_);
v___x_3817_ = l_Array_append___redArg(v___y_3812_, v___y_3816_);
lean_dec_ref(v___y_3816_);
lean_inc(v___y_3802_);
lean_inc(v___y_3807_);
v___x_3818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3818_, 0, v___y_3807_);
lean_ctor_set(v___x_3818_, 1, v___y_3802_);
lean_ctor_set(v___x_3818_, 2, v___x_3817_);
if (lean_obj_tag(v___y_3799_) == 1)
{
lean_object* v_val_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_val_3819_ = lean_ctor_get(v___y_3799_, 0);
lean_inc(v_val_3819_);
lean_dec_ref_known(v___y_3799_, 1);
v___x_3820_ = l_Lean_SourceInfo_fromRef(v_val_3819_, v___x_3755_);
lean_dec(v_val_3819_);
v___x_3821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3820_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = l_Array_mkArray1___redArg(v___x_3822_);
v___y_3759_ = v___y_3795_;
v___y_3760_ = v___y_3796_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3798_;
v___y_3763_ = v___y_3800_;
v___y_3764_ = v___y_3801_;
v___y_3765_ = v___y_3802_;
v___y_3766_ = v___y_3803_;
v___y_3767_ = v___y_3804_;
v___y_3768_ = v___y_3805_;
v___y_3769_ = v___y_3806_;
v___y_3770_ = v___y_3807_;
v___y_3771_ = v___x_3818_;
v___y_3772_ = v___y_3808_;
v___y_3773_ = v___y_3809_;
v___y_3774_ = v___y_3810_;
v___y_3775_ = v___y_3811_;
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3813_;
v___y_3778_ = v___y_3814_;
v___y_3779_ = v___y_3815_;
v___y_3780_ = v___x_3823_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3799_);
lean_dec(v___y_3799_);
v___y_3759_ = v___y_3795_;
v___y_3760_ = v___y_3796_;
v___y_3761_ = v___y_3797_;
v___y_3762_ = v___y_3798_;
v___y_3763_ = v___y_3800_;
v___y_3764_ = v___y_3801_;
v___y_3765_ = v___y_3802_;
v___y_3766_ = v___y_3803_;
v___y_3767_ = v___y_3804_;
v___y_3768_ = v___y_3805_;
v___y_3769_ = v___y_3806_;
v___y_3770_ = v___y_3807_;
v___y_3771_ = v___x_3818_;
v___y_3772_ = v___y_3808_;
v___y_3773_ = v___y_3809_;
v___y_3774_ = v___y_3810_;
v___y_3775_ = v___y_3811_;
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3813_;
v___y_3778_ = v___y_3814_;
v___y_3779_ = v___y_3815_;
v___y_3780_ = v___x_3824_;
goto v___jp_3758_;
}
}
v___jp_3825_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_inc_ref(v___y_3842_);
v___x_3847_ = l_Array_append___redArg(v___y_3842_, v___y_3846_);
lean_dec_ref(v___y_3846_);
lean_inc(v___y_3833_);
lean_inc(v___y_3837_);
v___x_3848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3848_, 0, v___y_3837_);
lean_ctor_set(v___x_3848_, 1, v___y_3833_);
lean_ctor_set(v___x_3848_, 2, v___x_3847_);
v___x_3849_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7));
if (lean_obj_tag(v___y_3831_) == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3795_ = v___y_3826_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3828_;
v___y_3798_ = v___y_3829_;
v___y_3799_ = v___y_3830_;
v___y_3800_ = v___x_3849_;
v___y_3801_ = v___y_3832_;
v___y_3802_ = v___y_3833_;
v___y_3803_ = v___y_3834_;
v___y_3804_ = v___y_3835_;
v___y_3805_ = v___x_3848_;
v___y_3806_ = v___y_3836_;
v___y_3807_ = v___y_3837_;
v___y_3808_ = v___y_3838_;
v___y_3809_ = v___y_3839_;
v___y_3810_ = v___y_3840_;
v___y_3811_ = v___y_3841_;
v___y_3812_ = v___y_3842_;
v___y_3813_ = v___y_3843_;
v___y_3814_ = v___y_3844_;
v___y_3815_ = v___y_3845_;
v___y_3816_ = v___x_3850_;
goto v___jp_3794_;
}
else
{
lean_object* v_val_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_val_3851_ = lean_ctor_get(v___y_3831_, 0);
lean_inc(v_val_3851_);
lean_dec_ref_known(v___y_3831_, 1);
v___x_3852_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3853_ = lean_array_push(v___x_3852_, v_val_3851_);
v___y_3795_ = v___y_3826_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3828_;
v___y_3798_ = v___y_3829_;
v___y_3799_ = v___y_3830_;
v___y_3800_ = v___x_3849_;
v___y_3801_ = v___y_3832_;
v___y_3802_ = v___y_3833_;
v___y_3803_ = v___y_3834_;
v___y_3804_ = v___y_3835_;
v___y_3805_ = v___x_3848_;
v___y_3806_ = v___y_3836_;
v___y_3807_ = v___y_3837_;
v___y_3808_ = v___y_3838_;
v___y_3809_ = v___y_3839_;
v___y_3810_ = v___y_3840_;
v___y_3811_ = v___y_3841_;
v___y_3812_ = v___y_3842_;
v___y_3813_ = v___y_3843_;
v___y_3814_ = v___y_3844_;
v___y_3815_ = v___y_3845_;
v___y_3816_ = v___x_3853_;
goto v___jp_3794_;
}
}
v___jp_3854_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_inc_ref(v___y_3870_);
v___x_3876_ = l_Array_append___redArg(v___y_3870_, v___y_3875_);
lean_dec_ref(v___y_3875_);
lean_inc(v___y_3861_);
lean_inc(v___y_3865_);
v___x_3877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3877_, 0, v___y_3865_);
lean_ctor_set(v___x_3877_, 1, v___y_3861_);
lean_ctor_set(v___x_3877_, 2, v___x_3876_);
if (lean_obj_tag(v___y_3871_) == 1)
{
lean_object* v_val_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_val_3878_ = lean_ctor_get(v___y_3871_, 0);
lean_inc(v_val_3878_);
lean_dec_ref_known(v___y_3871_, 1);
v___x_3879_ = l_Lean_SourceInfo_fromRef(v_val_3878_, v___x_3755_);
lean_dec(v_val_3878_);
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_3881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Array_mkArray1___redArg(v___x_3881_);
v___y_3826_ = v___y_3855_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3857_;
v___y_3829_ = v___y_3858_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___y_3860_;
v___y_3832_ = v___x_3877_;
v___y_3833_ = v___y_3861_;
v___y_3834_ = v___y_3862_;
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3865_;
v___y_3838_ = v___y_3866_;
v___y_3839_ = v___y_3867_;
v___y_3840_ = v___y_3868_;
v___y_3841_ = v___y_3869_;
v___y_3842_ = v___y_3870_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___x_3882_;
goto v___jp_3825_;
}
else
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3871_);
lean_dec(v___y_3871_);
v___y_3826_ = v___y_3855_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3857_;
v___y_3829_ = v___y_3858_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___y_3860_;
v___y_3832_ = v___x_3877_;
v___y_3833_ = v___y_3861_;
v___y_3834_ = v___y_3862_;
v___y_3835_ = v___y_3863_;
v___y_3836_ = v___y_3864_;
v___y_3837_ = v___y_3865_;
v___y_3838_ = v___y_3866_;
v___y_3839_ = v___y_3867_;
v___y_3840_ = v___y_3868_;
v___y_3841_ = v___y_3869_;
v___y_3842_ = v___y_3870_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___x_3883_;
goto v___jp_3825_;
}
}
v___jp_3885_:
{
lean_object* v_ref_3901_; uint8_t v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_ref_3901_ = lean_ctor_get(v___y_3893_, 5);
v___x_3902_ = 0;
v___x_3903_ = l_Lean_SourceInfo_fromRef(v_ref_3901_, v___x_3902_);
v___x_3904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3906_ = l_Lean_SourceInfo_fromRef(v_tk_3884_, v___x_3755_);
lean_dec(v_tk_3884_);
v___x_3907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
lean_ctor_set(v___x_3907_, 1, v___x_3904_);
v___x_3908_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_3909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_3890_) == 1)
{
lean_object* v_val_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_val_3910_ = lean_ctor_get(v___y_3890_, 0);
lean_inc(v_val_3910_);
lean_dec_ref_known(v___y_3890_, 1);
v___x_3911_ = l_Lean_SourceInfo_fromRef(v_val_3910_, v___x_3755_);
lean_dec(v_val_3910_);
v___x_3912_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_3913_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = l_Array_mkArray1___redArg(v___x_3913_);
v___y_3855_ = v___x_3907_;
v___y_3856_ = v___x_3902_;
v___y_3857_ = v___y_3886_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___y_3900_;
v___y_3861_ = v___x_3908_;
v___y_3862_ = v___y_3889_;
v___y_3863_ = v___y_3891_;
v___y_3864_ = v___x_3905_;
v___y_3865_ = v___x_3903_;
v___y_3866_ = v___y_3892_;
v___y_3867_ = v___y_3893_;
v___y_3868_ = v___y_3894_;
v___y_3869_ = v___y_3895_;
v___y_3870_ = v___x_3909_;
v___y_3871_ = v___y_3896_;
v___y_3872_ = v___y_3897_;
v___y_3873_ = v___y_3898_;
v___y_3874_ = v___y_3899_;
v___y_3875_ = v___x_3914_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3890_);
lean_dec(v___y_3890_);
v___y_3855_ = v___x_3907_;
v___y_3856_ = v___x_3902_;
v___y_3857_ = v___y_3886_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___y_3900_;
v___y_3861_ = v___x_3908_;
v___y_3862_ = v___y_3889_;
v___y_3863_ = v___y_3891_;
v___y_3864_ = v___x_3905_;
v___y_3865_ = v___x_3903_;
v___y_3866_ = v___y_3892_;
v___y_3867_ = v___y_3893_;
v___y_3868_ = v___y_3894_;
v___y_3869_ = v___y_3895_;
v___y_3870_ = v___x_3909_;
v___y_3871_ = v___y_3896_;
v___y_3872_ = v___y_3897_;
v___y_3873_ = v___y_3898_;
v___y_3874_ = v___y_3899_;
v___y_3875_ = v___x_3915_;
goto v___jp_3854_;
}
}
v___jp_3916_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = lean_unsigned_to_nat(5u);
v___x_3933_ = l_Lean_Syntax_getArg(v___y_3918_, v___x_3932_);
lean_dec(v___y_3918_);
v___x_3934_ = l_Lean_Syntax_getOptional_x3f(v___y_3919_);
lean_dec(v___y_3919_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_box(0);
v___y_3886_ = v_args_3923_;
v___y_3887_ = v___y_3929_;
v___y_3888_ = v___y_3917_;
v___y_3889_ = v___y_3928_;
v___y_3890_ = v___y_3922_;
v___y_3891_ = v___y_3926_;
v___y_3892_ = v___y_3931_;
v___y_3893_ = v___y_3930_;
v___y_3894_ = v___y_3927_;
v___y_3895_ = v___x_3933_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___y_3925_;
v___y_3898_ = v___y_3924_;
v___y_3899_ = v___y_3921_;
v___y_3900_ = v___x_3935_;
goto v___jp_3885_;
}
else
{
lean_object* v_val_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
v_val_3936_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3934_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_val_3936_);
lean_dec(v___x_3934_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_val_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
v___y_3886_ = v_args_3923_;
v___y_3887_ = v___y_3929_;
v___y_3888_ = v___y_3917_;
v___y_3889_ = v___y_3928_;
v___y_3890_ = v___y_3922_;
v___y_3891_ = v___y_3926_;
v___y_3892_ = v___y_3931_;
v___y_3893_ = v___y_3930_;
v___y_3894_ = v___y_3927_;
v___y_3895_ = v___x_3933_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___y_3925_;
v___y_3898_ = v___y_3924_;
v___y_3899_ = v___y_3921_;
v___y_3900_ = v___x_3941_;
goto v___jp_3885_;
}
}
}
}
v___jp_3945_:
{
lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3961_ = l_Lean_Syntax_getArg(v___y_3947_, v___y_3946_);
v___x_3962_ = l_Lean_Syntax_isNone(v___x_3961_);
if (v___x_3962_ == 0)
{
uint8_t v___x_3963_; 
lean_inc(v___x_3961_);
v___x_3963_ = l_Lean_Syntax_matchesNull(v___x_3961_, v___x_3944_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_dec(v___x_3961_);
lean_dec(v_only_3952_);
lean_dec(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec(v_tk_3884_);
v___x_3964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3964_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3965_ = l_Lean_Syntax_getArg(v___x_3961_, v___x_3757_);
lean_dec(v___x_3961_);
v___x_3966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
lean_inc(v___x_3965_);
v___x_3967_ = l_Lean_Syntax_isOfKind(v___x_3965_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_dec(v___x_3965_);
lean_dec(v_only_3952_);
lean_dec(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec(v_tk_3884_);
v___x_3968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; lean_object* v_args_3970_; lean_object* v___x_3971_; 
v___x_3969_ = l_Lean_Syntax_getArg(v___x_3965_, v___x_3944_);
lean_dec(v___x_3965_);
v_args_3970_ = l_Lean_Syntax_getArgs(v___x_3969_);
lean_dec(v___x_3969_);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v_args_3970_);
v___y_3917_ = v_only_3952_;
v___y_3918_ = v___y_3947_;
v___y_3919_ = v___y_3949_;
v___y_3920_ = v___y_3948_;
v___y_3921_ = v___y_3951_;
v___y_3922_ = v___y_3950_;
v_args_3923_ = v___x_3971_;
v___y_3924_ = v___y_3953_;
v___y_3925_ = v___y_3954_;
v___y_3926_ = v___y_3955_;
v___y_3927_ = v___y_3956_;
v___y_3928_ = v___y_3957_;
v___y_3929_ = v___y_3958_;
v___y_3930_ = v___y_3959_;
v___y_3931_ = v___y_3960_;
goto v___jp_3916_;
}
}
}
else
{
lean_object* v___x_3972_; 
lean_dec(v___x_3961_);
v___x_3972_ = lean_box(0);
v___y_3917_ = v_only_3952_;
v___y_3918_ = v___y_3947_;
v___y_3919_ = v___y_3949_;
v___y_3920_ = v___y_3948_;
v___y_3921_ = v___y_3951_;
v___y_3922_ = v___y_3950_;
v_args_3923_ = v___x_3972_;
v___y_3924_ = v___y_3953_;
v___y_3925_ = v___y_3954_;
v___y_3926_ = v___y_3955_;
v___y_3927_ = v___y_3956_;
v___y_3928_ = v___y_3957_;
v___y_3929_ = v___y_3958_;
v___y_3930_ = v___y_3959_;
v___y_3931_ = v___y_3960_;
goto v___jp_3916_;
}
}
v___jp_3973_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3985_ = lean_unsigned_to_nat(3u);
v___x_3986_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_3985_);
lean_dec(v_stx_3713_);
v___x_3987_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_3986_);
v___x_3988_ = l_Lean_Syntax_isOfKind(v___x_3986_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_dec(v___x_3986_);
lean_dec(v_unfold_3976_);
lean_dec(v___y_3975_);
lean_dec(v_tk_3884_);
v___x_3989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3990_ = l_Lean_Syntax_getArg(v___x_3986_, v___x_3757_);
v___x_3991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9));
lean_inc(v___x_3990_);
v___x_3992_ = l_Lean_Syntax_isOfKind(v___x_3990_, v___x_3991_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; 
lean_dec(v___x_3990_);
lean_dec(v___x_3986_);
lean_dec(v_unfold_3976_);
lean_dec(v___y_3975_);
lean_dec(v_tk_3884_);
v___x_3993_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3993_;
}
else
{
lean_object* v___x_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; 
v___x_3994_ = l_Lean_Syntax_getArg(v___x_3986_, v___x_3944_);
v___x_3995_ = l_Lean_Syntax_getArg(v___x_3986_, v___y_3974_);
v___x_3996_ = l_Lean_Syntax_isNone(v___x_3995_);
if (v___x_3996_ == 0)
{
uint8_t v___x_3997_; 
lean_inc(v___x_3995_);
v___x_3997_ = l_Lean_Syntax_matchesNull(v___x_3995_, v___x_3944_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; 
lean_dec(v___x_3995_);
lean_dec(v___x_3994_);
lean_dec(v___x_3990_);
lean_dec(v___x_3986_);
lean_dec(v_unfold_3976_);
lean_dec(v___y_3975_);
lean_dec(v_tk_3884_);
v___x_3998_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3998_;
}
else
{
lean_object* v_only_3999_; lean_object* v___x_4000_; 
v_only_3999_ = l_Lean_Syntax_getArg(v___x_3995_, v___x_3757_);
lean_dec(v___x_3995_);
v___x_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_only_3999_);
v___y_3946_ = v___x_3985_;
v___y_3947_ = v___x_3986_;
v___y_3948_ = v_unfold_3976_;
v___y_3949_ = v___x_3994_;
v___y_3950_ = v___y_3975_;
v___y_3951_ = v___x_3990_;
v_only_3952_ = v___x_4000_;
v___y_3953_ = v___y_3977_;
v___y_3954_ = v___y_3978_;
v___y_3955_ = v___y_3979_;
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3981_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3983_;
v___y_3960_ = v___y_3984_;
goto v___jp_3945_;
}
}
else
{
lean_object* v___x_4001_; 
lean_dec(v___x_3995_);
v___x_4001_ = lean_box(0);
v___y_3946_ = v___x_3985_;
v___y_3947_ = v___x_3986_;
v___y_3948_ = v_unfold_3976_;
v___y_3949_ = v___x_3994_;
v___y_3950_ = v___y_3975_;
v___y_3951_ = v___x_3990_;
v_only_3952_ = v___x_4001_;
v___y_3953_ = v___y_3977_;
v___y_3954_ = v___y_3978_;
v___y_3955_ = v___y_3979_;
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3981_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3983_;
v___y_3960_ = v___y_3984_;
goto v___jp_3945_;
}
}
}
}
v___jp_4002_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4012_ = lean_unsigned_to_nat(2u);
v___x_4013_ = l_Lean_Syntax_getArg(v_stx_3713_, v___x_4012_);
v___x_4014_ = l_Lean_Syntax_isNone(v___x_4013_);
if (v___x_4014_ == 0)
{
uint8_t v___x_4015_; 
lean_inc(v___x_4013_);
v___x_4015_ = l_Lean_Syntax_matchesNull(v___x_4013_, v___x_3944_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; 
lean_dec(v___x_4013_);
lean_dec(v_squeeze_4003_);
lean_dec(v_tk_3884_);
lean_dec(v_stx_3713_);
v___x_4016_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4016_;
}
else
{
lean_object* v_unfold_4017_; lean_object* v___x_4018_; 
v_unfold_4017_ = l_Lean_Syntax_getArg(v___x_4013_, v___x_3757_);
lean_dec(v___x_4013_);
v___x_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_unfold_4017_);
v___y_3974_ = v___x_4012_;
v___y_3975_ = v_squeeze_4003_;
v_unfold_3976_ = v___x_4018_;
v___y_3977_ = v___y_4004_;
v___y_3978_ = v___y_4005_;
v___y_3979_ = v___y_4006_;
v___y_3980_ = v___y_4007_;
v___y_3981_ = v___y_4008_;
v___y_3982_ = v___y_4009_;
v___y_3983_ = v___y_4010_;
v___y_3984_ = v___y_4011_;
goto v___jp_3973_;
}
}
else
{
lean_object* v___x_4019_; 
lean_dec(v___x_4013_);
v___x_4019_ = lean_box(0);
v___y_3974_ = v___x_4012_;
v___y_3975_ = v_squeeze_4003_;
v_unfold_3976_ = v___x_4019_;
v___y_3977_ = v___y_4004_;
v___y_3978_ = v___y_4005_;
v___y_3979_ = v___y_4006_;
v___y_3980_ = v___y_4007_;
v___y_3981_ = v___y_4008_;
v___y_3982_ = v___y_4009_;
v___y_3983_ = v___y_4010_;
v___y_3984_ = v___y_4011_;
goto v___jp_3973_;
}
}
}
v___jp_3723_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_inc_ref(v___y_3741_);
v___x_3746_ = l_Array_append___redArg(v___y_3741_, v___y_3745_);
lean_dec_ref(v___y_3745_);
lean_inc_n(v___y_3730_, 2);
lean_inc_n(v___y_3735_, 4);
v___x_3747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3747_, 0, v___y_3735_);
lean_ctor_set(v___x_3747_, 1, v___y_3730_);
lean_ctor_set(v___x_3747_, 2, v___x_3746_);
v___x_3748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___y_3735_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = l_Lean_Syntax_node2(v___y_3735_, v___y_3730_, v___x_3749_, v___y_3740_);
lean_inc(v___y_3728_);
v___x_3751_ = l_Lean_Syntax_node5(v___y_3735_, v___y_3728_, v___y_3744_, v___y_3736_, v___y_3726_, v___x_3747_, v___x_3750_);
lean_inc(v___y_3734_);
v___x_3752_ = l_Lean_Syntax_node4(v___y_3735_, v___y_3734_, v___y_3724_, v___y_3729_, v___y_3733_, v___x_3751_);
v___x_3753_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3725_, v___x_3752_, v___y_3743_, v___y_3742_, v___y_3732_, v___y_3739_, v___y_3731_, v___y_3727_, v___y_3738_, v___y_3737_);
return v___x_3753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4046_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4047_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4049_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4050_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4046_, v___x_4047_, v___x_4048_, v___x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4052_;
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
res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
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
