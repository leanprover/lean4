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
lean_object* v___f_247_; lean_object* v___x_81824__overap_248_; lean_object* v___x_249_; 
v___f_247_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0));
v___x_81824__overap_248_ = lean_panic_fn_borrowed(v___f_247_, v_msg_237_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
lean_inc_ref(v___y_240_);
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
v___x_249_ = lean_apply_9(v___x_81824__overap_248_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, lean_box(0));
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
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_575_; 
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v___x_405_, 0);
lean_dec(v_unused_576_);
v___x_407_ = v___x_405_;
v_isShared_408_ = v_isSharedCheck_575_;
goto v_resetjp_406_;
}
else
{
lean_dec(v___x_405_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_575_;
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
lean_object* v_a_410_; uint8_t v_____do__lift_412_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___y_415_; lean_object* v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
if (v_useReducible_355_ == 0)
{
lean_object* v___x_430_; uint8_t v_foApprox_431_; uint8_t v_ctxApprox_432_; uint8_t v_quasiPatternApprox_433_; uint8_t v_constApprox_434_; uint8_t v_isDefEqStuckEx_435_; uint8_t v_unificationHints_436_; uint8_t v_proofIrrelevance_437_; uint8_t v_offsetCnstrs_438_; uint8_t v_transparency_439_; uint8_t v_etaStruct_440_; uint8_t v_univApprox_441_; uint8_t v_iota_442_; uint8_t v_beta_443_; uint8_t v_proj_444_; uint8_t v_zeta_445_; uint8_t v_zetaDelta_446_; uint8_t v_zetaUnused_447_; uint8_t v_zetaHave_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_479_; 
v___x_430_ = l_Lean_Meta_Context_config(v___y_361_);
v_foApprox_431_ = lean_ctor_get_uint8(v___x_430_, 0);
v_ctxApprox_432_ = lean_ctor_get_uint8(v___x_430_, 1);
v_quasiPatternApprox_433_ = lean_ctor_get_uint8(v___x_430_, 2);
v_constApprox_434_ = lean_ctor_get_uint8(v___x_430_, 3);
v_isDefEqStuckEx_435_ = lean_ctor_get_uint8(v___x_430_, 4);
v_unificationHints_436_ = lean_ctor_get_uint8(v___x_430_, 5);
v_proofIrrelevance_437_ = lean_ctor_get_uint8(v___x_430_, 6);
v_offsetCnstrs_438_ = lean_ctor_get_uint8(v___x_430_, 8);
v_transparency_439_ = lean_ctor_get_uint8(v___x_430_, 9);
v_etaStruct_440_ = lean_ctor_get_uint8(v___x_430_, 10);
v_univApprox_441_ = lean_ctor_get_uint8(v___x_430_, 11);
v_iota_442_ = lean_ctor_get_uint8(v___x_430_, 12);
v_beta_443_ = lean_ctor_get_uint8(v___x_430_, 13);
v_proj_444_ = lean_ctor_get_uint8(v___x_430_, 14);
v_zeta_445_ = lean_ctor_get_uint8(v___x_430_, 15);
v_zetaDelta_446_ = lean_ctor_get_uint8(v___x_430_, 16);
v_zetaUnused_447_ = lean_ctor_get_uint8(v___x_430_, 17);
v_zetaHave_448_ = lean_ctor_get_uint8(v___x_430_, 18);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_479_ == 0)
{
v___x_450_ = v___x_430_;
v_isShared_451_ = v_isSharedCheck_479_;
goto v_resetjp_449_;
}
else
{
lean_dec(v___x_430_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_479_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint8_t v_trackZetaDelta_452_; lean_object* v_zetaDeltaSet_453_; lean_object* v_lctx_454_; lean_object* v_localInstances_455_; lean_object* v_defEqCtx_x3f_456_; lean_object* v_synthPendingDepth_457_; lean_object* v_canUnfold_x3f_458_; uint8_t v_univApprox_459_; uint8_t v_inTypeClassResolution_460_; uint8_t v_cacheInferType_461_; lean_object* v___x_463_; 
v_trackZetaDelta_452_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7);
v_zetaDeltaSet_453_ = lean_ctor_get(v___y_361_, 1);
v_lctx_454_ = lean_ctor_get(v___y_361_, 2);
v_localInstances_455_ = lean_ctor_get(v___y_361_, 3);
v_defEqCtx_x3f_456_ = lean_ctor_get(v___y_361_, 4);
v_synthPendingDepth_457_ = lean_ctor_get(v___y_361_, 5);
v_canUnfold_x3f_458_ = lean_ctor_get(v___y_361_, 6);
v_univApprox_459_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_460_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 2);
v_cacheInferType_461_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 3);
if (v_isShared_451_ == 0)
{
v___x_463_ = v___x_450_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 0, v_foApprox_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 1, v_ctxApprox_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 2, v_quasiPatternApprox_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 3, v_constApprox_434_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 4, v_isDefEqStuckEx_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 5, v_unificationHints_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 6, v_proofIrrelevance_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 8, v_offsetCnstrs_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 9, v_transparency_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 10, v_etaStruct_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 11, v_univApprox_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 12, v_iota_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 13, v_beta_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 14, v_proj_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 15, v_zeta_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 16, v_zetaDelta_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 17, v_zetaUnused_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, 18, v_zetaHave_448_);
v___x_463_ = v_reuseFailAlloc_478_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
uint64_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_ctor_set_uint8(v___x_463_, 7, v___x_356_);
v___x_464_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set_uint64(v___x_465_, sizeof(void*)*1, v___x_464_);
lean_inc(v_canUnfold_x3f_458_);
lean_inc(v_synthPendingDepth_457_);
lean_inc(v_defEqCtx_x3f_456_);
lean_inc_ref(v_localInstances_455_);
lean_inc_ref(v_lctx_454_);
lean_inc(v_zetaDeltaSet_453_);
v___x_466_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_zetaDeltaSet_453_);
lean_ctor_set(v___x_466_, 2, v_lctx_454_);
lean_ctor_set(v___x_466_, 3, v_localInstances_455_);
lean_ctor_set(v___x_466_, 4, v_defEqCtx_x3f_456_);
lean_ctor_set(v___x_466_, 5, v_synthPendingDepth_457_);
lean_ctor_set(v___x_466_, 6, v_canUnfold_x3f_458_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*7, v_trackZetaDelta_452_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*7 + 1, v_univApprox_459_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*7 + 2, v_inTypeClassResolution_460_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*7 + 3, v_cacheInferType_461_);
lean_inc(v_a_410_);
lean_inc(v_a_367_);
v___x_467_ = l_Lean_Meta_isExprDefEq(v_a_367_, v_a_410_, v___x_466_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref_known(v___x_466_, 7);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; uint8_t v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_unbox(v_a_468_);
lean_dec(v_a_468_);
v_____do__lift_412_ = v___x_469_;
v___y_413_ = v___y_357_;
v___y_414_ = v___y_358_;
v___y_415_ = v___y_359_;
v___y_416_ = v___y_360_;
v___y_417_ = v___y_361_;
v___y_418_ = v___y_362_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
goto v___jp_411_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
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
v_a_470_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_467_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_467_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
else
{
lean_object* v___x_480_; uint8_t v_foApprox_481_; uint8_t v_ctxApprox_482_; uint8_t v_quasiPatternApprox_483_; uint8_t v_constApprox_484_; uint8_t v_isDefEqStuckEx_485_; uint8_t v_unificationHints_486_; uint8_t v_proofIrrelevance_487_; uint8_t v_assignSyntheticOpaque_488_; uint8_t v_offsetCnstrs_489_; uint8_t v_etaStruct_490_; uint8_t v_univApprox_491_; uint8_t v_iota_492_; uint8_t v_beta_493_; uint8_t v_proj_494_; uint8_t v_zeta_495_; uint8_t v_zetaDelta_496_; uint8_t v_zetaUnused_497_; uint8_t v_zetaHave_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_566_; 
v___x_480_ = l_Lean_Meta_Context_config(v___y_361_);
v_foApprox_481_ = lean_ctor_get_uint8(v___x_480_, 0);
v_ctxApprox_482_ = lean_ctor_get_uint8(v___x_480_, 1);
v_quasiPatternApprox_483_ = lean_ctor_get_uint8(v___x_480_, 2);
v_constApprox_484_ = lean_ctor_get_uint8(v___x_480_, 3);
v_isDefEqStuckEx_485_ = lean_ctor_get_uint8(v___x_480_, 4);
v_unificationHints_486_ = lean_ctor_get_uint8(v___x_480_, 5);
v_proofIrrelevance_487_ = lean_ctor_get_uint8(v___x_480_, 6);
v_assignSyntheticOpaque_488_ = lean_ctor_get_uint8(v___x_480_, 7);
v_offsetCnstrs_489_ = lean_ctor_get_uint8(v___x_480_, 8);
v_etaStruct_490_ = lean_ctor_get_uint8(v___x_480_, 10);
v_univApprox_491_ = lean_ctor_get_uint8(v___x_480_, 11);
v_iota_492_ = lean_ctor_get_uint8(v___x_480_, 12);
v_beta_493_ = lean_ctor_get_uint8(v___x_480_, 13);
v_proj_494_ = lean_ctor_get_uint8(v___x_480_, 14);
v_zeta_495_ = lean_ctor_get_uint8(v___x_480_, 15);
v_zetaDelta_496_ = lean_ctor_get_uint8(v___x_480_, 16);
v_zetaUnused_497_ = lean_ctor_get_uint8(v___x_480_, 17);
v_zetaHave_498_ = lean_ctor_get_uint8(v___x_480_, 18);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_566_ == 0)
{
v___x_500_ = v___x_480_;
v_isShared_501_ = v_isSharedCheck_566_;
goto v_resetjp_499_;
}
else
{
lean_dec(v___x_480_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_566_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v_trackZetaDelta_502_; lean_object* v_zetaDeltaSet_503_; lean_object* v_lctx_504_; lean_object* v_localInstances_505_; lean_object* v_defEqCtx_x3f_506_; lean_object* v_synthPendingDepth_507_; lean_object* v_canUnfold_x3f_508_; uint8_t v_univApprox_509_; uint8_t v_inTypeClassResolution_510_; uint8_t v_cacheInferType_511_; uint8_t v___x_512_; lean_object* v_config_514_; 
v_trackZetaDelta_502_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7);
v_zetaDeltaSet_503_ = lean_ctor_get(v___y_361_, 1);
v_lctx_504_ = lean_ctor_get(v___y_361_, 2);
v_localInstances_505_ = lean_ctor_get(v___y_361_, 3);
v_defEqCtx_x3f_506_ = lean_ctor_get(v___y_361_, 4);
v_synthPendingDepth_507_ = lean_ctor_get(v___y_361_, 5);
v_canUnfold_x3f_508_ = lean_ctor_get(v___y_361_, 6);
v_univApprox_509_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_510_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 2);
v_cacheInferType_511_ = lean_ctor_get_uint8(v___y_361_, sizeof(void*)*7 + 3);
v___x_512_ = 2;
if (v_isShared_501_ == 0)
{
v_config_514_ = v___x_500_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 0, v_foApprox_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 1, v_ctxApprox_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 2, v_quasiPatternApprox_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 3, v_constApprox_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 4, v_isDefEqStuckEx_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 5, v_unificationHints_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 6, v_proofIrrelevance_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 7, v_assignSyntheticOpaque_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 8, v_offsetCnstrs_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 10, v_etaStruct_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 11, v_univApprox_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 12, v_iota_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 13, v_beta_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 14, v_proj_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 15, v_zeta_495_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 16, v_zetaDelta_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 17, v_zetaUnused_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, 18, v_zetaHave_498_);
v_config_514_ = v_reuseFailAlloc_565_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v_key_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v_foApprox_524_; uint8_t v_ctxApprox_525_; uint8_t v_quasiPatternApprox_526_; uint8_t v_constApprox_527_; uint8_t v_isDefEqStuckEx_528_; uint8_t v_unificationHints_529_; uint8_t v_proofIrrelevance_530_; uint8_t v_offsetCnstrs_531_; uint8_t v_transparency_532_; uint8_t v_etaStruct_533_; uint8_t v_univApprox_534_; uint8_t v_iota_535_; uint8_t v_beta_536_; uint8_t v_proj_537_; uint8_t v_zeta_538_; uint8_t v_zetaDelta_539_; uint8_t v_zetaUnused_540_; uint8_t v_zetaHave_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_564_; 
lean_ctor_set_uint8(v_config_514_, 9, v___x_512_);
v___x_515_ = l_Lean_Meta_Context_configKey(v___y_361_);
v___x_516_ = 3ULL;
v___x_517_ = lean_uint64_shift_right(v___x_515_, v___x_516_);
v___x_518_ = lean_uint64_shift_left(v___x_517_, v___x_516_);
v___x_519_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4);
v_key_520_ = lean_uint64_lor(v___x_518_, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_521_, 0, v_config_514_);
lean_ctor_set_uint64(v___x_521_, sizeof(void*)*1, v_key_520_);
lean_inc(v_canUnfold_x3f_508_);
lean_inc(v_synthPendingDepth_507_);
lean_inc(v_defEqCtx_x3f_506_);
lean_inc_ref(v_localInstances_505_);
lean_inc_ref(v_lctx_504_);
lean_inc(v_zetaDeltaSet_503_);
v___x_522_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_zetaDeltaSet_503_);
lean_ctor_set(v___x_522_, 2, v_lctx_504_);
lean_ctor_set(v___x_522_, 3, v_localInstances_505_);
lean_ctor_set(v___x_522_, 4, v_defEqCtx_x3f_506_);
lean_ctor_set(v___x_522_, 5, v_synthPendingDepth_507_);
lean_ctor_set(v___x_522_, 6, v_canUnfold_x3f_508_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7, v_trackZetaDelta_502_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7 + 1, v_univApprox_509_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7 + 2, v_inTypeClassResolution_510_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*7 + 3, v_cacheInferType_511_);
v___x_523_ = l_Lean_Meta_Context_config(v___x_522_);
lean_dec_ref_known(v___x_522_, 7);
v_foApprox_524_ = lean_ctor_get_uint8(v___x_523_, 0);
v_ctxApprox_525_ = lean_ctor_get_uint8(v___x_523_, 1);
v_quasiPatternApprox_526_ = lean_ctor_get_uint8(v___x_523_, 2);
v_constApprox_527_ = lean_ctor_get_uint8(v___x_523_, 3);
v_isDefEqStuckEx_528_ = lean_ctor_get_uint8(v___x_523_, 4);
v_unificationHints_529_ = lean_ctor_get_uint8(v___x_523_, 5);
v_proofIrrelevance_530_ = lean_ctor_get_uint8(v___x_523_, 6);
v_offsetCnstrs_531_ = lean_ctor_get_uint8(v___x_523_, 8);
v_transparency_532_ = lean_ctor_get_uint8(v___x_523_, 9);
v_etaStruct_533_ = lean_ctor_get_uint8(v___x_523_, 10);
v_univApprox_534_ = lean_ctor_get_uint8(v___x_523_, 11);
v_iota_535_ = lean_ctor_get_uint8(v___x_523_, 12);
v_beta_536_ = lean_ctor_get_uint8(v___x_523_, 13);
v_proj_537_ = lean_ctor_get_uint8(v___x_523_, 14);
v_zeta_538_ = lean_ctor_get_uint8(v___x_523_, 15);
v_zetaDelta_539_ = lean_ctor_get_uint8(v___x_523_, 16);
v_zetaUnused_540_ = lean_ctor_get_uint8(v___x_523_, 17);
v_zetaHave_541_ = lean_ctor_get_uint8(v___x_523_, 18);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_564_ == 0)
{
v___x_543_ = v___x_523_;
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_523_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 0, v_foApprox_524_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 1, v_ctxApprox_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 2, v_quasiPatternApprox_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 3, v_constApprox_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 4, v_isDefEqStuckEx_528_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 5, v_unificationHints_529_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 6, v_proofIrrelevance_530_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 8, v_offsetCnstrs_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 9, v_transparency_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 10, v_etaStruct_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 11, v_univApprox_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 12, v_iota_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 13, v_beta_536_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 14, v_proj_537_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 15, v_zeta_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 16, v_zetaDelta_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 17, v_zetaUnused_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, 18, v_zetaHave_541_);
v___x_546_ = v_reuseFailAlloc_563_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
uint64_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_ctor_set_uint8(v___x_546_, 7, v___x_356_);
v___x_547_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set_uint64(v___x_548_, sizeof(void*)*1, v___x_547_);
lean_inc(v_canUnfold_x3f_508_);
lean_inc(v_synthPendingDepth_507_);
lean_inc(v_defEqCtx_x3f_506_);
lean_inc_ref(v_localInstances_505_);
lean_inc_ref(v_lctx_504_);
lean_inc(v_zetaDeltaSet_503_);
v___x_549_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v_zetaDeltaSet_503_);
lean_ctor_set(v___x_549_, 2, v_lctx_504_);
lean_ctor_set(v___x_549_, 3, v_localInstances_505_);
lean_ctor_set(v___x_549_, 4, v_defEqCtx_x3f_506_);
lean_ctor_set(v___x_549_, 5, v_synthPendingDepth_507_);
lean_ctor_set(v___x_549_, 6, v_canUnfold_x3f_508_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*7, v_trackZetaDelta_502_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*7 + 1, v_univApprox_509_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*7 + 2, v_inTypeClassResolution_510_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*7 + 3, v_cacheInferType_511_);
lean_inc(v_a_410_);
lean_inc(v_a_367_);
v___x_550_ = l_Lean_Meta_isExprDefEq(v_a_367_, v_a_410_, v___x_549_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref_known(v___x_549_, 7);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; uint8_t v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = lean_unbox(v_a_551_);
lean_dec(v_a_551_);
v_____do__lift_412_ = v___x_552_;
v___y_413_ = v___y_357_;
v___y_414_ = v___y_358_;
v___y_415_ = v___y_359_;
v___y_416_ = v___y_360_;
v___y_417_ = v___y_361_;
v___y_418_ = v___y_362_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
goto v___jp_411_;
}
else
{
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_553_; uint8_t v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_550_, 1);
v___x_554_ = lean_unbox(v_a_553_);
lean_dec(v_a_553_);
v_____do__lift_412_ = v___x_554_;
v___y_413_ = v___y_357_;
v___y_414_ = v___y_358_;
v___y_415_ = v___y_359_;
v___y_416_ = v___y_360_;
v___y_417_ = v___y_361_;
v___y_418_ = v___y_362_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
goto v___jp_411_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
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
v_a_555_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_550_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_550_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
}
}
}
v___jp_411_:
{
if (v_____do__lift_412_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_421_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1);
lean_inc_ref(v_a_351_);
v___x_422_ = l_Lean_indentExpr(v_a_351_);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 1);
lean_ctor_set(v___x_407_, 0, v___x_425_);
v___x_427_ = v___x_407_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_429_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; 
lean_inc(v_a_371_);
v___x_428_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_427_, v_a_367_, v_a_410_, v_a_371_, v___x_354_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec_ref(v___x_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_dec_ref_known(v___x_428_, 1);
v___y_373_ = v___y_413_;
v___y_374_ = v___y_414_;
v___y_375_ = v___y_415_;
v___y_376_ = v___y_416_;
v___y_377_ = v___y_417_;
v___y_378_ = v___y_418_;
v___y_379_ = v___y_419_;
v___y_380_ = v___y_420_;
goto v___jp_372_;
}
else
{
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v_a_371_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
return v___x_428_;
}
}
}
else
{
lean_dec(v_a_410_);
lean_del_object(v___x_407_);
lean_dec(v_a_367_);
lean_dec(v___x_354_);
v___y_373_ = v___y_413_;
v___y_374_ = v___y_414_;
v___y_375_ = v___y_415_;
v___y_376_ = v___y_416_;
v___y_377_ = v___y_417_;
v___y_378_ = v___y_418_;
v___y_379_ = v___y_419_;
v___y_380_ = v___y_420_;
goto v___jp_372_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
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
v_a_567_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_409_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_409_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
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
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_367_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_347_);
v_a_577_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_370_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_370_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___x_354_);
lean_dec_ref(v___x_353_);
lean_dec_ref(v_a_351_);
lean_dec(v_a_348_);
lean_dec(v_a_347_);
v_a_585_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_366_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_366_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object** _args){
lean_object* v_a_593_ = _args[0];
lean_object* v_a_594_ = _args[1];
lean_object* v___x_595_ = _args[2];
lean_object* v___x_596_ = _args[3];
lean_object* v_a_597_ = _args[4];
lean_object* v_mvarCounter_598_ = _args[5];
lean_object* v___x_599_ = _args[6];
lean_object* v___x_600_ = _args[7];
lean_object* v_useReducible_601_ = _args[8];
lean_object* v___x_602_ = _args[9];
lean_object* v___y_603_ = _args[10];
lean_object* v___y_604_ = _args[11];
lean_object* v___y_605_ = _args[12];
lean_object* v___y_606_ = _args[13];
lean_object* v___y_607_ = _args[14];
lean_object* v___y_608_ = _args[15];
lean_object* v___y_609_ = _args[16];
lean_object* v___y_610_ = _args[17];
lean_object* v___y_611_ = _args[18];
_start:
{
uint8_t v___x_94441__boxed_612_; uint8_t v___x_94442__boxed_613_; uint8_t v_useReducible_boxed_614_; uint8_t v___x_94446__boxed_615_; lean_object* v_res_616_; 
v___x_94441__boxed_612_ = lean_unbox(v___x_595_);
v___x_94442__boxed_613_ = lean_unbox(v___x_596_);
v_useReducible_boxed_614_ = lean_unbox(v_useReducible_601_);
v___x_94446__boxed_615_ = lean_unbox(v___x_602_);
v_res_616_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_593_, v_a_594_, v___x_94441__boxed_612_, v___x_94442__boxed_613_, v_a_597_, v_mvarCounter_598_, v___x_599_, v___x_600_, v_useReducible_boxed_614_, v___x_94446__boxed_615_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v_mvarCounter_598_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_infoState_628_; lean_object* v_env_629_; lean_object* v_nextMacroScope_630_; lean_object* v_ngen_631_; lean_object* v_auxDeclNGen_632_; lean_object* v_traceState_633_; lean_object* v_cache_634_; lean_object* v_messages_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_657_; 
v___x_627_ = lean_st_ref_take(v___y_625_);
v_infoState_628_ = lean_ctor_get(v___x_627_, 7);
v_env_629_ = lean_ctor_get(v___x_627_, 0);
v_nextMacroScope_630_ = lean_ctor_get(v___x_627_, 1);
v_ngen_631_ = lean_ctor_get(v___x_627_, 2);
v_auxDeclNGen_632_ = lean_ctor_get(v___x_627_, 3);
v_traceState_633_ = lean_ctor_get(v___x_627_, 4);
v_cache_634_ = lean_ctor_get(v___x_627_, 5);
v_messages_635_ = lean_ctor_get(v___x_627_, 6);
v_snapshotTasks_636_ = lean_ctor_get(v___x_627_, 8);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_657_ == 0)
{
v___x_638_ = v___x_627_;
v_isShared_639_ = v_isSharedCheck_657_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snapshotTasks_636_);
lean_inc(v_infoState_628_);
lean_inc(v_messages_635_);
lean_inc(v_cache_634_);
lean_inc(v_traceState_633_);
lean_inc(v_auxDeclNGen_632_);
lean_inc(v_ngen_631_);
lean_inc(v_nextMacroScope_630_);
lean_inc(v_env_629_);
lean_dec(v___x_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_657_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint8_t v_enabled_640_; lean_object* v_assignment_641_; lean_object* v_lazyAssignment_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_655_; 
v_enabled_640_ = lean_ctor_get_uint8(v_infoState_628_, sizeof(void*)*3);
v_assignment_641_ = lean_ctor_get(v_infoState_628_, 0);
v_lazyAssignment_642_ = lean_ctor_get(v_infoState_628_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_infoState_628_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_infoState_628_, 2);
lean_dec(v_unused_656_);
v___x_644_ = v_infoState_628_;
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_lazyAssignment_642_);
lean_inc(v_assignment_641_);
lean_dec(v_infoState_628_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 2, v_a_617_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_assignment_641_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_lazyAssignment_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_a_617_);
lean_ctor_set_uint8(v_reuseFailAlloc_654_, sizeof(void*)*3, v_enabled_640_);
v___x_647_ = v_reuseFailAlloc_654_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 7, v___x_647_);
v___x_649_ = v___x_638_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_env_629_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_nextMacroScope_630_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_ngen_631_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_auxDeclNGen_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_traceState_633_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v_cache_634_);
lean_ctor_set(v_reuseFailAlloc_653_, 6, v_messages_635_);
lean_ctor_set(v_reuseFailAlloc_653_, 7, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 8, v_snapshotTasks_636_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_st_ref_set(v___y_625_, v___x_649_);
v___x_651_ = lean_box(0);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object* v_a_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
return v_x_669_;
}
else
{
lean_object* v_key_671_; lean_object* v_value_672_; lean_object* v_tail_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_696_; 
v_key_671_ = lean_ctor_get(v_x_670_, 0);
v_value_672_ = lean_ctor_get(v_x_670_, 1);
v_tail_673_ = lean_ctor_get(v_x_670_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_696_ == 0)
{
v___x_675_ = v_x_670_;
v_isShared_676_ = v_isSharedCheck_696_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_tail_673_);
lean_inc(v_value_672_);
lean_inc(v_key_671_);
lean_dec(v_x_670_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_696_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; uint64_t v___x_680_; uint64_t v_fold_681_; uint64_t v___x_682_; uint64_t v___x_683_; uint64_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_677_ = lean_array_get_size(v_x_669_);
v___x_678_ = l_Lean_Expr_hash(v_key_671_);
v___x_679_ = 32ULL;
v___x_680_ = lean_uint64_shift_right(v___x_678_, v___x_679_);
v_fold_681_ = lean_uint64_xor(v___x_678_, v___x_680_);
v___x_682_ = 16ULL;
v___x_683_ = lean_uint64_shift_right(v_fold_681_, v___x_682_);
v___x_684_ = lean_uint64_xor(v_fold_681_, v___x_683_);
v___x_685_ = lean_uint64_to_usize(v___x_684_);
v___x_686_ = lean_usize_of_nat(v___x_677_);
v___x_687_ = ((size_t)1ULL);
v___x_688_ = lean_usize_sub(v___x_686_, v___x_687_);
v___x_689_ = lean_usize_land(v___x_685_, v___x_688_);
v___x_690_ = lean_array_uget_borrowed(v_x_669_, v___x_689_);
lean_inc(v___x_690_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 2, v___x_690_);
v___x_692_ = v___x_675_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_key_671_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_value_672_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v___x_690_);
v___x_692_ = v_reuseFailAlloc_695_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_array_uset(v_x_669_, v___x_689_, v___x_692_);
v_x_669_ = v___x_693_;
v_x_670_ = v_tail_673_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object* v_i_697_, lean_object* v_source_698_, lean_object* v_target_699_){
_start:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_array_get_size(v_source_698_);
v___x_701_ = lean_nat_dec_lt(v_i_697_, v___x_700_);
if (v___x_701_ == 0)
{
lean_dec_ref(v_source_698_);
lean_dec(v_i_697_);
return v_target_699_;
}
else
{
lean_object* v_es_702_; lean_object* v___x_703_; lean_object* v_source_704_; lean_object* v_target_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_es_702_ = lean_array_fget(v_source_698_, v_i_697_);
v___x_703_ = lean_box(0);
v_source_704_ = lean_array_fset(v_source_698_, v_i_697_, v___x_703_);
v_target_705_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_699_, v_es_702_);
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v_i_697_, v___x_706_);
lean_dec(v_i_697_);
v_i_697_ = v___x_707_;
v_source_698_ = v_source_704_;
v_target_699_ = v_target_705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_data_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_nbuckets_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_710_ = lean_array_get_size(v_data_709_);
v___x_711_ = lean_unsigned_to_nat(2u);
v_nbuckets_712_ = lean_nat_mul(v___x_710_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_box(0);
v___x_715_ = lean_mk_array(v_nbuckets_712_, v___x_714_);
v___x_716_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_713_, v_data_709_, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_a_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
uint8_t v___x_719_; 
v___x_719_ = 0;
return v___x_719_;
}
else
{
lean_object* v_key_720_; lean_object* v_tail_721_; uint8_t v___x_722_; 
v_key_720_ = lean_ctor_get(v_x_718_, 0);
v_tail_721_ = lean_ctor_get(v_x_718_, 2);
v___x_722_ = lean_expr_eqv(v_key_720_, v_a_717_);
if (v___x_722_ == 0)
{
v_x_718_ = v_tail_721_;
goto _start;
}
else
{
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_a_724_, lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_724_, v_x_725_);
lean_dec(v_x_725_);
lean_dec_ref(v_a_724_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(lean_object* v_m_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
lean_object* v_size_731_; lean_object* v_buckets_732_; lean_object* v___x_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; uint64_t v_fold_737_; uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v___x_743_; size_t v___x_744_; size_t v___x_745_; lean_object* v_bkt_746_; uint8_t v___x_747_; 
v_size_731_ = lean_ctor_get(v_m_728_, 0);
v_buckets_732_ = lean_ctor_get(v_m_728_, 1);
v___x_733_ = lean_array_get_size(v_buckets_732_);
v___x_734_ = l_Lean_Expr_hash(v_a_729_);
v___x_735_ = 32ULL;
v___x_736_ = lean_uint64_shift_right(v___x_734_, v___x_735_);
v_fold_737_ = lean_uint64_xor(v___x_734_, v___x_736_);
v___x_738_ = 16ULL;
v___x_739_ = lean_uint64_shift_right(v_fold_737_, v___x_738_);
v___x_740_ = lean_uint64_xor(v_fold_737_, v___x_739_);
v___x_741_ = lean_uint64_to_usize(v___x_740_);
v___x_742_ = lean_usize_of_nat(v___x_733_);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_sub(v___x_742_, v___x_743_);
v___x_745_ = lean_usize_land(v___x_741_, v___x_744_);
v_bkt_746_ = lean_array_uget_borrowed(v_buckets_732_, v___x_745_);
v___x_747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_729_, v_bkt_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_768_; 
lean_inc_ref(v_buckets_732_);
lean_inc(v_size_731_);
v_isSharedCheck_768_ = !lean_is_exclusive(v_m_728_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_769_ = lean_ctor_get(v_m_728_, 1);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_m_728_, 0);
lean_dec(v_unused_770_);
v___x_749_ = v_m_728_;
v_isShared_750_ = v_isSharedCheck_768_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_m_728_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_768_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v_size_x27_752_; lean_object* v___x_753_; lean_object* v_buckets_x27_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v_size_x27_752_ = lean_nat_add(v_size_731_, v___x_751_);
lean_dec(v_size_731_);
lean_inc(v_bkt_746_);
v___x_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_753_, 0, v_a_729_);
lean_ctor_set(v___x_753_, 1, v_b_730_);
lean_ctor_set(v___x_753_, 2, v_bkt_746_);
v_buckets_x27_754_ = lean_array_uset(v_buckets_732_, v___x_745_, v___x_753_);
v___x_755_ = lean_unsigned_to_nat(4u);
v___x_756_ = lean_nat_mul(v_size_x27_752_, v___x_755_);
v___x_757_ = lean_unsigned_to_nat(3u);
v___x_758_ = lean_nat_div(v___x_756_, v___x_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_array_get_size(v_buckets_x27_754_);
v___x_760_ = lean_nat_dec_le(v___x_758_, v___x_759_);
lean_dec(v___x_758_);
if (v___x_760_ == 0)
{
lean_object* v_val_761_; lean_object* v___x_763_; 
v_val_761_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_754_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_val_761_);
lean_ctor_set(v___x_749_, 0, v_size_x27_752_);
v___x_763_ = v___x_749_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_size_x27_752_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_val_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
else
{
lean_object* v___x_766_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_buckets_x27_754_);
lean_ctor_set(v___x_749_, 0, v_size_x27_752_);
v___x_766_ = v___x_749_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_size_x27_752_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_buckets_x27_754_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_dec(v_b_730_);
lean_dec_ref(v_a_729_);
return v_m_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(lean_object* v_mvarId_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_mctx_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_775_ = lean_st_ref_get(v___y_773_);
v_mctx_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc_ref(v_mctx_776_);
lean_dec(v___x_775_);
v___x_777_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_776_, v_mvarId_771_);
lean_dec_ref(v_mctx_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___y_772_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object* v_mvarId_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec(v_mvarId_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_mvarId_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_mctx_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_790_ = lean_st_ref_get(v___y_788_);
v_mctx_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc_ref(v_mctx_791_);
lean_dec(v___x_790_);
v___x_792_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_791_, v_mvarId_786_);
lean_dec_ref(v_mctx_791_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___y_787_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_mvarId_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec(v_mvarId_796_);
return v_res_800_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_buckets_803_; lean_object* v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v_fold_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_buckets_803_ = lean_ctor_get(v_m_801_, 1);
v___x_804_ = lean_array_get_size(v_buckets_803_);
v___x_805_ = l_Lean_Expr_hash(v_a_802_);
v___x_806_ = 32ULL;
v___x_807_ = lean_uint64_shift_right(v___x_805_, v___x_806_);
v_fold_808_ = lean_uint64_xor(v___x_805_, v___x_807_);
v___x_809_ = 16ULL;
v___x_810_ = lean_uint64_shift_right(v_fold_808_, v___x_809_);
v___x_811_ = lean_uint64_xor(v_fold_808_, v___x_810_);
v___x_812_ = lean_uint64_to_usize(v___x_811_);
v___x_813_ = lean_usize_of_nat(v___x_804_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_sub(v___x_813_, v___x_814_);
v___x_816_ = lean_usize_land(v___x_812_, v___x_815_);
v___x_817_ = lean_array_uget_borrowed(v_buckets_803_, v___x_816_);
v___x_818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_802_, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_819_, lean_object* v_a_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_819_, v_a_820_);
lean_dec_ref(v_a_820_);
lean_dec_ref(v_m_819_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_827_, lean_object* v_e_828_, lean_object* v_a_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_d_840_; lean_object* v_b_841_; lean_object* v___y_842_; uint8_t v___x_848_; 
v___x_848_ = l_Lean_Expr_hasExprMVar(v_e_828_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v_e_828_);
v___x_849_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v_a_829_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_829_, v_e_828_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_box(0);
lean_inc_ref(v_e_828_);
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_a_829_, v_e_828_, v___x_853_);
switch(lean_obj_tag(v_e_828_))
{
case 11:
{
lean_object* v_struct_855_; 
v_struct_855_ = lean_ctor_get(v_e_828_, 2);
lean_inc_ref(v_struct_855_);
lean_dec_ref_known(v_e_828_, 3);
v_e_828_ = v_struct_855_;
v_a_829_ = v___x_854_;
goto _start;
}
case 7:
{
lean_object* v_binderType_857_; lean_object* v_body_858_; 
v_binderType_857_ = lean_ctor_get(v_e_828_, 1);
lean_inc_ref(v_binderType_857_);
v_body_858_ = lean_ctor_get(v_e_828_, 2);
lean_inc_ref(v_body_858_);
lean_dec_ref_known(v_e_828_, 3);
v_d_840_ = v_binderType_857_;
v_b_841_ = v_body_858_;
v___y_842_ = v___x_854_;
goto v___jp_839_;
}
case 6:
{
lean_object* v_binderType_859_; lean_object* v_body_860_; 
v_binderType_859_ = lean_ctor_get(v_e_828_, 1);
lean_inc_ref(v_binderType_859_);
v_body_860_ = lean_ctor_get(v_e_828_, 2);
lean_inc_ref(v_body_860_);
lean_dec_ref_known(v_e_828_, 3);
v_d_840_ = v_binderType_859_;
v_b_841_ = v_body_860_;
v___y_842_ = v___x_854_;
goto v___jp_839_;
}
case 8:
{
lean_object* v_type_861_; lean_object* v_value_862_; lean_object* v_body_863_; lean_object* v___x_864_; 
v_type_861_ = lean_ctor_get(v_e_828_, 1);
lean_inc_ref(v_type_861_);
v_value_862_ = lean_ctor_get(v_e_828_, 2);
lean_inc_ref(v_value_862_);
v_body_863_ = lean_ctor_get(v_e_828_, 3);
lean_inc_ref(v_body_863_);
lean_dec_ref_known(v_e_828_, 4);
v___x_864_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_827_, v_type_861_, v___x_854_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_fst_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
v_fst_866_ = lean_ctor_get(v_a_865_, 0);
if (lean_obj_tag(v_fst_866_) == 0)
{
lean_dec(v_a_865_);
lean_dec_ref(v_body_863_);
lean_dec_ref(v_value_862_);
return v___x_864_;
}
else
{
lean_object* v_snd_867_; lean_object* v___x_868_; 
lean_dec_ref_known(v___x_864_, 1);
v_snd_867_ = lean_ctor_get(v_a_865_, 1);
lean_inc(v_snd_867_);
lean_dec(v_a_865_);
v___x_868_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_827_, v_value_862_, v_snd_867_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_fst_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
v_fst_870_ = lean_ctor_get(v_a_869_, 0);
if (lean_obj_tag(v_fst_870_) == 0)
{
lean_dec(v_a_869_);
lean_dec_ref(v_body_863_);
return v___x_868_;
}
else
{
lean_object* v_snd_871_; 
lean_dec_ref_known(v___x_868_, 1);
v_snd_871_ = lean_ctor_get(v_a_869_, 1);
lean_inc(v_snd_871_);
lean_dec(v_a_869_);
v_e_828_ = v_body_863_;
v_a_829_ = v_snd_871_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_863_);
return v___x_868_;
}
}
}
else
{
lean_dec_ref(v_body_863_);
lean_dec_ref(v_value_862_);
return v___x_864_;
}
}
case 10:
{
lean_object* v_expr_873_; 
v_expr_873_ = lean_ctor_get(v_e_828_, 1);
lean_inc_ref(v_expr_873_);
lean_dec_ref_known(v_e_828_, 2);
v_e_828_ = v_expr_873_;
v_a_829_ = v___x_854_;
goto _start;
}
case 5:
{
lean_object* v_fn_875_; lean_object* v_arg_876_; lean_object* v___x_877_; 
v_fn_875_ = lean_ctor_get(v_e_828_, 0);
lean_inc_ref(v_fn_875_);
v_arg_876_ = lean_ctor_get(v_e_828_, 1);
lean_inc_ref(v_arg_876_);
lean_dec_ref_known(v_e_828_, 2);
v___x_877_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_827_, v_fn_875_, v___x_854_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v_fst_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
v_fst_879_ = lean_ctor_get(v_a_878_, 0);
if (lean_obj_tag(v_fst_879_) == 0)
{
lean_dec(v_a_878_);
lean_dec_ref(v_arg_876_);
return v___x_877_;
}
else
{
lean_object* v_snd_880_; 
lean_dec_ref_known(v___x_877_, 1);
v_snd_880_ = lean_ctor_get(v_a_878_, 1);
lean_inc(v_snd_880_);
lean_dec(v_a_878_);
v_e_828_ = v_arg_876_;
v_a_829_ = v_snd_880_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_876_);
return v___x_877_;
}
}
case 2:
{
lean_object* v_mvarId_882_; lean_object* v___x_883_; 
v_mvarId_882_ = lean_ctor_get(v_e_828_, 0);
lean_inc(v_mvarId_882_);
lean_dec_ref_known(v_e_828_, 1);
v___x_883_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_827_, v_mvarId_882_, v___x_854_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_883_;
}
default: 
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec_ref(v_e_828_);
v___x_884_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_854_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec_ref(v_e_828_);
v___x_887_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v_a_829_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
v___jp_839_:
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_827_, v_d_840_, v___y_842_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v_fst_845_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
v_fst_845_ = lean_ctor_get(v_a_844_, 0);
if (lean_obj_tag(v_fst_845_) == 0)
{
lean_dec(v_a_844_);
lean_dec_ref(v_b_841_);
return v___x_843_;
}
else
{
lean_object* v_snd_846_; 
lean_dec_ref_known(v___x_843_, 1);
v_snd_846_ = lean_ctor_get(v_a_844_, 1);
lean_inc(v_snd_846_);
lean_dec(v_a_844_);
v_e_828_ = v_b_841_;
v_a_829_ = v_snd_846_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_841_);
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object* v_mvarId_890_, lean_object* v_mvarId_x27_891_, lean_object* v_a_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_instBEqMVarId_beq(v_mvarId_890_, v_mvarId_x27_891_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_891_, v_a_892_, v___y_898_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_987_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_987_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_987_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_987_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_fst_908_; 
v_fst_908_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_fst_908_);
if (lean_obj_tag(v_fst_908_) == 0)
{
lean_object* v_snd_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_mvarId_x27_891_);
v_snd_909_ = lean_ctor_get(v_a_904_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_a_904_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v_a_904_, 0);
lean_dec(v_unused_928_);
v___x_911_ = v_a_904_;
v_isShared_912_ = v_isSharedCheck_927_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snd_909_);
lean_dec(v_a_904_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_927_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_926_; 
v_a_913_ = lean_ctor_get(v_fst_908_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_fst_908_);
if (v_isSharedCheck_926_ == 0)
{
v___x_915_ = v_fst_908_;
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v_fst_908_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_925_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_918_);
v___x_920_ = v___x_911_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_snd_909_);
v___x_920_ = v_reuseFailAlloc_924_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_920_);
v___x_922_ = v___x_906_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
else
{
lean_object* v_a_929_; 
lean_del_object(v___x_906_);
v_a_929_ = lean_ctor_get(v_fst_908_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v_fst_908_, 1);
if (lean_obj_tag(v_a_929_) == 0)
{
lean_object* v_snd_930_; lean_object* v___x_931_; 
v_snd_930_ = lean_ctor_get(v_a_904_, 1);
lean_inc(v_snd_930_);
lean_dec(v_a_904_);
v___x_931_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_891_, v_snd_930_, v___y_898_);
lean_dec(v_mvarId_x27_891_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_975_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_975_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_975_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_975_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_fst_936_; 
v_fst_936_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_fst_936_);
if (lean_obj_tag(v_fst_936_) == 0)
{
lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_955_; 
v_snd_937_ = lean_ctor_get(v_a_932_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_a_932_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_a_932_, 0);
lean_dec(v_unused_956_);
v___x_939_ = v_a_932_;
v_isShared_940_ = v_isSharedCheck_955_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_dec(v_a_932_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_955_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_954_; 
v_a_941_ = lean_ctor_get(v_fst_936_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_fst_936_);
if (v_isSharedCheck_954_ == 0)
{
v___x_943_ = v_fst_936_;
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v_fst_936_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_953_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_946_);
v___x_948_ = v___x_939_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_snd_937_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_948_);
v___x_950_ = v___x_934_;
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
}
}
else
{
lean_object* v_a_957_; 
v_a_957_ = lean_ctor_get(v_fst_936_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v_fst_936_, 1);
if (lean_obj_tag(v_a_957_) == 0)
{
lean_object* v_snd_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_969_; 
v_snd_958_ = lean_ctor_get(v_a_932_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_932_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v_a_932_, 0);
lean_dec(v_unused_970_);
v___x_960_ = v_a_932_;
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_snd_958_);
lean_dec(v_a_932_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_snd_958_);
v___x_964_ = v_reuseFailAlloc_968_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_964_);
v___x_966_ = v___x_934_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_val_971_; lean_object* v_snd_972_; lean_object* v_mvarIdPending_973_; 
lean_del_object(v___x_934_);
v_val_971_ = lean_ctor_get(v_a_957_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v_a_957_, 1);
v_snd_972_ = lean_ctor_get(v_a_932_, 1);
lean_inc(v_snd_972_);
lean_dec(v_a_932_);
v_mvarIdPending_973_ = lean_ctor_get(v_val_971_, 1);
lean_inc(v_mvarIdPending_973_);
lean_dec(v_val_971_);
v_mvarId_x27_891_ = v_mvarIdPending_973_;
v_a_892_ = v_snd_972_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
v_a_976_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_931_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_931_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_snd_984_; lean_object* v_val_985_; lean_object* v___x_986_; 
lean_dec(v_mvarId_x27_891_);
v_snd_984_ = lean_ctor_get(v_a_904_, 1);
lean_inc(v_snd_984_);
lean_dec(v_a_904_);
v_val_985_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v_a_929_, 1);
v___x_986_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_890_, v_val_985_, v_snd_984_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_986_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_mvarId_x27_891_);
v_a_988_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_903_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_903_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec(v_mvarId_x27_891_);
v___x_996_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1));
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_a_892_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_999_, lean_object* v_mvarId_x27_1000_, lean_object* v_a_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_999_, v_mvarId_x27_1000_, v_a_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v_mvarId_999_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_1012_, lean_object* v_e_1013_, lean_object* v_a_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1012_, v_e_1013_, v_a_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v_mvarId_1012_);
return v_res_1024_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_unsigned_to_nat(16u);
v___x_1027_ = lean_mk_array(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1031_, lean_object* v_e_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Lean_Expr_hasExprMVar(v_e_1032_);
if (v___x_1042_ == 0)
{
uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref(v_e_1032_);
v___x_1043_ = 1;
v___x_1044_ = lean_box(v___x_1043_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1047_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1031_, v_e_1032_, v___x_1046_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1062_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1062_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1062_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_fst_1052_; 
v_fst_1052_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_fst_1052_);
lean_dec(v_a_1048_);
if (lean_obj_tag(v_fst_1052_) == 0)
{
uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_dec_ref_known(v_fst_1052_, 1);
v___x_1053_ = 0;
v___x_1054_ = lean_box(v___x_1053_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1054_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
lean_dec_ref_known(v_fst_1052_, 1);
v___x_1058_ = lean_box(v___x_1042_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1058_);
v___x_1060_ = v___x_1050_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
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
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
v_a_1063_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1047_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1047_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1071_, lean_object* v_e_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1071_, v_e_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_mvarId_1071_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object* v_msgData_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v_env_1090_; lean_object* v___x_1091_; lean_object* v_mctx_1092_; lean_object* v_lctx_1093_; lean_object* v_options_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1089_ = lean_st_ref_get(v___y_1087_);
v_env_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_env_1090_);
lean_dec(v___x_1089_);
v___x_1091_ = lean_st_ref_get(v___y_1085_);
v_mctx_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_mctx_1092_);
lean_dec(v___x_1091_);
v_lctx_1093_ = lean_ctor_get(v___y_1084_, 2);
v_options_1094_ = lean_ctor_get(v___y_1086_, 2);
lean_inc_ref(v_options_1094_);
lean_inc_ref(v_lctx_1093_);
v___x_1095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1095_, 0, v_env_1090_);
lean_ctor_set(v___x_1095_, 1, v_mctx_1092_);
lean_ctor_set(v___x_1095_, 2, v_lctx_1093_);
lean_ctor_set(v___x_1095_, 3, v_options_1094_);
v___x_1096_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_msgData_1083_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object* v_msgData_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msgData_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v_msg_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_ref_1111_; lean_object* v___x_1112_; lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v_ref_1111_ = lean_ctor_get(v___y_1108_, 5);
v___x_1112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msg_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
lean_inc(v_ref_1111_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_ref_1111_);
lean_ctor_set(v___x_1117_, 1, v_a_1113_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set_tag(v___x_1115_, 1);
lean_ctor_set(v___x_1115_, 0, v___x_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v_msg_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_ks_1133_; lean_object* v_vs_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1158_; 
v_ks_1133_ = lean_ctor_get(v_x_1129_, 0);
v_vs_1134_ = lean_ctor_get(v_x_1129_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_x_1129_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1136_ = v_x_1129_;
v_isShared_1137_ = v_isSharedCheck_1158_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_vs_1134_);
lean_inc(v_ks_1133_);
lean_dec(v_x_1129_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1158_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_array_get_size(v_ks_1133_);
v___x_1139_ = lean_nat_dec_lt(v_x_1130_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_x_1130_);
v___x_1140_ = lean_array_push(v_ks_1133_, v_x_1131_);
v___x_1141_ = lean_array_push(v_vs_1134_, v_x_1132_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1141_);
lean_ctor_set(v___x_1136_, 0, v___x_1140_);
v___x_1143_ = v___x_1136_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
lean_object* v_k_x27_1145_; uint8_t v___x_1146_; 
v_k_x27_1145_ = lean_array_fget_borrowed(v_ks_1133_, v_x_1130_);
v___x_1146_ = l_Lean_instBEqMVarId_beq(v_x_1131_, v_k_x27_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1148_; 
if (v_isShared_1137_ == 0)
{
v___x_1148_ = v___x_1136_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_ks_1133_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_vs_1134_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_add(v_x_1130_, v___x_1149_);
lean_dec(v_x_1130_);
v_x_1129_ = v___x_1148_;
v_x_1130_ = v___x_1150_;
goto _start;
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_array_fset(v_ks_1133_, v_x_1130_, v_x_1131_);
v___x_1154_ = lean_array_fset(v_vs_1134_, v_x_1130_, v_x_1132_);
lean_dec(v_x_1130_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1154_);
lean_ctor_set(v___x_1136_, 0, v___x_1153_);
v___x_1156_ = v___x_1136_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1159_, lean_object* v_k_1160_, lean_object* v_v_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1159_, v___x_1162_, v_k_1160_, v_v_1161_);
return v___x_1163_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; 
v___x_1164_ = ((size_t)5ULL);
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_shift_left(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; 
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1169_ = lean_usize_sub(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(lean_object* v_x_1171_, size_t v_x_1172_, size_t v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
if (lean_obj_tag(v_x_1171_) == 0)
{
lean_object* v_es_1176_; size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; lean_object* v_j_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v_es_1176_ = lean_ctor_get(v_x_1171_, 0);
v___x_1177_ = ((size_t)5ULL);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1);
v___x_1180_ = lean_usize_land(v_x_1172_, v___x_1179_);
v_j_1181_ = lean_usize_to_nat(v___x_1180_);
v___x_1182_ = lean_array_get_size(v_es_1176_);
v___x_1183_ = lean_nat_dec_lt(v_j_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_dec(v_j_1181_);
lean_dec(v_x_1175_);
lean_dec(v_x_1174_);
return v_x_1171_;
}
else
{
lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1220_; 
lean_inc_ref(v_es_1176_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_x_1171_, 0);
lean_dec(v_unused_1221_);
v___x_1185_ = v_x_1171_;
v_isShared_1186_ = v_isSharedCheck_1220_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v_x_1171_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1220_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_v_1187_; lean_object* v___x_1188_; lean_object* v_xs_x27_1189_; lean_object* v___y_1191_; 
v_v_1187_ = lean_array_fget(v_es_1176_, v_j_1181_);
v___x_1188_ = lean_box(0);
v_xs_x27_1189_ = lean_array_fset(v_es_1176_, v_j_1181_, v___x_1188_);
switch(lean_obj_tag(v_v_1187_))
{
case 0:
{
lean_object* v_key_1196_; lean_object* v_val_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1207_; 
v_key_1196_ = lean_ctor_get(v_v_1187_, 0);
v_val_1197_ = lean_ctor_get(v_v_1187_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_v_1187_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1199_ = v_v_1187_;
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_val_1197_);
lean_inc(v_key_1196_);
lean_dec(v_v_1187_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
uint8_t v___x_1201_; 
v___x_1201_ = l_Lean_instBEqMVarId_beq(v_x_1174_, v_key_1196_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_del_object(v___x_1199_);
v___x_1202_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1196_, v_val_1197_, v_x_1174_, v_x_1175_);
v___x_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
v___y_1191_ = v___x_1203_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1205_; 
lean_dec(v_val_1197_);
lean_dec(v_key_1196_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v_x_1175_);
lean_ctor_set(v___x_1199_, 0, v_x_1174_);
v___x_1205_ = v___x_1199_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_x_1174_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_x_1175_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
v___y_1191_ = v___x_1205_;
goto v___jp_1190_;
}
}
}
}
case 1:
{
lean_object* v_node_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1218_; 
v_node_1208_ = lean_ctor_get(v_v_1187_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_v_1187_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1210_ = v_v_1187_;
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_node_1208_);
lean_dec(v_v_1187_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1212_ = lean_usize_shift_right(v_x_1172_, v___x_1177_);
v___x_1213_ = lean_usize_add(v_x_1173_, v___x_1178_);
v___x_1214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_node_1208_, v___x_1212_, v___x_1213_, v_x_1174_, v_x_1175_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1214_);
v___x_1216_ = v___x_1210_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
v___y_1191_ = v___x_1216_;
goto v___jp_1190_;
}
}
}
default: 
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_x_1174_);
lean_ctor_set(v___x_1219_, 1, v_x_1175_);
v___y_1191_ = v___x_1219_;
goto v___jp_1190_;
}
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_array_fset(v_xs_x27_1189_, v_j_1181_, v___y_1191_);
lean_dec(v_j_1181_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1192_);
v___x_1194_ = v___x_1185_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_object* v_ks_1222_; lean_object* v_vs_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1243_; 
v_ks_1222_ = lean_ctor_get(v_x_1171_, 0);
v_vs_1223_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1225_ = v_x_1171_;
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_vs_1223_);
lean_inc(v_ks_1222_);
lean_dec(v_x_1171_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_ks_1222_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_vs_1223_);
v___x_1228_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v_newNode_1229_; uint8_t v___y_1231_; size_t v___x_1237_; uint8_t v___x_1238_; 
v_newNode_1229_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1228_, v_x_1174_, v_x_1175_);
v___x_1237_ = ((size_t)7ULL);
v___x_1238_ = lean_usize_dec_le(v___x_1237_, v_x_1173_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1239_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1229_);
v___x_1240_ = lean_unsigned_to_nat(4u);
v___x_1241_ = lean_nat_dec_lt(v___x_1239_, v___x_1240_);
lean_dec(v___x_1239_);
v___y_1231_ = v___x_1241_;
goto v___jp_1230_;
}
else
{
v___y_1231_ = v___x_1238_;
goto v___jp_1230_;
}
v___jp_1230_:
{
if (v___y_1231_ == 0)
{
lean_object* v_ks_1232_; lean_object* v_vs_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_ks_1232_ = lean_ctor_get(v_newNode_1229_, 0);
lean_inc_ref(v_ks_1232_);
v_vs_1233_ = lean_ctor_get(v_newNode_1229_, 1);
lean_inc_ref(v_vs_1233_);
lean_dec_ref(v_newNode_1229_);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2);
v___x_1236_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1173_, v_ks_1232_, v_vs_1233_, v___x_1234_, v___x_1235_);
lean_dec_ref(v_vs_1233_);
lean_dec_ref(v_ks_1232_);
return v___x_1236_;
}
else
{
return v_newNode_1229_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1244_, lean_object* v_keys_1245_, lean_object* v_vals_1246_, lean_object* v_i_1247_, lean_object* v_entries_1248_){
_start:
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = lean_array_get_size(v_keys_1245_);
v___x_1250_ = lean_nat_dec_lt(v_i_1247_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_dec(v_i_1247_);
return v_entries_1248_;
}
else
{
lean_object* v_k_1251_; lean_object* v_v_1252_; uint64_t v___x_1253_; size_t v_h_1254_; size_t v___x_1255_; lean_object* v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v_h_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_k_1251_ = lean_array_fget_borrowed(v_keys_1245_, v_i_1247_);
v_v_1252_ = lean_array_fget_borrowed(v_vals_1246_, v_i_1247_);
v___x_1253_ = l_Lean_instHashableMVarId_hash(v_k_1251_);
v_h_1254_ = lean_uint64_to_usize(v___x_1253_);
v___x_1255_ = ((size_t)5ULL);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_sub(v_depth_1244_, v___x_1257_);
v___x_1259_ = lean_usize_mul(v___x_1255_, v___x_1258_);
v_h_1260_ = lean_usize_shift_right(v_h_1254_, v___x_1259_);
v___x_1261_ = lean_nat_add(v_i_1247_, v___x_1256_);
lean_dec(v_i_1247_);
lean_inc(v_v_1252_);
lean_inc(v_k_1251_);
v___x_1262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_entries_1248_, v_h_1260_, v_depth_1244_, v_k_1251_, v_v_1252_);
v_i_1247_ = v___x_1261_;
v_entries_1248_ = v___x_1262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1264_, lean_object* v_keys_1265_, lean_object* v_vals_1266_, lean_object* v_i_1267_, lean_object* v_entries_1268_){
_start:
{
size_t v_depth_boxed_1269_; lean_object* v_res_1270_; 
v_depth_boxed_1269_ = lean_unbox_usize(v_depth_1264_);
lean_dec(v_depth_1264_);
v_res_1270_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1269_, v_keys_1265_, v_vals_1266_, v_i_1267_, v_entries_1268_);
lean_dec_ref(v_vals_1266_);
lean_dec_ref(v_keys_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
size_t v_x_95755__boxed_1276_; size_t v_x_95756__boxed_1277_; lean_object* v_res_1278_; 
v_x_95755__boxed_1276_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_x_95756__boxed_1277_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_res_1278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1271_, v_x_95755__boxed_1276_, v_x_95756__boxed_1277_, v_x_1274_, v_x_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
uint64_t v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1282_ = l_Lean_instHashableMVarId_hash(v_x_1280_);
v___x_1283_ = lean_uint64_to_usize(v___x_1282_);
v___x_1284_ = ((size_t)1ULL);
v___x_1285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1279_, v___x_1283_, v___x_1284_, v_x_1280_, v_x_1281_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_1286_, lean_object* v_val_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v_mctx_1291_; lean_object* v_cache_1292_; lean_object* v_zetaDeltaFVarIds_1293_; lean_object* v_postponed_1294_; lean_object* v_diag_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1323_; 
v___x_1290_ = lean_st_ref_take(v___y_1288_);
v_mctx_1291_ = lean_ctor_get(v___x_1290_, 0);
v_cache_1292_ = lean_ctor_get(v___x_1290_, 1);
v_zetaDeltaFVarIds_1293_ = lean_ctor_get(v___x_1290_, 2);
v_postponed_1294_ = lean_ctor_get(v___x_1290_, 3);
v_diag_1295_ = lean_ctor_get(v___x_1290_, 4);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1297_ = v___x_1290_;
v_isShared_1298_ = v_isSharedCheck_1323_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_diag_1295_);
lean_inc(v_postponed_1294_);
lean_inc(v_zetaDeltaFVarIds_1293_);
lean_inc(v_cache_1292_);
lean_inc(v_mctx_1291_);
lean_dec(v___x_1290_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1323_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v_depth_1299_; lean_object* v_levelAssignDepth_1300_; lean_object* v_lmvarCounter_1301_; lean_object* v_mvarCounter_1302_; lean_object* v_lDecls_1303_; lean_object* v_decls_1304_; lean_object* v_userNames_1305_; lean_object* v_lAssignment_1306_; lean_object* v_eAssignment_1307_; lean_object* v_dAssignment_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1322_; 
v_depth_1299_ = lean_ctor_get(v_mctx_1291_, 0);
v_levelAssignDepth_1300_ = lean_ctor_get(v_mctx_1291_, 1);
v_lmvarCounter_1301_ = lean_ctor_get(v_mctx_1291_, 2);
v_mvarCounter_1302_ = lean_ctor_get(v_mctx_1291_, 3);
v_lDecls_1303_ = lean_ctor_get(v_mctx_1291_, 4);
v_decls_1304_ = lean_ctor_get(v_mctx_1291_, 5);
v_userNames_1305_ = lean_ctor_get(v_mctx_1291_, 6);
v_lAssignment_1306_ = lean_ctor_get(v_mctx_1291_, 7);
v_eAssignment_1307_ = lean_ctor_get(v_mctx_1291_, 8);
v_dAssignment_1308_ = lean_ctor_get(v_mctx_1291_, 9);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_mctx_1291_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1310_ = v_mctx_1291_;
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_dAssignment_1308_);
lean_inc(v_eAssignment_1307_);
lean_inc(v_lAssignment_1306_);
lean_inc(v_userNames_1305_);
lean_inc(v_decls_1304_);
lean_inc(v_lDecls_1303_);
lean_inc(v_mvarCounter_1302_);
lean_inc(v_lmvarCounter_1301_);
lean_inc(v_levelAssignDepth_1300_);
lean_inc(v_depth_1299_);
lean_dec(v_mctx_1291_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1322_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_1307_, v_mvarId_1286_, v_val_1287_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 8, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_depth_1299_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_levelAssignDepth_1300_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_lmvarCounter_1301_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_mvarCounter_1302_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_lDecls_1303_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_decls_1304_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_userNames_1305_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_lAssignment_1306_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1321_, 9, v_dAssignment_1308_);
v___x_1314_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1314_);
v___x_1316_ = v___x_1297_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_cache_1292_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_zetaDeltaFVarIds_1293_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_postponed_1294_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v_diag_1295_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_st_ref_set(v___y_1288_, v___x_1316_);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_1324_, lean_object* v_val_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_1324_, v_val_1325_, v___y_1326_);
lean_dec(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1337_, uint8_t v_suppressElabErrors_1338_, lean_object* v_x_1339_){
_start:
{
if (lean_obj_tag(v_x_1339_) == 1)
{
lean_object* v_pre_1340_; 
v_pre_1340_ = lean_ctor_get(v_x_1339_, 0);
switch(lean_obj_tag(v_pre_1340_))
{
case 1:
{
lean_object* v_pre_1341_; 
v_pre_1341_ = lean_ctor_get(v_pre_1340_, 0);
switch(lean_obj_tag(v_pre_1341_))
{
case 0:
{
lean_object* v_str_1342_; lean_object* v_str_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v_str_1342_ = lean_ctor_get(v_x_1339_, 1);
v_str_1343_ = lean_ctor_get(v_pre_1340_, 1);
v___x_1344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1345_ = lean_string_dec_eq(v_str_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1347_ = lean_string_dec_eq(v_str_1343_, v___x_1346_);
if (v___x_1347_ == 0)
{
return v___y_1337_;
}
else
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1349_ = lean_string_dec_eq(v_str_1342_, v___x_1348_);
if (v___x_1349_ == 0)
{
return v___y_1337_;
}
else
{
return v_suppressElabErrors_1338_;
}
}
}
else
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1351_ = lean_string_dec_eq(v_str_1342_, v___x_1350_);
if (v___x_1351_ == 0)
{
return v___y_1337_;
}
else
{
return v_suppressElabErrors_1338_;
}
}
}
case 1:
{
lean_object* v_pre_1352_; 
v_pre_1352_ = lean_ctor_get(v_pre_1341_, 0);
if (lean_obj_tag(v_pre_1352_) == 0)
{
lean_object* v_str_1353_; lean_object* v_str_1354_; lean_object* v_str_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_str_1353_ = lean_ctor_get(v_x_1339_, 1);
v_str_1354_ = lean_ctor_get(v_pre_1340_, 1);
v_str_1355_ = lean_ctor_get(v_pre_1341_, 1);
v___x_1356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1357_ = lean_string_dec_eq(v_str_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
return v___y_1337_;
}
else
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1359_ = lean_string_dec_eq(v_str_1354_, v___x_1358_);
if (v___x_1359_ == 0)
{
return v___y_1337_;
}
else
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1361_ = lean_string_dec_eq(v_str_1353_, v___x_1360_);
if (v___x_1361_ == 0)
{
return v___y_1337_;
}
else
{
return v_suppressElabErrors_1338_;
}
}
}
}
else
{
return v___y_1337_;
}
}
default: 
{
return v___y_1337_;
}
}
}
case 0:
{
lean_object* v_str_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_str_1362_ = lean_ctor_get(v_x_1339_, 1);
v___x_1363_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1364_ = lean_string_dec_eq(v_str_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
return v___y_1337_;
}
else
{
return v_suppressElabErrors_1338_;
}
}
default: 
{
return v___y_1337_;
}
}
}
else
{
return v___y_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1365_, lean_object* v_suppressElabErrors_1366_, lean_object* v_x_1367_){
_start:
{
uint8_t v___y_95990__boxed_1368_; uint8_t v_suppressElabErrors_boxed_1369_; uint8_t v_res_1370_; lean_object* v_r_1371_; 
v___y_95990__boxed_1368_ = lean_unbox(v___y_1365_);
v_suppressElabErrors_boxed_1369_ = lean_unbox(v_suppressElabErrors_1366_);
v_res_1370_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v___y_95990__boxed_1368_, v_suppressElabErrors_boxed_1369_, v_x_1367_);
lean_dec(v_x_1367_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1373_, lean_object* v_msgData_1374_, uint8_t v_severity_1375_, uint8_t v_isSilent_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; uint8_t v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1444_; uint8_t v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; uint8_t v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1455_; uint8_t v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1459_; lean_object* v___y_1460_; uint8_t v___y_1461_; uint8_t v___x_1466_; lean_object* v___y_1468_; uint8_t v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; uint8_t v___y_1473_; uint8_t v___y_1474_; uint8_t v___y_1476_; uint8_t v___x_1491_; 
v___x_1466_ = 2;
v___x_1491_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1375_, v___x_1466_);
if (v___x_1491_ == 0)
{
v___y_1476_ = v___x_1491_;
goto v___jp_1475_;
}
else
{
uint8_t v___x_1492_; 
lean_inc_ref(v_msgData_1374_);
v___x_1492_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1374_);
v___y_1476_ = v___x_1492_;
goto v___jp_1475_;
}
v___jp_1382_:
{
lean_object* v___x_1392_; lean_object* v_currNamespace_1393_; lean_object* v_openDecls_1394_; lean_object* v_env_1395_; lean_object* v_nextMacroScope_1396_; lean_object* v_ngen_1397_; lean_object* v_auxDeclNGen_1398_; lean_object* v_traceState_1399_; lean_object* v_cache_1400_; lean_object* v_messages_1401_; lean_object* v_infoState_1402_; lean_object* v_snapshotTasks_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1417_; 
v___x_1392_ = lean_st_ref_take(v___y_1391_);
v_currNamespace_1393_ = lean_ctor_get(v___y_1390_, 6);
v_openDecls_1394_ = lean_ctor_get(v___y_1390_, 7);
v_env_1395_ = lean_ctor_get(v___x_1392_, 0);
v_nextMacroScope_1396_ = lean_ctor_get(v___x_1392_, 1);
v_ngen_1397_ = lean_ctor_get(v___x_1392_, 2);
v_auxDeclNGen_1398_ = lean_ctor_get(v___x_1392_, 3);
v_traceState_1399_ = lean_ctor_get(v___x_1392_, 4);
v_cache_1400_ = lean_ctor_get(v___x_1392_, 5);
v_messages_1401_ = lean_ctor_get(v___x_1392_, 6);
v_infoState_1402_ = lean_ctor_get(v___x_1392_, 7);
v_snapshotTasks_1403_ = lean_ctor_get(v___x_1392_, 8);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1405_ = v___x_1392_;
v_isShared_1406_ = v_isSharedCheck_1417_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_snapshotTasks_1403_);
lean_inc(v_infoState_1402_);
lean_inc(v_messages_1401_);
lean_inc(v_cache_1400_);
lean_inc(v_traceState_1399_);
lean_inc(v_auxDeclNGen_1398_);
lean_inc(v_ngen_1397_);
lean_inc(v_nextMacroScope_1396_);
lean_inc(v_env_1395_);
lean_dec(v___x_1392_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1417_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc(v_openDecls_1394_);
lean_inc(v_currNamespace_1393_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_currNamespace_1393_);
lean_ctor_set(v___x_1407_, 1, v_openDecls_1394_);
v___x_1408_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v___y_1384_);
lean_inc_ref(v___y_1386_);
lean_inc_ref(v___y_1385_);
v___x_1409_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1409_, 0, v___y_1385_);
lean_ctor_set(v___x_1409_, 1, v___y_1383_);
lean_ctor_set(v___x_1409_, 2, v___y_1387_);
lean_ctor_set(v___x_1409_, 3, v___y_1386_);
lean_ctor_set(v___x_1409_, 4, v___x_1408_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*5, v___y_1389_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*5 + 1, v___y_1388_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*5 + 2, v_isSilent_1376_);
v___x_1410_ = l_Lean_MessageLog_add(v___x_1409_, v_messages_1401_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 6, v___x_1410_);
v___x_1412_ = v___x_1405_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_env_1395_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_nextMacroScope_1396_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_ngen_1397_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_auxDeclNGen_1398_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_traceState_1399_);
lean_ctor_set(v_reuseFailAlloc_1416_, 5, v_cache_1400_);
lean_ctor_set(v_reuseFailAlloc_1416_, 6, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1416_, 7, v_infoState_1402_);
lean_ctor_set(v_reuseFailAlloc_1416_, 8, v_snapshotTasks_1403_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_st_ref_set(v___y_1391_, v___x_1412_);
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
}
v___jp_1418_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1442_; 
v___x_1427_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1374_);
v___x_1428_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v___x_1427_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_inc_ref_n(v___y_1424_, 2);
v___x_1433_ = l_Lean_FileMap_toPosition(v___y_1424_, v___y_1422_);
lean_dec(v___y_1422_);
v___x_1434_ = l_Lean_FileMap_toPosition(v___y_1424_, v___y_1426_);
lean_dec(v___y_1426_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1420_ == 0)
{
lean_del_object(v___x_1431_);
lean_dec_ref(v___y_1419_);
v___y_1383_ = v___x_1433_;
v___y_1384_ = v_a_1429_;
v___y_1385_ = v___y_1421_;
v___y_1386_ = v___x_1436_;
v___y_1387_ = v___x_1435_;
v___y_1388_ = v___y_1423_;
v___y_1389_ = v___y_1425_;
v___y_1390_ = v___y_1379_;
v___y_1391_ = v___y_1380_;
goto v___jp_1382_;
}
else
{
uint8_t v___x_1437_; 
lean_inc(v_a_1429_);
v___x_1437_ = l_Lean_MessageData_hasTag(v___y_1419_, v_a_1429_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec_ref_known(v___x_1435_, 1);
lean_dec_ref(v___x_1433_);
lean_dec(v_a_1429_);
v___x_1438_ = lean_box(0);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1438_);
v___x_1440_ = v___x_1431_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_del_object(v___x_1431_);
v___y_1383_ = v___x_1433_;
v___y_1384_ = v_a_1429_;
v___y_1385_ = v___y_1421_;
v___y_1386_ = v___x_1436_;
v___y_1387_ = v___x_1435_;
v___y_1388_ = v___y_1423_;
v___y_1389_ = v___y_1425_;
v___y_1390_ = v___y_1379_;
v___y_1391_ = v___y_1380_;
goto v___jp_1382_;
}
}
}
}
v___jp_1443_:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Syntax_getTailPos_x3f(v___y_1447_, v___y_1450_);
lean_dec(v___y_1447_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_inc(v___y_1451_);
v___y_1419_ = v___y_1444_;
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___y_1446_;
v___y_1422_ = v___y_1451_;
v___y_1423_ = v___y_1449_;
v___y_1424_ = v___y_1448_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v___y_1451_;
goto v___jp_1418_;
}
else
{
lean_object* v_val_1453_; 
v_val_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v___x_1452_, 1);
v___y_1419_ = v___y_1444_;
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___y_1446_;
v___y_1422_ = v___y_1451_;
v___y_1423_ = v___y_1449_;
v___y_1424_ = v___y_1448_;
v___y_1425_ = v___y_1450_;
v___y_1426_ = v_val_1453_;
goto v___jp_1418_;
}
}
v___jp_1454_:
{
lean_object* v_ref_1462_; lean_object* v___x_1463_; 
v_ref_1462_ = l_Lean_replaceRef(v_ref_1373_, v___y_1460_);
v___x_1463_ = l_Lean_Syntax_getPos_x3f(v_ref_1462_, v___y_1459_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___y_1444_ = v___y_1455_;
v___y_1445_ = v___y_1456_;
v___y_1446_ = v___y_1457_;
v___y_1447_ = v_ref_1462_;
v___y_1448_ = v___y_1458_;
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1459_;
v___y_1451_ = v___x_1464_;
goto v___jp_1443_;
}
else
{
lean_object* v_val_1465_; 
v_val_1465_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v___x_1463_, 1);
v___y_1444_ = v___y_1455_;
v___y_1445_ = v___y_1456_;
v___y_1446_ = v___y_1457_;
v___y_1447_ = v_ref_1462_;
v___y_1448_ = v___y_1458_;
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1459_;
v___y_1451_ = v_val_1465_;
goto v___jp_1443_;
}
}
v___jp_1467_:
{
if (v___y_1474_ == 0)
{
v___y_1455_ = v___y_1468_;
v___y_1456_ = v___y_1469_;
v___y_1457_ = v___y_1470_;
v___y_1458_ = v___y_1471_;
v___y_1459_ = v___y_1473_;
v___y_1460_ = v___y_1472_;
v___y_1461_ = v_severity_1375_;
goto v___jp_1454_;
}
else
{
v___y_1455_ = v___y_1468_;
v___y_1456_ = v___y_1469_;
v___y_1457_ = v___y_1470_;
v___y_1458_ = v___y_1471_;
v___y_1459_ = v___y_1473_;
v___y_1460_ = v___y_1472_;
v___y_1461_ = v___x_1466_;
goto v___jp_1454_;
}
}
v___jp_1475_:
{
if (v___y_1476_ == 0)
{
lean_object* v_fileName_1477_; lean_object* v_fileMap_1478_; lean_object* v_options_1479_; lean_object* v_ref_1480_; uint8_t v_suppressElabErrors_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___f_1484_; uint8_t v___x_1485_; uint8_t v___x_1486_; 
v_fileName_1477_ = lean_ctor_get(v___y_1379_, 0);
v_fileMap_1478_ = lean_ctor_get(v___y_1379_, 1);
v_options_1479_ = lean_ctor_get(v___y_1379_, 2);
v_ref_1480_ = lean_ctor_get(v___y_1379_, 5);
v_suppressElabErrors_1481_ = lean_ctor_get_uint8(v___y_1379_, sizeof(void*)*14 + 1);
v___x_1482_ = lean_box(v___y_1476_);
v___x_1483_ = lean_box(v_suppressElabErrors_1481_);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1484_, 0, v___x_1482_);
lean_closure_set(v___f_1484_, 1, v___x_1483_);
v___x_1485_ = 1;
v___x_1486_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1375_, v___x_1485_);
if (v___x_1486_ == 0)
{
v___y_1468_ = v___f_1484_;
v___y_1469_ = v_suppressElabErrors_1481_;
v___y_1470_ = v_fileName_1477_;
v___y_1471_ = v_fileMap_1478_;
v___y_1472_ = v_ref_1480_;
v___y_1473_ = v___y_1476_;
v___y_1474_ = v___x_1486_;
goto v___jp_1467_;
}
else
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = l_Lean_warningAsError;
v___x_1488_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_1479_, v___x_1487_);
v___y_1468_ = v___f_1484_;
v___y_1469_ = v_suppressElabErrors_1481_;
v___y_1470_ = v_fileName_1477_;
v___y_1471_ = v_fileMap_1478_;
v___y_1472_ = v_ref_1480_;
v___y_1473_ = v___y_1476_;
v___y_1474_ = v___x_1488_;
goto v___jp_1467_;
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref(v_msgData_1374_);
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1493_, lean_object* v_msgData_1494_, lean_object* v_severity_1495_, lean_object* v_isSilent_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_severity_boxed_1502_; uint8_t v_isSilent_boxed_1503_; lean_object* v_res_1504_; 
v_severity_boxed_1502_ = lean_unbox(v_severity_1495_);
v_isSilent_boxed_1503_ = lean_unbox(v_isSilent_1496_);
v_res_1504_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1493_, v_msgData_1494_, v_severity_boxed_1502_, v_isSilent_boxed_1503_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v_ref_1493_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(lean_object* v_ref_1505_, lean_object* v_msgData_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = 1;
v___x_1517_ = 0;
v___x_1518_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1505_, v_msgData_1506_, v___x_1516_, v___x_1517_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(lean_object* v_ref_1519_, lean_object* v_msgData_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_ref_1519_, v_msgData_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v_ref_1519_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_linterOption_1537_, lean_object* v_stx_1538_, lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_name_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1567_; 
v_name_1549_ = lean_ctor_get(v_linterOption_1537_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_linterOption_1537_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v_linterOption_1537_, 1);
lean_dec(v_unused_1568_);
v___x_1551_ = v_linterOption_1537_;
v_isShared_1552_ = v_isSharedCheck_1567_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_name_1549_);
lean_dec(v_linterOption_1537_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1567_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1553_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
lean_inc(v_name_1549_);
v___x_1554_ = l_Lean_MessageData_ofName(v_name_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 7);
lean_ctor_set(v___x_1551_, 1, v___x_1554_);
lean_ctor_set(v___x_1551_, 0, v___x_1553_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v_disable_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1557_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v_disable_1559_ = l_Lean_MessageData_note(v___x_1558_);
v___x_1560_ = l_Lean_Linter_linterMessageTag;
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_msg_1539_);
lean_ctor_set(v___x_1561_, 1, v_disable_1559_);
v___x_1562_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_name_1549_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
lean_inc(v_stx_1538_);
v___x_1564_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_stx_1538_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_stx_1538_, v___x_1564_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v_stx_1538_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_linterOption_1569_, lean_object* v_stx_1570_, lean_object* v_msg_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_linterOption_1569_, v_stx_1570_, v_msg_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object* v___y_1582_, lean_object* v_mkInfoTree_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v_a_1591_, lean_object* v_a_x3f_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v_infoState_1595_; lean_object* v_trees_1596_; lean_object* v___x_1597_; 
v___x_1594_ = lean_st_ref_get(v___y_1582_);
v_infoState_1595_ = lean_ctor_get(v___x_1594_, 7);
lean_inc_ref(v_infoState_1595_);
lean_dec(v___x_1594_);
v_trees_1596_ = lean_ctor_get(v_infoState_1595_, 2);
lean_inc_ref(v_trees_1596_);
lean_dec_ref(v_infoState_1595_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
lean_inc(v___y_1585_);
lean_inc_ref(v___y_1584_);
v___x_1597_ = lean_apply_10(v_mkInfoTree_1583_, v_trees_1596_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1582_, lean_box(0));
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1636_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1636_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1636_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v_infoState_1603_; lean_object* v_env_1604_; lean_object* v_nextMacroScope_1605_; lean_object* v_ngen_1606_; lean_object* v_auxDeclNGen_1607_; lean_object* v_traceState_1608_; lean_object* v_cache_1609_; lean_object* v_messages_1610_; lean_object* v_snapshotTasks_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1635_; 
v___x_1602_ = lean_st_ref_take(v___y_1582_);
v_infoState_1603_ = lean_ctor_get(v___x_1602_, 7);
v_env_1604_ = lean_ctor_get(v___x_1602_, 0);
v_nextMacroScope_1605_ = lean_ctor_get(v___x_1602_, 1);
v_ngen_1606_ = lean_ctor_get(v___x_1602_, 2);
v_auxDeclNGen_1607_ = lean_ctor_get(v___x_1602_, 3);
v_traceState_1608_ = lean_ctor_get(v___x_1602_, 4);
v_cache_1609_ = lean_ctor_get(v___x_1602_, 5);
v_messages_1610_ = lean_ctor_get(v___x_1602_, 6);
v_snapshotTasks_1611_ = lean_ctor_get(v___x_1602_, 8);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1613_ = v___x_1602_;
v_isShared_1614_ = v_isSharedCheck_1635_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_snapshotTasks_1611_);
lean_inc(v_infoState_1603_);
lean_inc(v_messages_1610_);
lean_inc(v_cache_1609_);
lean_inc(v_traceState_1608_);
lean_inc(v_auxDeclNGen_1607_);
lean_inc(v_ngen_1606_);
lean_inc(v_nextMacroScope_1605_);
lean_inc(v_env_1604_);
lean_dec(v___x_1602_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1635_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
uint8_t v_enabled_1615_; lean_object* v_assignment_1616_; lean_object* v_lazyAssignment_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1633_; 
v_enabled_1615_ = lean_ctor_get_uint8(v_infoState_1603_, sizeof(void*)*3);
v_assignment_1616_ = lean_ctor_get(v_infoState_1603_, 0);
v_lazyAssignment_1617_ = lean_ctor_get(v_infoState_1603_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_infoState_1603_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v_infoState_1603_, 2);
lean_dec(v_unused_1634_);
v___x_1619_ = v_infoState_1603_;
v_isShared_1620_ = v_isSharedCheck_1633_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_lazyAssignment_1617_);
lean_inc(v_assignment_1616_);
lean_dec(v_infoState_1603_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1633_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = l_Lean_PersistentArray_push___redArg(v_a_1591_, v_a_1598_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 2, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_assignment_1616_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_lazyAssignment_1617_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v___x_1621_);
lean_ctor_set_uint8(v_reuseFailAlloc_1632_, sizeof(void*)*3, v_enabled_1615_);
v___x_1623_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 7, v___x_1623_);
v___x_1625_ = v___x_1613_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_env_1604_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_nextMacroScope_1605_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_ngen_1606_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_auxDeclNGen_1607_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_traceState_1608_);
lean_ctor_set(v_reuseFailAlloc_1631_, 5, v_cache_1609_);
lean_ctor_set(v_reuseFailAlloc_1631_, 6, v_messages_1610_);
lean_ctor_set(v_reuseFailAlloc_1631_, 7, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1631_, 8, v_snapshotTasks_1611_);
v___x_1625_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1626_ = lean_st_ref_set(v___y_1582_, v___x_1625_);
v___x_1627_ = lean_box(0);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1627_);
v___x_1629_ = v___x_1600_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec_ref(v_a_1591_);
v_a_1637_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1597_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1597_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object* v___y_1645_, lean_object* v_mkInfoTree_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v_a_1654_, lean_object* v_a_x3f_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1645_, v_mkInfoTree_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v_a_1654_, v_a_x3f_1655_);
lean_dec(v_a_x3f_1655_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1645_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object* v_x_1658_, lean_object* v_mkInfoTree_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v_infoState_1670_; uint8_t v_enabled_1671_; 
v___x_1669_ = lean_st_ref_get(v___y_1667_);
v_infoState_1670_ = lean_ctor_get(v___x_1669_, 7);
lean_inc_ref(v_infoState_1670_);
lean_dec(v___x_1669_);
v_enabled_1671_ = lean_ctor_get_uint8(v_infoState_1670_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1670_);
if (v_enabled_1671_ == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v_mkInfoTree_1659_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
v___x_1672_ = lean_apply_9(v_x_1658_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, lean_box(0));
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v_r_1675_; 
v___x_1673_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1667_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
v_r_1675_ = lean_apply_9(v_x_1658_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, lean_box(0));
if (lean_obj_tag(v_r_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1700_; 
v_a_1676_ = lean_ctor_get(v_r_1675_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_r_1675_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1678_ = v_r_1675_;
v_isShared_1679_ = v_isSharedCheck_1700_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v_r_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1700_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
lean_inc(v_a_1676_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 1);
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1667_, v_mkInfoTree_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v_a_1674_, v___x_1681_);
lean_dec_ref(v___x_1681_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; 
v_unused_1690_ = lean_ctor_get(v___x_1682_, 0);
lean_dec(v_unused_1690_);
v___x_1684_ = v___x_1682_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_dec(v___x_1682_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 0, v_a_1676_);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1676_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec(v_a_1676_);
v_a_1691_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1682_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1682_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_a_1701_ = lean_ctor_get(v_r_1675_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v_r_1675_, 1);
v___x_1702_ = lean_box(0);
v___x_1703_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1667_, v_mkInfoTree_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v_a_1674_, v___x_1702_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1703_, 0);
lean_dec(v_unused_1711_);
v___x_1705_ = v___x_1703_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v___x_1703_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 1);
lean_ctor_set(v___x_1705_, 0, v_a_1701_);
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1701_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_a_1701_);
v_a_1712_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1703_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1703_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object* v_x_1720_, lean_object* v_mkInfoTree_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_1720_, v_mkInfoTree_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v_env_1736_; lean_object* v___x_1737_; lean_object* v_toEnvExtension_1738_; lean_object* v_asyncMode_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v_merged_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
v___x_1735_ = lean_st_ref_get(v___y_1733_);
v_env_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc_ref(v_env_1736_);
lean_dec(v___x_1735_);
v___x_1737_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1738_ = lean_ctor_get(v___x_1737_, 0);
v_asyncMode_1739_ = lean_ctor_get(v_toEnvExtension_1738_, 2);
v___x_1740_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1741_ = lean_box(0);
v___x_1742_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1740_, v___x_1737_, v_env_1736_, v_asyncMode_1739_, v___x_1741_);
v_merged_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v___x_1742_, 1);
lean_dec(v_unused_1752_);
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_merged_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_merged_1743_);
lean_ctor_set(v___x_1745_, 0, v_o_1732_);
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_o_1732_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_merged_1743_);
v___x_1748_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_1753_, v___y_1754_);
lean_dec(v___y_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_options_1766_; lean_object* v___x_1767_; 
v_options_1766_ = lean_ctor_get(v___y_1763_, 2);
lean_inc_ref(v_options_1766_);
v___x_1767_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_1766_, v___y_1764_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_usingArg_1799_, lean_object* v_snd_1800_, uint8_t v___x_1801_, uint8_t v___x_1802_, lean_object* v___x_1803_, uint8_t v_useReducible_1804_, uint8_t v___x_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_simprocs_1808_, lean_object* v_discharge_x3f_1809_, lean_object* v_snd_1810_, lean_object* v___x_1811_, lean_object* v___f_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; 
if (lean_obj_tag(v_usingArg_1799_) == 1)
{
lean_object* v_val_2003_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___x_2055_; lean_object* v_infoState_2056_; uint8_t v_enabled_2057_; 
v_val_2003_ = lean_ctor_get(v_usingArg_1799_, 0);
lean_inc(v_val_2003_);
lean_dec_ref_known(v_usingArg_1799_, 1);
v___x_2055_ = lean_st_ref_get(v___y_1820_);
v_infoState_2056_ = lean_ctor_get(v___x_2055_, 7);
lean_inc_ref(v_infoState_2056_);
lean_dec(v___x_2055_);
v_enabled_2057_ = lean_ctor_get_uint8(v_infoState_2056_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2056_);
if (v_enabled_2057_ == 0)
{
lean_dec_ref(v___f_1812_);
v___y_2005_ = v___y_1813_;
v___y_2006_ = v___y_1814_;
v___y_2007_ = v___y_1815_;
v___y_2008_ = v___y_1816_;
v___y_2009_ = v___y_1817_;
v___y_2010_ = v___y_1818_;
v___y_2011_ = v___y_1819_;
v___y_2012_ = v___y_1820_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2058_; lean_object* v_a_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; 
v___x_2058_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1820_);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2058_);
v___f_2060_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2060_, 0, v_a_2059_);
v___x_2061_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_2060_, v___f_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_dec_ref_known(v___x_2061_, 1);
v___y_2005_ = v___y_1813_;
v___y_2006_ = v___y_1814_;
v___y_2007_ = v___y_1815_;
v___y_2008_ = v___y_1816_;
v___y_2009_ = v___y_1817_;
v___y_2010_ = v___y_1818_;
v___y_2011_ = v___y_1819_;
v___y_2012_ = v___y_1820_;
goto v___jp_2004_;
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_val_2003_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
v___jp_2004_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_st_ref_get(v___y_2010_);
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Lean_Elab_Tactic_elabTerm(v_val_2003_, v___x_2014_, v___x_1801_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_n(v_a_2016_, 2);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_1800_, v_a_2016_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_mctx_2018_; lean_object* v_a_2019_; uint8_t v___x_2020_; 
v_mctx_2018_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_mctx_2018_);
lean_dec(v___x_2013_);
v_a_2019_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2020_ = lean_unbox(v_a_2019_);
lean_dec(v_a_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_mctx_2018_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
v___x_2021_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
v___x_2022_ = l_Lean_indentExpr(v_a_2016_);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = l_Lean_Expr_mvar___override(v_snd_1800_);
v___x_2027_ = l_Lean_MessageData_ofExpr(v___x_2026_);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2025_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_2028_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
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
else
{
lean_object* v_mvarCounter_2038_; 
v_mvarCounter_2038_ = lean_ctor_get(v_mctx_2018_, 3);
lean_inc(v_mvarCounter_2038_);
lean_dec_ref(v_mctx_2018_);
lean_inc(v_a_2016_);
v___y_1887_ = v_a_2016_;
v___y_1888_ = v_mvarCounter_2038_;
v___y_1889_ = v___x_2014_;
v___y_1890_ = v_a_2016_;
v___y_1891_ = v___x_2014_;
v___y_1892_ = v___y_2005_;
v___y_1893_ = v___y_2006_;
v___y_1894_ = v___y_2007_;
v___y_1895_ = v___y_2008_;
v___y_1896_ = v___y_2009_;
v___y_1897_ = v___y_2010_;
v___y_1898_ = v___y_2011_;
v___y_1899_ = v___y_2012_;
goto v___jp_1886_;
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_2016_);
lean_dec(v___x_2013_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_2039_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2017_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2017_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v___x_2013_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_2047_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2015_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2015_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
else
{
lean_object* v_lctx_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec_ref(v___f_1812_);
lean_dec_ref(v___x_1803_);
lean_dec(v_usingArg_1799_);
v_lctx_2070_ = lean_ctor_get(v___y_1817_, 2);
v___x_2071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13));
v___x_2072_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2070_, v___x_2071_);
if (lean_obj_tag(v___x_2072_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_val_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_val_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = l_Lean_LocalDecl_fvarId(v_val_2073_);
lean_dec(v_val_2073_);
v___x_2075_ = lean_mk_empty_array_with_capacity(v___x_1806_);
v___x_2076_ = lean_array_push(v___x_2075_, v___x_2074_);
lean_inc_ref(v_snd_1810_);
v___x_2077_ = l_Lean_Meta_simpGoal(v_snd_1800_, v___x_1807_, v_simprocs_1808_, v_discharge_x3f_1809_, v___x_1802_, v___x_2076_, v_snd_1810_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2106_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2106_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2106_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_fst_2082_; 
v_fst_2082_ = lean_ctor_get(v_a_2078_, 0);
if (lean_obj_tag(v_fst_2082_) == 1)
{
lean_object* v_val_2083_; lean_object* v_snd_2084_; lean_object* v_snd_2085_; lean_object* v___x_2086_; 
lean_del_object(v___x_2080_);
lean_dec_ref(v_snd_1810_);
v_val_2083_ = lean_ctor_get(v_fst_2082_, 0);
lean_inc(v_val_2083_);
v_snd_2084_ = lean_ctor_get(v_a_2078_, 1);
lean_inc(v_snd_2084_);
lean_dec(v_a_2078_);
v_snd_2085_ = lean_ctor_get(v_val_2083_, 1);
lean_inc(v_snd_2085_);
lean_dec(v_val_2083_);
v___x_2086_ = l_Lean_MVarId_assumption(v_snd_2085_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v___x_2086_, 0);
lean_dec(v_unused_2094_);
v___x_2088_ = v___x_2086_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_dec(v___x_2086_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v_snd_2084_);
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_snd_2084_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_snd_2084_);
v_a_2095_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2086_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2086_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v___x_2104_; 
lean_dec(v_a_2078_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v_snd_1810_);
v___x_2104_ = v___x_2080_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_snd_1810_);
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
lean_dec_ref(v_snd_1810_);
v_a_2107_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2077_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2077_);
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
else
{
lean_object* v___x_2115_; 
lean_dec(v___x_2072_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
v___x_2115_ = l_Lean_MVarId_assumption(v_snd_1800_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v___x_2115_, 0);
lean_dec(v_unused_2123_);
v___x_2117_ = v___x_2115_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_dec(v___x_2115_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v_snd_1810_);
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_snd_1810_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_snd_1810_);
v_a_2124_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2115_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2115_);
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
v___jp_1822_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v___x_1826_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_1800_, v___y_1824_, v___y_1825_);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v___x_1826_, 0);
lean_dec(v_unused_1834_);
v___x_1828_ = v___x_1826_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_dec(v___x_1826_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___y_1823_);
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___y_1823_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
v___jp_1835_:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Core_mkFreshUserName(v___y_1846_, v___y_1844_, v___y_1841_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc_n(v_a_1853_, 2);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = l_Lean_MVarId_rename(v___y_1842_, v___y_1851_, v_a_1853_, v___y_1848_, v___y_1850_, v___y_1844_, v___y_1841_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; lean_object* v___x_1861_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc_n(v_a_1855_, 2);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = lean_box(v___x_1801_);
v___x_1857_ = lean_box(v___x_1802_);
v___x_1858_ = lean_box(v_useReducible_1804_);
v___x_1859_ = lean_box(v___x_1805_);
v___f_1860_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 19, 10);
lean_closure_set(v___f_1860_, 0, v_a_1855_);
lean_closure_set(v___f_1860_, 1, v_a_1853_);
lean_closure_set(v___f_1860_, 2, v___x_1856_);
lean_closure_set(v___f_1860_, 3, v___x_1857_);
lean_closure_set(v___f_1860_, 4, v___y_1836_);
lean_closure_set(v___f_1860_, 5, v___y_1837_);
lean_closure_set(v___f_1860_, 6, v___x_1803_);
lean_closure_set(v___f_1860_, 7, v___y_1838_);
lean_closure_set(v___f_1860_, 8, v___x_1858_);
lean_closure_set(v___f_1860_, 9, v___x_1859_);
v___x_1861_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1855_, v___f_1860_, v___y_1843_, v___y_1840_, v___y_1845_, v___y_1847_, v___y_1848_, v___y_1850_, v___y_1844_, v___y_1841_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref_known(v___x_1861_, 1);
v___y_1823_ = v___y_1839_;
v___y_1824_ = v___y_1849_;
v___y_1825_ = v___y_1850_;
goto v___jp_1822_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v___y_1849_);
lean_dec_ref(v___y_1839_);
lean_dec(v_snd_1800_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_a_1853_);
lean_dec_ref(v___y_1849_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_1870_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1854_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1854_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_1878_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1852_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1852_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
v___jp_1886_:
{
lean_object* v___x_1900_; 
lean_inc(v_snd_1800_);
v___x_1900_ = l_Lean_MVarId_getType(v_snd_1800_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
lean_inc(v_snd_1800_);
v___x_1902_ = l_Lean_MVarId_getTag(v_snd_1800_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1901_, v_a_1903_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = l_Lean_Expr_mvarId_x21(v_a_1905_);
v___x_1907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1));
lean_inc_ref(v___y_1890_);
v___x_1908_ = l_Lean_MVarId_note(v___x_1906_, v___x_1907_, v___y_1890_, v___y_1891_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v_fst_1910_; lean_object* v_snd_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1970_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v_fst_1910_ = lean_ctor_get(v_a_1909_, 0);
v_snd_1911_ = lean_ctor_get(v_a_1909_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_a_1909_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1913_ = v_a_1909_;
v_isShared_1914_ = v_isSharedCheck_1970_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_snd_1911_);
lean_inc(v_fst_1910_);
lean_dec(v_a_1909_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1970_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_mk_empty_array_with_capacity(v___x_1806_);
lean_inc(v_fst_1910_);
v___x_1916_ = lean_array_push(v___x_1915_, v_fst_1910_);
v___x_1917_ = l_Lean_Meta_simpGoal(v_snd_1911_, v___x_1807_, v_simprocs_1808_, v_discharge_x3f_1809_, v___x_1802_, v___x_1916_, v_snd_1810_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_fst_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v_fst_1919_ = lean_ctor_get(v_a_1918_, 0);
if (lean_obj_tag(v_fst_1919_) == 0)
{
lean_object* v_snd_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_fst_1910_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___x_1803_);
v_snd_1920_ = lean_ctor_get(v_a_1918_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_a_1918_);
if (v_isSharedCheck_1953_ == 0)
{
lean_object* v_unused_1954_; 
v_unused_1954_ = lean_ctor_get(v_a_1918_, 0);
lean_dec(v_unused_1954_);
v___x_1922_ = v_a_1918_;
v_isShared_1923_ = v_isSharedCheck_1953_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_snd_1920_);
lean_dec(v_a_1918_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1953_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v_a_1925_; uint8_t v___x_1926_; 
v___x_1924_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
v___x_1926_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1925_);
lean_dec(v_a_1925_);
if (v___x_1926_ == 0)
{
lean_del_object(v___x_1922_);
lean_del_object(v___x_1913_);
lean_dec_ref(v___y_1890_);
v___y_1823_ = v_snd_1920_;
v___y_1824_ = v_a_1905_;
v___y_1825_ = v___y_1897_;
goto v___jp_1822_;
}
else
{
if (lean_obj_tag(v___y_1890_) == 1)
{
lean_object* v_fvarId_1927_; lean_object* v_lctx_1928_; lean_object* v___x_1929_; 
v_fvarId_1927_ = lean_ctor_get(v___y_1890_, 0);
v_lctx_1928_ = lean_ctor_get(v___y_1896_, 2);
lean_inc(v_fvarId_1927_);
lean_inc_ref(v_lctx_1928_);
v___x_1929_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1928_, v_fvarId_1927_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_dec_ref_known(v___y_1890_, 1);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1913_);
v___y_1823_ = v_snd_1920_;
v___y_1824_ = v_a_1905_;
v___y_1825_ = v___y_1897_;
goto v___jp_1822_;
}
else
{
lean_dec_ref_known(v___x_1929_, 1);
if (v___x_1805_ == 0)
{
lean_dec_ref_known(v___y_1890_, 1);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1913_);
v___y_1823_ = v_snd_1920_;
v___y_1824_ = v_a_1905_;
v___y_1825_ = v___y_1897_;
goto v___jp_1822_;
}
else
{
lean_object* v_ref_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v_ref_1930_ = lean_ctor_get(v___y_1898_, 5);
v___x_1931_ = l_linter_unnecessarySimpa;
v___x_1932_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_1933_ = l_Lean_MessageData_ofExpr(v___y_1890_);
lean_inc_ref(v___x_1933_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 7);
lean_ctor_set(v___x_1922_, 1, v___x_1933_);
lean_ctor_set(v___x_1922_, 0, v___x_1932_);
v___x_1935_ = v___x_1922_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 7);
lean_ctor_set(v___x_1913_, 1, v___x_1936_);
lean_ctor_set(v___x_1913_, 0, v___x_1935_);
v___x_1938_ = v___x_1913_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1933_);
v___x_1940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
lean_inc(v_ref_1930_);
v___x_1942_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_1931_, v_ref_1930_, v___x_1941_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_dec_ref_known(v___x_1942_, 1);
v___y_1823_ = v_snd_1920_;
v___y_1824_ = v_a_1905_;
v___y_1825_ = v___y_1897_;
goto v___jp_1822_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_snd_1920_);
lean_dec(v_a_1905_);
lean_dec(v_snd_1800_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
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
lean_del_object(v___x_1922_);
lean_del_object(v___x_1913_);
lean_dec_ref(v___y_1890_);
v___y_1823_ = v_snd_1920_;
v___y_1824_ = v_a_1905_;
v___y_1825_ = v___y_1897_;
goto v___jp_1822_;
}
}
}
}
else
{
lean_object* v_val_1955_; lean_object* v_snd_1956_; lean_object* v_fst_1957_; lean_object* v_snd_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
lean_del_object(v___x_1913_);
lean_dec_ref(v___y_1890_);
v_val_1955_ = lean_ctor_get(v_fst_1919_, 0);
lean_inc(v_val_1955_);
v_snd_1956_ = lean_ctor_get(v_a_1918_, 1);
lean_inc(v_snd_1956_);
lean_dec(v_a_1918_);
v_fst_1957_ = lean_ctor_get(v_val_1955_, 0);
lean_inc(v_fst_1957_);
v_snd_1958_ = lean_ctor_get(v_val_1955_, 1);
lean_inc(v_snd_1958_);
lean_dec(v_val_1955_);
v___x_1959_ = lean_array_get_size(v_fst_1957_);
v___x_1960_ = lean_nat_dec_lt(v___x_1811_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_dec(v_fst_1957_);
v___y_1836_ = v___y_1887_;
v___y_1837_ = v___y_1888_;
v___y_1838_ = v___y_1889_;
v___y_1839_ = v_snd_1956_;
v___y_1840_ = v___y_1893_;
v___y_1841_ = v___y_1899_;
v___y_1842_ = v_snd_1958_;
v___y_1843_ = v___y_1892_;
v___y_1844_ = v___y_1898_;
v___y_1845_ = v___y_1894_;
v___y_1846_ = v___x_1907_;
v___y_1847_ = v___y_1895_;
v___y_1848_ = v___y_1896_;
v___y_1849_ = v_a_1905_;
v___y_1850_ = v___y_1897_;
v___y_1851_ = v_fst_1910_;
goto v___jp_1835_;
}
else
{
lean_object* v___x_1961_; 
lean_dec(v_fst_1910_);
v___x_1961_ = lean_array_fget(v_fst_1957_, v___x_1811_);
lean_dec(v_fst_1957_);
v___y_1836_ = v___y_1887_;
v___y_1837_ = v___y_1888_;
v___y_1838_ = v___y_1889_;
v___y_1839_ = v_snd_1956_;
v___y_1840_ = v___y_1893_;
v___y_1841_ = v___y_1899_;
v___y_1842_ = v_snd_1958_;
v___y_1843_ = v___y_1892_;
v___y_1844_ = v___y_1898_;
v___y_1845_ = v___y_1894_;
v___y_1846_ = v___x_1907_;
v___y_1847_ = v___y_1895_;
v___y_1848_ = v___y_1896_;
v___y_1849_ = v_a_1905_;
v___y_1850_ = v___y_1897_;
v___y_1851_ = v___x_1961_;
goto v___jp_1835_;
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_del_object(v___x_1913_);
lean_dec(v_fst_1910_);
lean_dec(v_a_1905_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_1962_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1917_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1917_);
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
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_a_1905_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_1971_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1908_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1908_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_1979_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1904_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1904_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_a_1901_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_1987_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1902_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1902_);
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
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_snd_1810_);
lean_dec(v_discharge_x3f_1809_);
lean_dec_ref(v_simprocs_1808_);
lean_dec_ref(v___x_1807_);
lean_dec_ref(v___x_1803_);
lean_dec(v_snd_1800_);
v_a_1995_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1900_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1900_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2132_ = _args[0];
lean_object* v_snd_2133_ = _args[1];
lean_object* v___x_2134_ = _args[2];
lean_object* v___x_2135_ = _args[3];
lean_object* v___x_2136_ = _args[4];
lean_object* v_useReducible_2137_ = _args[5];
lean_object* v___x_2138_ = _args[6];
lean_object* v___x_2139_ = _args[7];
lean_object* v___x_2140_ = _args[8];
lean_object* v_simprocs_2141_ = _args[9];
lean_object* v_discharge_x3f_2142_ = _args[10];
lean_object* v_snd_2143_ = _args[11];
lean_object* v___x_2144_ = _args[12];
lean_object* v___f_2145_ = _args[13];
lean_object* v___y_2146_ = _args[14];
lean_object* v___y_2147_ = _args[15];
lean_object* v___y_2148_ = _args[16];
lean_object* v___y_2149_ = _args[17];
lean_object* v___y_2150_ = _args[18];
lean_object* v___y_2151_ = _args[19];
lean_object* v___y_2152_ = _args[20];
lean_object* v___y_2153_ = _args[21];
lean_object* v___y_2154_ = _args[22];
_start:
{
uint8_t v___x_96725__boxed_2155_; uint8_t v___x_96726__boxed_2156_; uint8_t v_useReducible_boxed_2157_; uint8_t v___x_96728__boxed_2158_; lean_object* v_res_2159_; 
v___x_96725__boxed_2155_ = lean_unbox(v___x_2134_);
v___x_96726__boxed_2156_ = lean_unbox(v___x_2135_);
v_useReducible_boxed_2157_ = lean_unbox(v_useReducible_2137_);
v___x_96728__boxed_2158_ = lean_unbox(v___x_2138_);
v_res_2159_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2132_, v_snd_2133_, v___x_96725__boxed_2155_, v___x_96726__boxed_2156_, v___x_2136_, v_useReducible_boxed_2157_, v___x_96728__boxed_2158_, v___x_2139_, v___x_2140_, v_simprocs_2141_, v_discharge_x3f_2142_, v_snd_2143_, v___x_2144_, v___f_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___x_2144_);
lean_dec(v___x_2139_);
return v_res_2159_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2160_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_unsigned_to_nat(32u);
v___x_2164_ = lean_mk_empty_array_with_capacity(v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2170_ = l_Lean_MessageData_ofFormat(v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v___x_2171_, lean_object* v_tk_2172_, lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v___x_2175_, lean_object* v_simprocs_2176_, uint8_t v___x_2177_, lean_object* v_usingArg_2178_, uint8_t v___x_2179_, lean_object* v___x_2180_, uint8_t v_useReducible_2181_, uint8_t v___x_2182_, lean_object* v___x_2183_, lean_object* v_usingTk_x3f_2184_, lean_object* v_discharge_x3f_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___y_2196_; 
if (lean_obj_tag(v_usingTk_x3f_2184_) == 0)
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_box(0);
v___y_2196_ = v___x_2301_;
goto v___jp_2195_;
}
else
{
lean_object* v_val_2302_; 
v_val_2302_ = lean_ctor_get(v_usingTk_x3f_2184_, 0);
lean_inc(v_val_2302_);
lean_dec_ref_known(v_usingTk_x3f_2184_, 1);
v___y_2196_ = v_val_2302_;
goto v___jp_2195_;
}
v___jp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2197_ = lean_mk_empty_array_with_capacity(v___x_2171_);
v___x_2198_ = lean_array_push(v___x_2197_, v_tk_2172_);
v___x_2199_ = lean_array_push(v___x_2198_, v___y_2196_);
v___x_2200_ = lean_box(2);
v___x_2201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___x_2173_);
lean_ctor_set(v___x_2201_, 2, v___x_2199_);
v___x_2202_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2201_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2187_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; size_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = lean_mk_empty_array_with_capacity(v___x_2174_);
v___x_2207_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
lean_inc_n(v___x_2174_, 3);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2174_);
v___x_2209_ = lean_unsigned_to_nat(32u);
v___x_2210_ = lean_mk_empty_array_with_capacity(v___x_2209_);
v___x_2211_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
v___x_2212_ = ((size_t)5ULL);
v___x_2213_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2210_);
lean_ctor_set(v___x_2213_, 2, v___x_2174_);
lean_ctor_set(v___x_2213_, 3, v___x_2174_);
lean_ctor_set_usize(v___x_2213_, 4, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2207_);
lean_ctor_set(v___x_2214_, 1, v___x_2207_);
lean_ctor_set(v___x_2214_, 2, v___x_2207_);
lean_ctor_set(v___x_2214_, 3, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2208_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
lean_inc_ref(v___x_2215_);
lean_inc(v_discharge_x3f_2185_);
lean_inc_ref(v_simprocs_2176_);
lean_inc_ref(v___x_2175_);
v___x_2216_ = l_Lean_Meta_simpGoal(v_a_2205_, v___x_2175_, v_simprocs_2176_, v_discharge_x3f_2185_, v___x_2177_, v___x_2206_, v___x_2215_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_fst_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v_fst_2218_ = lean_ctor_get(v_a_2217_, 0);
if (lean_obj_tag(v_fst_2218_) == 1)
{
lean_object* v_val_2219_; lean_object* v_snd_2220_; lean_object* v_snd_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref_known(v___x_2215_, 2);
v_val_2219_ = lean_ctor_get(v_fst_2218_, 0);
lean_inc(v_val_2219_);
v_snd_2220_ = lean_ctor_get(v_a_2217_, 1);
lean_inc(v_snd_2220_);
lean_dec(v_a_2217_);
v_snd_2221_ = lean_ctor_get(v_val_2219_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_val_2219_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v_val_2219_, 0);
lean_dec(v_unused_2246_);
v___x_2223_ = v_val_2219_;
v_isShared_2224_ = v_isSharedCheck_2245_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_snd_2221_);
lean_dec(v_val_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2245_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_box(0);
lean_inc(v_snd_2221_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 1, v___x_2225_);
lean_ctor_set(v___x_2223_, 0, v_snd_2221_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_snd_2221_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2227_, v___y_2187_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___y_2234_; lean_object* v___x_2235_; 
lean_dec_ref_known(v___x_2228_, 1);
v___f_2229_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2229_, 0, v_a_2203_);
v___x_2230_ = lean_box(v___x_2177_);
v___x_2231_ = lean_box(v___x_2179_);
v___x_2232_ = lean_box(v_useReducible_2181_);
v___x_2233_ = lean_box(v___x_2182_);
lean_inc(v_snd_2221_);
v___y_2234_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 23, 14);
lean_closure_set(v___y_2234_, 0, v_usingArg_2178_);
lean_closure_set(v___y_2234_, 1, v_snd_2221_);
lean_closure_set(v___y_2234_, 2, v___x_2230_);
lean_closure_set(v___y_2234_, 3, v___x_2231_);
lean_closure_set(v___y_2234_, 4, v___x_2180_);
lean_closure_set(v___y_2234_, 5, v___x_2232_);
lean_closure_set(v___y_2234_, 6, v___x_2233_);
lean_closure_set(v___y_2234_, 7, v___x_2183_);
lean_closure_set(v___y_2234_, 8, v___x_2175_);
lean_closure_set(v___y_2234_, 9, v_simprocs_2176_);
lean_closure_set(v___y_2234_, 10, v_discharge_x3f_2185_);
lean_closure_set(v___y_2234_, 11, v_snd_2220_);
lean_closure_set(v___y_2234_, 12, v___x_2174_);
lean_closure_set(v___y_2234_, 13, v___f_2229_);
v___x_2235_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_2221_, v___y_2234_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2235_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_snd_2221_);
lean_dec(v_snd_2220_);
lean_dec(v_a_2203_);
lean_dec(v_discharge_x3f_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2180_);
lean_dec(v_usingArg_2178_);
lean_dec_ref(v_simprocs_2176_);
lean_dec_ref(v___x_2175_);
lean_dec(v___x_2174_);
v_a_2236_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2228_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2228_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
}
else
{
lean_object* v___x_2247_; lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_a_2217_);
lean_dec(v_a_2203_);
lean_dec(v_discharge_x3f_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2180_);
lean_dec(v_usingArg_2178_);
lean_dec_ref(v_simprocs_2176_);
lean_dec_ref(v___x_2175_);
lean_dec(v___x_2174_);
v___x_2247_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2276_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2276_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
uint8_t v___x_2252_; 
v___x_2252_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2248_);
lean_dec(v_a_2248_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2254_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2215_);
v___x_2254_ = v___x_2250_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2215_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
else
{
lean_object* v_ref_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
lean_del_object(v___x_2250_);
v_ref_2256_ = lean_ctor_get(v___y_2192_, 5);
v___x_2257_ = l_linter_unnecessarySimpa;
v___x_2258_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
lean_inc(v_ref_2256_);
v___x_2259_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2257_, v_ref_2256_, v___x_2258_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; 
v_unused_2267_ = lean_ctor_get(v___x_2259_, 0);
lean_dec(v_unused_2267_);
v___x_2261_ = v___x_2259_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_dec(v___x_2259_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2215_);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2215_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref_known(v___x_2215_, 2);
v_a_2268_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2259_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2259_);
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
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref_known(v___x_2215_, 2);
lean_dec(v_a_2203_);
lean_dec(v_discharge_x3f_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2180_);
lean_dec(v_usingArg_2178_);
lean_dec_ref(v_simprocs_2176_);
lean_dec_ref(v___x_2175_);
lean_dec(v___x_2174_);
v_a_2277_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2216_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2216_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_a_2203_);
lean_dec(v_discharge_x3f_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2180_);
lean_dec(v_usingArg_2178_);
lean_dec_ref(v_simprocs_2176_);
lean_dec_ref(v___x_2175_);
lean_dec(v___x_2174_);
v_a_2285_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2204_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2204_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_discharge_x3f_2185_);
lean_dec(v___x_2183_);
lean_dec_ref(v___x_2180_);
lean_dec(v_usingArg_2178_);
lean_dec_ref(v_simprocs_2176_);
lean_dec_ref(v___x_2175_);
lean_dec(v___x_2174_);
v_a_2293_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2202_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2202_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v___x_2303_ = _args[0];
lean_object* v_tk_2304_ = _args[1];
lean_object* v___x_2305_ = _args[2];
lean_object* v___x_2306_ = _args[3];
lean_object* v___x_2307_ = _args[4];
lean_object* v_simprocs_2308_ = _args[5];
lean_object* v___x_2309_ = _args[6];
lean_object* v_usingArg_2310_ = _args[7];
lean_object* v___x_2311_ = _args[8];
lean_object* v___x_2312_ = _args[9];
lean_object* v_useReducible_2313_ = _args[10];
lean_object* v___x_2314_ = _args[11];
lean_object* v___x_2315_ = _args[12];
lean_object* v_usingTk_x3f_2316_ = _args[13];
lean_object* v_discharge_x3f_2317_ = _args[14];
lean_object* v___y_2318_ = _args[15];
lean_object* v___y_2319_ = _args[16];
lean_object* v___y_2320_ = _args[17];
lean_object* v___y_2321_ = _args[18];
lean_object* v___y_2322_ = _args[19];
lean_object* v___y_2323_ = _args[20];
lean_object* v___y_2324_ = _args[21];
lean_object* v___y_2325_ = _args[22];
lean_object* v___y_2326_ = _args[23];
_start:
{
uint8_t v___x_97449__boxed_2327_; uint8_t v___x_97450__boxed_2328_; uint8_t v_useReducible_boxed_2329_; uint8_t v___x_97452__boxed_2330_; lean_object* v_res_2331_; 
v___x_97449__boxed_2327_ = lean_unbox(v___x_2309_);
v___x_97450__boxed_2328_ = lean_unbox(v___x_2311_);
v_useReducible_boxed_2329_ = lean_unbox(v_useReducible_2313_);
v___x_97452__boxed_2330_ = lean_unbox(v___x_2314_);
v_res_2331_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2303_, v_tk_2304_, v___x_2305_, v___x_2306_, v___x_2307_, v_simprocs_2308_, v___x_97449__boxed_2327_, v_usingArg_2310_, v___x_97450__boxed_2328_, v___x_2312_, v_useReducible_boxed_2329_, v___x_97452__boxed_2330_, v___x_2315_, v_usingTk_x3f_2316_, v_discharge_x3f_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___x_2303_);
return v_res_2331_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2340_ = lean_unsigned_to_nat(38u);
v___x_2341_ = lean_unsigned_to_nat(126u);
v___x_2342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2344_ = l_mkPanicMessageWithDecl(v___x_2343_, v___x_2342_, v___x_2341_, v___x_2340_, v___x_2339_);
return v___x_2344_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Array_mkArray0(lean_box(0));
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2362_ = lean_unsigned_to_nat(15u);
v___x_2363_ = lean_unsigned_to_nat(127u);
v___x_2364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2366_ = l_mkPanicMessageWithDecl(v___x_2365_, v___x_2364_, v___x_2363_, v___x_2362_, v___x_2361_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2368_, lean_object* v___x_2369_, lean_object* v___x_2370_, lean_object* v___x_2371_, lean_object* v___x_2372_, uint8_t v___x_2373_, lean_object* v___x_2374_, lean_object* v___x_2375_, uint8_t v_useReducible_2376_, lean_object* v___f_2377_, lean_object* v___x_2378_, lean_object* v___x_2379_, lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v___x_2382_, lean_object* v___x_2383_, lean_object* v_usingArg_2384_, lean_object* v___x_2385_, uint8_t v___x_2386_, lean_object* v_usingTk_x3f_2387_, lean_object* v_squeeze_2388_, lean_object* v_unfold_2389_, lean_object* v_args_2390_, lean_object* v_only_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___y_2403_; lean_object* v___y_2407_; lean_object* v_stx_2408_; lean_object* v___y_2409_; lean_object* v_ref_2410_; lean_object* v___y_2411_; lean_object* v___y_2430_; lean_object* v_stx_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v_options_2456_; lean_object* v_ref_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; uint8_t v___y_2872_; lean_object* v_args_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; uint8_t v___y_2911_; lean_object* v___y_2912_; lean_object* v_only_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2941_; uint8_t v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_3001_; lean_object* v___y_3002_; uint8_t v___y_3003_; lean_object* v___y_3014_; uint8_t v___y_3015_; lean_object* v___y_3016_; uint8_t v___y_3017_; lean_object* v___y_3019_; lean_object* v___y_3020_; uint8_t v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3091_; 
v_options_2456_ = lean_ctor_get(v___y_2399_, 2);
v_ref_2457_ = lean_ctor_get(v___y_2399_, 5);
v___x_2458_ = 0;
v___x_2459_ = l_Lean_SourceInfo_fromRef(v_ref_2457_, v___x_2458_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7));
lean_inc_ref(v___x_2371_);
lean_inc_ref(v___x_2370_);
lean_inc_ref(v___x_2369_);
v___x_2461_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2460_);
lean_inc(v___x_2459_);
v___x_2462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2459_);
lean_ctor_set(v___x_2462_, 1, v___x_2460_);
v___x_2463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_2464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_2392_) == 0)
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_3091_ = v___x_3100_;
goto v___jp_3090_;
}
else
{
lean_object* v_val_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_val_3101_ = lean_ctor_get(v___y_2392_, 0);
lean_inc(v_val_3101_);
lean_dec_ref_known(v___y_2392_, 1);
v___x_3102_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___x_3103_ = lean_array_push(v___x_3102_, v_val_3101_);
v___y_3091_ = v___x_3103_;
goto v___jp_3090_;
}
v___jp_2402_:
{
lean_object* v_diag_2404_; lean_object* v___x_2405_; 
v_diag_2404_ = lean_ctor_get(v___y_2403_, 1);
lean_inc_ref(v_diag_2404_);
lean_dec_ref(v___y_2403_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v_diag_2404_);
return v___x_2405_;
}
v___jp_2406_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2412_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1));
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v_stx_2408_);
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
lean_ctor_set(v___x_2415_, 2, v___x_2414_);
lean_ctor_set(v___x_2415_, 3, v___x_2414_);
lean_ctor_set(v___x_2415_, 4, v___x_2414_);
lean_ctor_set(v___x_2415_, 5, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_ref_2410_);
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2));
v___x_2418_ = 4;
v___x_2419_ = l_Lean_MessageData_nil;
v___x_2420_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2368_, v___x_2415_, v___x_2416_, v___x_2417_, v___x_2414_, v___x_2418_, v___x_2419_, v___y_2409_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2409_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_dec_ref_known(v___x_2420_, 1);
v___y_2403_ = v___y_2407_;
goto v___jp_2402_;
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___y_2407_);
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
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
v___jp_2429_:
{
lean_object* v_ref_2434_; 
v_ref_2434_ = lean_ctor_get(v___y_2432_, 5);
lean_inc(v_ref_2434_);
v___y_2407_ = v___y_2430_;
v_stx_2408_ = v_stx_2431_;
v___y_2409_ = v___y_2432_;
v_ref_2410_ = v_ref_2434_;
v___y_2411_ = v___y_2433_;
goto v___jp_2406_;
}
v___jp_2435_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
v___x_2446_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2445_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___y_2430_ = v___y_2436_;
v_stx_2431_ = v_a_2447_;
v___y_2432_ = v___y_2443_;
v___y_2433_ = v___y_2444_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___y_2436_);
lean_dec(v_tk_2368_);
v_a_2448_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2446_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
v___jp_2465_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = l_Array_append___redArg(v___x_2464_, v___y_2476_);
lean_dec_ref(v___y_2476_);
lean_inc_n(v___y_2468_, 2);
v___x_2478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2478_, 0, v___y_2468_);
lean_ctor_set(v___x_2478_, 1, v___x_2463_);
lean_ctor_set(v___x_2478_, 2, v___x_2477_);
v___x_2479_ = l_Lean_Syntax_node5(v___y_2468_, v___x_2374_, v___y_2472_, v___y_2474_, v___y_2470_, v___y_2471_, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node2(v___y_2468_, v___y_2475_, v___y_2466_, v___x_2479_);
v___y_2430_ = v___y_2473_;
v_stx_2431_ = v___x_2480_;
v___y_2432_ = v___y_2469_;
v___y_2433_ = v___y_2467_;
goto v___jp_2429_;
}
v___jp_2481_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = l_Array_append___redArg(v___x_2464_, v___y_2492_);
lean_dec_ref(v___y_2492_);
lean_inc(v___y_2484_);
v___x_2494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2494_, 0, v___y_2484_);
lean_ctor_set(v___x_2494_, 1, v___x_2463_);
lean_ctor_set(v___x_2494_, 2, v___x_2493_);
if (lean_obj_tag(v___y_2485_) == 1)
{
lean_object* v_val_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_dec(v___x_2372_);
v_val_2495_ = lean_ctor_get(v___y_2485_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v___y_2485_, 1);
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2484_);
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___y_2484_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Array_mkArray2___redArg(v___x_2497_, v_val_2495_);
v___y_2466_ = v___y_2482_;
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2484_;
v___y_2469_ = v___y_2486_;
v___y_2470_ = v___y_2487_;
v___y_2471_ = v___x_2494_;
v___y_2472_ = v___y_2488_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2489_;
v___y_2475_ = v___y_2491_;
v___y_2476_ = v___x_2498_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2499_; 
lean_dec(v___y_2485_);
v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2466_ = v___y_2482_;
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2484_;
v___y_2469_ = v___y_2486_;
v___y_2470_ = v___y_2487_;
v___y_2471_ = v___x_2494_;
v___y_2472_ = v___y_2488_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2489_;
v___y_2475_ = v___y_2491_;
v___y_2476_ = v___x_2499_;
goto v___jp_2465_;
}
}
v___jp_2500_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = l_Array_append___redArg(v___x_2464_, v___y_2511_);
lean_dec_ref(v___y_2511_);
lean_inc(v___y_2503_);
v___x_2513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2503_);
lean_ctor_set(v___x_2513_, 1, v___x_2463_);
lean_ctor_set(v___x_2513_, 2, v___x_2512_);
if (lean_obj_tag(v___y_2506_) == 1)
{
lean_object* v_val_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_val_2514_ = lean_ctor_get(v___y_2506_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v___y_2506_, 1);
v___x_2515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2516_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2515_);
v___x_2517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2503_, 4);
v___x_2518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___y_2503_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Array_append___redArg(v___x_2464_, v_val_2514_);
lean_dec(v_val_2514_);
v___x_2520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2520_, 0, v___y_2503_);
lean_ctor_set(v___x_2520_, 1, v___x_2463_);
lean_ctor_set(v___x_2520_, 2, v___x_2519_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___y_2503_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_Syntax_node3(v___y_2503_, v___x_2516_, v___x_2518_, v___x_2520_, v___x_2522_);
v___x_2524_ = l_Array_mkArray1___redArg(v___x_2523_);
v___y_2482_ = v___y_2501_;
v___y_2483_ = v___y_2502_;
v___y_2484_ = v___y_2503_;
v___y_2485_ = v___y_2505_;
v___y_2486_ = v___y_2504_;
v___y_2487_ = v___x_2513_;
v___y_2488_ = v___y_2507_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2508_;
v___y_2491_ = v___y_2510_;
v___y_2492_ = v___x_2524_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2525_; 
lean_dec(v___y_2506_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2525_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2482_ = v___y_2501_;
v___y_2483_ = v___y_2502_;
v___y_2484_ = v___y_2503_;
v___y_2485_ = v___y_2505_;
v___y_2486_ = v___y_2504_;
v___y_2487_ = v___x_2513_;
v___y_2488_ = v___y_2507_;
v___y_2489_ = v___y_2509_;
v___y_2490_ = v___y_2508_;
v___y_2491_ = v___y_2510_;
v___y_2492_ = v___x_2525_;
goto v___jp_2481_;
}
}
v___jp_2526_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = l_Array_append___redArg(v___x_2464_, v___y_2537_);
lean_dec_ref(v___y_2537_);
lean_inc(v___y_2529_);
v___x_2539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2539_, 0, v___y_2529_);
lean_ctor_set(v___x_2539_, 1, v___x_2463_);
lean_ctor_set(v___x_2539_, 2, v___x_2538_);
if (lean_obj_tag(v___y_2533_) == 1)
{
lean_object* v_val_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_val_2540_ = lean_ctor_get(v___y_2533_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v___y_2533_, 1);
v___x_2541_ = l_Lean_SourceInfo_fromRef(v_val_2540_, v___x_2373_);
lean_dec(v_val_2540_);
v___x_2542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = l_Array_mkArray1___redArg(v___x_2543_);
v___y_2501_ = v___y_2527_;
v___y_2502_ = v___y_2528_;
v___y_2503_ = v___y_2529_;
v___y_2504_ = v___y_2531_;
v___y_2505_ = v___y_2530_;
v___y_2506_ = v___y_2532_;
v___y_2507_ = v___y_2534_;
v___y_2508_ = v___y_2535_;
v___y_2509_ = v___x_2539_;
v___y_2510_ = v___y_2536_;
v___y_2511_ = v___x_2544_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2545_; 
lean_dec(v___y_2533_);
v___x_2545_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2501_ = v___y_2527_;
v___y_2502_ = v___y_2528_;
v___y_2503_ = v___y_2529_;
v___y_2504_ = v___y_2531_;
v___y_2505_ = v___y_2530_;
v___y_2506_ = v___y_2532_;
v___y_2507_ = v___y_2534_;
v___y_2508_ = v___y_2535_;
v___y_2509_ = v___x_2539_;
v___y_2510_ = v___y_2536_;
v___y_2511_ = v___x_2545_;
goto v___jp_2500_;
}
}
v___jp_2546_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2561_ = l_Array_append___redArg(v___x_2464_, v___y_2560_);
lean_dec_ref(v___y_2560_);
lean_inc_n(v___y_2556_, 3);
v___x_2562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2562_, 0, v___y_2556_);
lean_ctor_set(v___x_2562_, 1, v___x_2463_);
lean_ctor_set(v___x_2562_, 2, v___x_2561_);
v___x_2563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___y_2556_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node6(v___y_2556_, v___y_2549_, v___y_2553_, v___y_2557_, v___y_2558_, v___x_2562_, v___x_2564_, v___y_2554_);
v___x_2566_ = l_Lean_Syntax_node4(v___y_2556_, v___y_2552_, v___y_2548_, v___y_2547_, v___y_2559_, v___x_2565_);
v___y_2430_ = v___y_2555_;
v_stx_2431_ = v___x_2566_;
v___y_2432_ = v___y_2551_;
v___y_2433_ = v___y_2550_;
goto v___jp_2429_;
}
v___jp_2567_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = l_Array_append___redArg(v___x_2464_, v___y_2581_);
lean_dec_ref(v___y_2581_);
lean_inc(v___y_2578_);
v___x_2583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2583_, 0, v___y_2578_);
lean_ctor_set(v___x_2583_, 1, v___x_2463_);
lean_ctor_set(v___x_2583_, 2, v___x_2582_);
if (lean_obj_tag(v___y_2569_) == 1)
{
lean_object* v_val_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v___x_2372_);
v_val_2584_ = lean_ctor_get(v___y_2569_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v___y_2569_, 1);
v___x_2585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2586_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2585_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2578_, 4);
v___x_2588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___y_2578_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Array_append___redArg(v___x_2464_, v_val_2584_);
lean_dec(v_val_2584_);
v___x_2590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___y_2578_);
lean_ctor_set(v___x_2590_, 1, v___x_2463_);
lean_ctor_set(v___x_2590_, 2, v___x_2589_);
v___x_2591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___y_2578_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = l_Lean_Syntax_node3(v___y_2578_, v___x_2586_, v___x_2588_, v___x_2590_, v___x_2592_);
v___x_2594_ = l_Array_mkArray1___redArg(v___x_2593_);
v___y_2547_ = v___y_2568_;
v___y_2548_ = v___y_2570_;
v___y_2549_ = v___y_2571_;
v___y_2550_ = v___y_2572_;
v___y_2551_ = v___y_2573_;
v___y_2552_ = v___y_2574_;
v___y_2553_ = v___y_2575_;
v___y_2554_ = v___y_2576_;
v___y_2555_ = v___y_2577_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
v___y_2558_ = v___x_2583_;
v___y_2559_ = v___y_2580_;
v___y_2560_ = v___x_2594_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2595_; 
lean_dec(v___y_2569_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2547_ = v___y_2568_;
v___y_2548_ = v___y_2570_;
v___y_2549_ = v___y_2571_;
v___y_2550_ = v___y_2572_;
v___y_2551_ = v___y_2573_;
v___y_2552_ = v___y_2574_;
v___y_2553_ = v___y_2575_;
v___y_2554_ = v___y_2576_;
v___y_2555_ = v___y_2577_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
v___y_2558_ = v___x_2583_;
v___y_2559_ = v___y_2580_;
v___y_2560_ = v___x_2595_;
goto v___jp_2546_;
}
}
v___jp_2596_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = l_Array_append___redArg(v___x_2464_, v___y_2610_);
lean_dec_ref(v___y_2610_);
lean_inc(v___y_2608_);
v___x_2612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2612_, 0, v___y_2608_);
lean_ctor_set(v___x_2612_, 1, v___x_2463_);
lean_ctor_set(v___x_2612_, 2, v___x_2611_);
if (lean_obj_tag(v___y_2601_) == 1)
{
lean_object* v_val_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_val_2613_ = lean_ctor_get(v___y_2601_, 0);
lean_inc(v_val_2613_);
lean_dec_ref_known(v___y_2601_, 1);
v___x_2614_ = l_Lean_SourceInfo_fromRef(v_val_2613_, v___x_2373_);
lean_dec(v_val_2613_);
v___x_2615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = l_Array_mkArray1___redArg(v___x_2616_);
v___y_2568_ = v___y_2597_;
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2599_;
v___y_2571_ = v___y_2600_;
v___y_2572_ = v___y_2602_;
v___y_2573_ = v___y_2603_;
v___y_2574_ = v___y_2604_;
v___y_2575_ = v___y_2605_;
v___y_2576_ = v___y_2606_;
v___y_2577_ = v___y_2607_;
v___y_2578_ = v___y_2608_;
v___y_2579_ = v___x_2612_;
v___y_2580_ = v___y_2609_;
v___y_2581_ = v___x_2617_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2618_; 
lean_dec(v___y_2601_);
v___x_2618_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2568_ = v___y_2597_;
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2599_;
v___y_2571_ = v___y_2600_;
v___y_2572_ = v___y_2602_;
v___y_2573_ = v___y_2603_;
v___y_2574_ = v___y_2604_;
v___y_2575_ = v___y_2605_;
v___y_2576_ = v___y_2606_;
v___y_2577_ = v___y_2607_;
v___y_2578_ = v___y_2608_;
v___y_2579_ = v___x_2612_;
v___y_2580_ = v___y_2609_;
v___y_2581_ = v___x_2618_;
goto v___jp_2567_;
}
}
v___jp_2619_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2631_ = l_Array_append___redArg(v___x_2464_, v___y_2630_);
lean_dec_ref(v___y_2630_);
lean_inc_n(v___y_2629_, 2);
v___x_2632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2632_, 0, v___y_2629_);
lean_ctor_set(v___x_2632_, 1, v___x_2463_);
lean_ctor_set(v___x_2632_, 2, v___x_2631_);
v___x_2633_ = l_Lean_Syntax_node5(v___y_2629_, v___x_2374_, v___y_2627_, v___y_2622_, v___y_2620_, v___y_2625_, v___x_2632_);
lean_inc(v___y_2624_);
v___x_2634_ = l_Lean_Syntax_node4(v___y_2629_, v___x_2375_, v___y_2626_, v___y_2624_, v___y_2624_, v___x_2633_);
v___y_2430_ = v___y_2628_;
v_stx_2431_ = v___x_2634_;
v___y_2432_ = v___y_2623_;
v___y_2433_ = v___y_2621_;
goto v___jp_2429_;
}
v___jp_2635_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = l_Array_append___redArg(v___x_2464_, v___y_2646_);
lean_dec_ref(v___y_2646_);
lean_inc(v___y_2645_);
v___x_2648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2648_, 0, v___y_2645_);
lean_ctor_set(v___x_2648_, 1, v___x_2463_);
lean_ctor_set(v___x_2648_, 2, v___x_2647_);
if (lean_obj_tag(v___y_2639_) == 1)
{
lean_object* v_val_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v___x_2372_);
v_val_2649_ = lean_ctor_get(v___y_2639_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v___y_2639_, 1);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2645_);
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___y_2645_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Array_mkArray2___redArg(v___x_2651_, v_val_2649_);
v___y_2620_ = v___y_2636_;
v___y_2621_ = v___y_2638_;
v___y_2622_ = v___y_2637_;
v___y_2623_ = v___y_2640_;
v___y_2624_ = v___y_2641_;
v___y_2625_ = v___x_2648_;
v___y_2626_ = v___y_2642_;
v___y_2627_ = v___y_2643_;
v___y_2628_ = v___y_2644_;
v___y_2629_ = v___y_2645_;
v___y_2630_ = v___x_2652_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2653_; 
lean_dec(v___y_2639_);
v___x_2653_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2620_ = v___y_2636_;
v___y_2621_ = v___y_2638_;
v___y_2622_ = v___y_2637_;
v___y_2623_ = v___y_2640_;
v___y_2624_ = v___y_2641_;
v___y_2625_ = v___x_2648_;
v___y_2626_ = v___y_2642_;
v___y_2627_ = v___y_2643_;
v___y_2628_ = v___y_2644_;
v___y_2629_ = v___y_2645_;
v___y_2630_ = v___x_2653_;
goto v___jp_2619_;
}
}
v___jp_2654_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = l_Array_append___redArg(v___x_2464_, v___y_2665_);
lean_dec_ref(v___y_2665_);
lean_inc(v___y_2664_);
v___x_2667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2664_);
lean_ctor_set(v___x_2667_, 1, v___x_2463_);
lean_ctor_set(v___x_2667_, 2, v___x_2666_);
if (lean_obj_tag(v___y_2659_) == 1)
{
lean_object* v_val_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_val_2668_ = lean_ctor_get(v___y_2659_, 0);
lean_inc(v_val_2668_);
lean_dec_ref_known(v___y_2659_, 1);
v___x_2669_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2670_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2669_);
v___x_2671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2664_, 4);
v___x_2672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___y_2664_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Array_append___redArg(v___x_2464_, v_val_2668_);
lean_dec(v_val_2668_);
v___x_2674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2674_, 0, v___y_2664_);
lean_ctor_set(v___x_2674_, 1, v___x_2463_);
lean_ctor_set(v___x_2674_, 2, v___x_2673_);
v___x_2675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___y_2664_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_Syntax_node3(v___y_2664_, v___x_2670_, v___x_2672_, v___x_2674_, v___x_2676_);
v___x_2678_ = l_Array_mkArray1___redArg(v___x_2677_);
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___y_2656_;
v___y_2638_ = v___y_2655_;
v___y_2639_ = v___y_2658_;
v___y_2640_ = v___y_2657_;
v___y_2641_ = v___y_2660_;
v___y_2642_ = v___y_2661_;
v___y_2643_ = v___y_2662_;
v___y_2644_ = v___y_2663_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___x_2678_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2679_; 
lean_dec(v___y_2659_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2679_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___y_2656_;
v___y_2638_ = v___y_2655_;
v___y_2639_ = v___y_2658_;
v___y_2640_ = v___y_2657_;
v___y_2641_ = v___y_2660_;
v___y_2642_ = v___y_2661_;
v___y_2643_ = v___y_2662_;
v___y_2644_ = v___y_2663_;
v___y_2645_ = v___y_2664_;
v___y_2646_ = v___x_2679_;
goto v___jp_2635_;
}
}
v___jp_2680_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = l_Array_append___redArg(v___x_2464_, v___y_2691_);
lean_dec_ref(v___y_2691_);
lean_inc(v___y_2690_);
v___x_2693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2693_, 0, v___y_2690_);
lean_ctor_set(v___x_2693_, 1, v___x_2463_);
lean_ctor_set(v___x_2693_, 2, v___x_2692_);
if (lean_obj_tag(v___y_2686_) == 1)
{
lean_object* v_val_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_val_2694_ = lean_ctor_get(v___y_2686_, 0);
lean_inc(v_val_2694_);
lean_dec_ref_known(v___y_2686_, 1);
v___x_2695_ = l_Lean_SourceInfo_fromRef(v_val_2694_, v___x_2373_);
lean_dec(v_val_2694_);
v___x_2696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Array_mkArray1___redArg(v___x_2697_);
v___y_2655_ = v___y_2681_;
v___y_2656_ = v___x_2693_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2682_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2684_;
v___y_2661_ = v___y_2687_;
v___y_2662_ = v___y_2688_;
v___y_2663_ = v___y_2689_;
v___y_2664_ = v___y_2690_;
v___y_2665_ = v___x_2698_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2699_; 
lean_dec(v___y_2686_);
v___x_2699_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2655_ = v___y_2681_;
v___y_2656_ = v___x_2693_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2682_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2684_;
v___y_2661_ = v___y_2687_;
v___y_2662_ = v___y_2688_;
v___y_2663_ = v___y_2689_;
v___y_2664_ = v___y_2690_;
v___y_2665_ = v___x_2699_;
goto v___jp_2654_;
}
}
v___jp_2700_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2714_ = l_Array_append___redArg(v___x_2464_, v___y_2713_);
lean_dec_ref(v___y_2713_);
lean_inc_n(v___y_2709_, 3);
v___x_2715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2715_, 0, v___y_2709_);
lean_ctor_set(v___x_2715_, 1, v___x_2463_);
lean_ctor_set(v___x_2715_, 2, v___x_2714_);
v___x_2716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___y_2709_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = l_Lean_Syntax_node6(v___y_2709_, v___y_2701_, v___y_2707_, v___y_2710_, v___y_2712_, v___x_2715_, v___x_2717_, v___y_2706_);
lean_inc(v___y_2711_);
v___x_2719_ = l_Lean_Syntax_node4(v___y_2709_, v___y_2702_, v___y_2704_, v___y_2711_, v___y_2711_, v___x_2718_);
v___y_2430_ = v___y_2708_;
v_stx_2431_ = v___x_2719_;
v___y_2432_ = v___y_2705_;
v___y_2433_ = v___y_2703_;
goto v___jp_2429_;
}
v___jp_2720_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = l_Array_append___redArg(v___x_2464_, v___y_2733_);
lean_dec_ref(v___y_2733_);
lean_inc(v___y_2730_);
v___x_2735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2735_, 0, v___y_2730_);
lean_ctor_set(v___x_2735_, 1, v___x_2463_);
lean_ctor_set(v___x_2735_, 2, v___x_2734_);
if (lean_obj_tag(v___y_2721_) == 1)
{
lean_object* v_val_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v___x_2372_);
v_val_2736_ = lean_ctor_get(v___y_2721_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___y_2721_, 1);
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2738_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2737_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2730_, 4);
v___x_2740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___y_2730_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Array_append___redArg(v___x_2464_, v_val_2736_);
lean_dec(v_val_2736_);
v___x_2742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2742_, 0, v___y_2730_);
lean_ctor_set(v___x_2742_, 1, v___x_2463_);
lean_ctor_set(v___x_2742_, 2, v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___y_2730_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = l_Lean_Syntax_node3(v___y_2730_, v___x_2738_, v___x_2740_, v___x_2742_, v___x_2744_);
v___x_2746_ = l_Array_mkArray1___redArg(v___x_2745_);
v___y_2701_ = v___y_2722_;
v___y_2702_ = v___y_2723_;
v___y_2703_ = v___y_2724_;
v___y_2704_ = v___y_2725_;
v___y_2705_ = v___y_2726_;
v___y_2706_ = v___y_2727_;
v___y_2707_ = v___y_2728_;
v___y_2708_ = v___y_2729_;
v___y_2709_ = v___y_2730_;
v___y_2710_ = v___y_2731_;
v___y_2711_ = v___y_2732_;
v___y_2712_ = v___x_2735_;
v___y_2713_ = v___x_2746_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2747_; 
lean_dec(v___y_2721_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2747_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2701_ = v___y_2722_;
v___y_2702_ = v___y_2723_;
v___y_2703_ = v___y_2724_;
v___y_2704_ = v___y_2725_;
v___y_2705_ = v___y_2726_;
v___y_2706_ = v___y_2727_;
v___y_2707_ = v___y_2728_;
v___y_2708_ = v___y_2729_;
v___y_2709_ = v___y_2730_;
v___y_2710_ = v___y_2731_;
v___y_2711_ = v___y_2732_;
v___y_2712_ = v___x_2735_;
v___y_2713_ = v___x_2747_;
goto v___jp_2700_;
}
}
v___jp_2748_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = l_Array_append___redArg(v___x_2464_, v___y_2761_);
lean_dec_ref(v___y_2761_);
lean_inc(v___y_2759_);
v___x_2763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2759_);
lean_ctor_set(v___x_2763_, 1, v___x_2463_);
lean_ctor_set(v___x_2763_, 2, v___x_2762_);
if (lean_obj_tag(v___y_2750_) == 1)
{
lean_object* v_val_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_val_2764_ = lean_ctor_get(v___y_2750_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___y_2750_, 1);
v___x_2765_ = l_Lean_SourceInfo_fromRef(v_val_2764_, v___x_2373_);
lean_dec(v_val_2764_);
v___x_2766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = l_Array_mkArray1___redArg(v___x_2767_);
v___y_2721_ = v___y_2749_;
v___y_2722_ = v___y_2751_;
v___y_2723_ = v___y_2752_;
v___y_2724_ = v___y_2753_;
v___y_2725_ = v___y_2754_;
v___y_2726_ = v___y_2755_;
v___y_2727_ = v___y_2756_;
v___y_2728_ = v___y_2757_;
v___y_2729_ = v___y_2758_;
v___y_2730_ = v___y_2759_;
v___y_2731_ = v___x_2763_;
v___y_2732_ = v___y_2760_;
v___y_2733_ = v___x_2768_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2769_; 
lean_dec(v___y_2750_);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2721_ = v___y_2749_;
v___y_2722_ = v___y_2751_;
v___y_2723_ = v___y_2752_;
v___y_2724_ = v___y_2753_;
v___y_2725_ = v___y_2754_;
v___y_2726_ = v___y_2755_;
v___y_2727_ = v___y_2756_;
v___y_2728_ = v___y_2757_;
v___y_2729_ = v___y_2758_;
v___y_2730_ = v___y_2759_;
v___y_2731_ = v___x_2763_;
v___y_2732_ = v___y_2760_;
v___y_2733_ = v___x_2769_;
goto v___jp_2720_;
}
}
v___jp_2770_:
{
if (v___y_2783_ == 0)
{
if (v_useReducible_2376_ == 0)
{
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
if (lean_obj_tag(v___y_2778_) == 0)
{
lean_dec(v___y_2785_);
lean_dec(v___y_2781_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___y_2436_ = v___y_2784_;
v___y_2437_ = v___y_2782_;
v___y_2438_ = v___y_2776_;
v___y_2439_ = v___y_2773_;
v___y_2440_ = v___y_2774_;
v___y_2441_ = v___y_2775_;
v___y_2442_ = v___y_2780_;
v___y_2443_ = v___y_2779_;
v___y_2444_ = v___y_2777_;
goto v___jp_2435_;
}
else
{
lean_object* v_val_2786_; lean_object* v___x_2787_; 
v_val_2786_ = lean_ctor_get(v___y_2778_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v___y_2778_, 1);
lean_inc(v___y_2777_);
lean_inc_ref(v___y_2779_);
v___x_2787_ = lean_apply_9(v___f_2377_, v___y_2782_, v___y_2776_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2780_, v___y_2779_, v___y_2777_, lean_box(0));
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc_n(v_a_2788_, 3);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2371_, 2);
lean_inc_ref_n(v___x_2370_, 2);
lean_inc_ref_n(v___x_2369_, 2);
v___x_2790_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_a_2788_);
lean_ctor_set(v___x_2791_, 1, v___x_2378_);
v___x_2792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2792_, 0, v_a_2788_);
lean_ctor_set(v___x_2792_, 1, v___x_2463_);
lean_ctor_set(v___x_2792_, 2, v___x_2464_);
v___x_2793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2794_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2793_);
if (lean_obj_tag(v___y_2785_) == 0)
{
lean_object* v___x_2795_; 
v___x_2795_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2749_ = v___y_2771_;
v___y_2750_ = v___y_2772_;
v___y_2751_ = v___x_2794_;
v___y_2752_ = v___x_2790_;
v___y_2753_ = v___y_2777_;
v___y_2754_ = v___x_2791_;
v___y_2755_ = v___y_2779_;
v___y_2756_ = v_val_2786_;
v___y_2757_ = v___y_2781_;
v___y_2758_ = v___y_2784_;
v___y_2759_ = v_a_2788_;
v___y_2760_ = v___x_2792_;
v___y_2761_ = v___x_2795_;
goto v___jp_2748_;
}
else
{
lean_object* v_val_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_val_2796_ = lean_ctor_get(v___y_2785_, 0);
lean_inc(v_val_2796_);
lean_dec_ref_known(v___y_2785_, 1);
v___x_2797_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___x_2798_ = lean_array_push(v___x_2797_, v_val_2796_);
v___y_2749_ = v___y_2771_;
v___y_2750_ = v___y_2772_;
v___y_2751_ = v___x_2794_;
v___y_2752_ = v___x_2790_;
v___y_2753_ = v___y_2777_;
v___y_2754_ = v___x_2791_;
v___y_2755_ = v___y_2779_;
v___y_2756_ = v_val_2786_;
v___y_2757_ = v___y_2781_;
v___y_2758_ = v___y_2784_;
v___y_2759_ = v_a_2788_;
v___y_2760_ = v___x_2792_;
v___y_2761_ = v___x_2798_;
goto v___jp_2748_;
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_val_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2777_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___x_2378_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v_a_2799_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2787_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2787_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
else
{
lean_object* v___x_2807_; 
lean_inc(v___y_2777_);
lean_inc_ref(v___y_2779_);
v___x_2807_ = lean_apply_9(v___f_2377_, v___y_2782_, v___y_2776_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2780_, v___y_2779_, v___y_2777_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc_n(v_a_2808_, 3);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2809_, 0, v_a_2808_);
lean_ctor_set(v___x_2809_, 1, v___x_2378_);
v___x_2810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2810_, 0, v_a_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2463_);
lean_ctor_set(v___x_2810_, 2, v___x_2464_);
if (lean_obj_tag(v___y_2785_) == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2681_ = v___y_2777_;
v___y_2682_ = v___y_2778_;
v___y_2683_ = v___y_2779_;
v___y_2684_ = v___x_2810_;
v___y_2685_ = v___y_2771_;
v___y_2686_ = v___y_2772_;
v___y_2687_ = v___x_2809_;
v___y_2688_ = v___y_2781_;
v___y_2689_ = v___y_2784_;
v___y_2690_ = v_a_2808_;
v___y_2691_ = v___x_2811_;
goto v___jp_2680_;
}
else
{
lean_object* v_val_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_val_2812_ = lean_ctor_get(v___y_2785_, 0);
lean_inc(v_val_2812_);
lean_dec_ref_known(v___y_2785_, 1);
v___x_2813_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___x_2814_ = lean_array_push(v___x_2813_, v_val_2812_);
v___y_2681_ = v___y_2777_;
v___y_2682_ = v___y_2778_;
v___y_2683_ = v___y_2779_;
v___y_2684_ = v___x_2810_;
v___y_2685_ = v___y_2771_;
v___y_2686_ = v___y_2772_;
v___y_2687_ = v___x_2809_;
v___y_2688_ = v___y_2781_;
v___y_2689_ = v___y_2784_;
v___y_2690_ = v_a_2808_;
v___y_2691_ = v___x_2814_;
goto v___jp_2680_;
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___x_2378_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v_a_2815_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2807_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2807_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
else
{
lean_dec(v___x_2375_);
if (v_useReducible_2376_ == 0)
{
lean_dec(v___x_2374_);
if (lean_obj_tag(v___y_2778_) == 0)
{
lean_dec(v___y_2785_);
lean_dec(v___y_2781_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___y_2436_ = v___y_2784_;
v___y_2437_ = v___y_2782_;
v___y_2438_ = v___y_2776_;
v___y_2439_ = v___y_2773_;
v___y_2440_ = v___y_2774_;
v___y_2441_ = v___y_2775_;
v___y_2442_ = v___y_2780_;
v___y_2443_ = v___y_2779_;
v___y_2444_ = v___y_2777_;
goto v___jp_2435_;
}
else
{
lean_object* v_val_2823_; lean_object* v___x_2824_; 
v_val_2823_ = lean_ctor_get(v___y_2778_, 0);
lean_inc(v_val_2823_);
lean_dec_ref_known(v___y_2778_, 1);
lean_inc(v___y_2777_);
lean_inc_ref(v___y_2779_);
v___x_2824_ = lean_apply_9(v___f_2377_, v___y_2782_, v___y_2776_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2780_, v___y_2779_, v___y_2777_, lean_box(0));
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc_n(v_a_2825_, 5);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2371_, 2);
lean_inc_ref_n(v___x_2370_, 2);
lean_inc_ref_n(v___x_2369_, 2);
v___x_2827_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2826_);
v___x_2828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2828_, 0, v_a_2825_);
lean_ctor_set(v___x_2828_, 1, v___x_2378_);
v___x_2829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2829_, 0, v_a_2825_);
lean_ctor_set(v___x_2829_, 1, v___x_2463_);
lean_ctor_set(v___x_2829_, 2, v___x_2464_);
v___x_2830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_2831_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_a_2825_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_Syntax_node1(v_a_2825_, v___x_2463_, v___x_2831_);
v___x_2833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2834_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2833_);
if (lean_obj_tag(v___y_2785_) == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2597_ = v___x_2829_;
v___y_2598_ = v___y_2771_;
v___y_2599_ = v___x_2828_;
v___y_2600_ = v___x_2834_;
v___y_2601_ = v___y_2772_;
v___y_2602_ = v___y_2777_;
v___y_2603_ = v___y_2779_;
v___y_2604_ = v___x_2827_;
v___y_2605_ = v___y_2781_;
v___y_2606_ = v_val_2823_;
v___y_2607_ = v___y_2784_;
v___y_2608_ = v_a_2825_;
v___y_2609_ = v___x_2832_;
v___y_2610_ = v___x_2835_;
goto v___jp_2596_;
}
else
{
lean_object* v_val_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_val_2836_ = lean_ctor_get(v___y_2785_, 0);
lean_inc(v_val_2836_);
lean_dec_ref_known(v___y_2785_, 1);
v___x_2837_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___x_2838_ = lean_array_push(v___x_2837_, v_val_2836_);
v___y_2597_ = v___x_2829_;
v___y_2598_ = v___y_2771_;
v___y_2599_ = v___x_2828_;
v___y_2600_ = v___x_2834_;
v___y_2601_ = v___y_2772_;
v___y_2602_ = v___y_2777_;
v___y_2603_ = v___y_2779_;
v___y_2604_ = v___x_2827_;
v___y_2605_ = v___y_2781_;
v___y_2606_ = v_val_2823_;
v___y_2607_ = v___y_2784_;
v___y_2608_ = v_a_2825_;
v___y_2609_ = v___x_2832_;
v___y_2610_ = v___x_2838_;
goto v___jp_2596_;
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_val_2823_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2777_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___x_2378_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v_a_2839_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2824_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2824_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
else
{
lean_object* v___x_2847_; 
lean_dec_ref(v___x_2378_);
lean_inc(v___y_2777_);
lean_inc_ref(v___y_2779_);
v___x_2847_ = lean_apply_9(v___f_2377_, v___y_2782_, v___y_2776_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2780_, v___y_2779_, v___y_2777_, lean_box(0));
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_n(v_a_2848_, 2);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20));
lean_inc_ref(v___x_2371_);
lean_inc_ref(v___x_2370_);
lean_inc_ref(v___x_2369_);
v___x_2850_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2849_);
v___x_2851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21));
v___x_2852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2852_, 0, v_a_2848_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
if (lean_obj_tag(v___y_2785_) == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2527_ = v___x_2852_;
v___y_2528_ = v___y_2777_;
v___y_2529_ = v_a_2848_;
v___y_2530_ = v___y_2778_;
v___y_2531_ = v___y_2779_;
v___y_2532_ = v___y_2771_;
v___y_2533_ = v___y_2772_;
v___y_2534_ = v___y_2781_;
v___y_2535_ = v___y_2784_;
v___y_2536_ = v___x_2850_;
v___y_2537_ = v___x_2853_;
goto v___jp_2526_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_val_2854_ = lean_ctor_get(v___y_2785_, 0);
lean_inc(v_val_2854_);
lean_dec_ref_known(v___y_2785_, 1);
v___x_2855_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___x_2856_ = lean_array_push(v___x_2855_, v_val_2854_);
v___y_2527_ = v___x_2852_;
v___y_2528_ = v___y_2777_;
v___y_2529_ = v_a_2848_;
v___y_2530_ = v___y_2778_;
v___y_2531_ = v___y_2779_;
v___y_2532_ = v___y_2771_;
v___y_2533_ = v___y_2772_;
v___y_2534_ = v___y_2781_;
v___y_2535_ = v___y_2784_;
v___y_2536_ = v___x_2850_;
v___y_2537_ = v___x_2856_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v_a_2857_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2847_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2847_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
}
v___jp_2865_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2882_ = lean_unsigned_to_nat(5u);
v___x_2883_ = l_Lean_Syntax_getArg(v___y_2869_, v___x_2882_);
lean_dec(v___y_2869_);
v___x_2884_ = l_Lean_Syntax_matchesNull(v___x_2883_, v___x_2372_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v_args_2873_);
lean_dec(v___y_2870_);
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2886_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2885_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___y_2430_ = v___y_2871_;
v_stx_2431_ = v_a_2887_;
v___y_2432_ = v___y_2880_;
v___y_2433_ = v___y_2881_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v___y_2871_);
lean_dec(v_tk_2368_);
v_a_2888_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2886_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2886_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Syntax_getOptional_x3f(v___y_2867_);
lean_dec(v___y_2867_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_box(0);
v___y_2771_ = v_args_2873_;
v___y_2772_ = v___y_2868_;
v___y_2773_ = v___y_2876_;
v___y_2774_ = v___y_2877_;
v___y_2775_ = v___y_2878_;
v___y_2776_ = v___y_2875_;
v___y_2777_ = v___y_2881_;
v___y_2778_ = v___y_2866_;
v___y_2779_ = v___y_2880_;
v___y_2780_ = v___y_2879_;
v___y_2781_ = v___y_2870_;
v___y_2782_ = v___y_2874_;
v___y_2783_ = v___y_2872_;
v___y_2784_ = v___y_2871_;
v___y_2785_ = v___x_2897_;
goto v___jp_2770_;
}
else
{
lean_object* v_val_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v_val_2898_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2896_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_val_2898_);
lean_dec(v___x_2896_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_val_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
v___y_2771_ = v_args_2873_;
v___y_2772_ = v___y_2868_;
v___y_2773_ = v___y_2876_;
v___y_2774_ = v___y_2877_;
v___y_2775_ = v___y_2878_;
v___y_2776_ = v___y_2875_;
v___y_2777_ = v___y_2881_;
v___y_2778_ = v___y_2866_;
v___y_2779_ = v___y_2880_;
v___y_2780_ = v___y_2879_;
v___y_2781_ = v___y_2870_;
v___y_2782_ = v___y_2874_;
v___y_2783_ = v___y_2872_;
v___y_2784_ = v___y_2871_;
v___y_2785_ = v___x_2903_;
goto v___jp_2770_;
}
}
}
}
}
v___jp_2906_:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = l_Lean_Syntax_getArg(v___y_2909_, v___x_2379_);
v___x_2923_ = l_Lean_Syntax_isNone(v___x_2922_);
if (v___x_2923_ == 0)
{
uint8_t v___x_2924_; 
lean_inc(v___x_2922_);
v___x_2924_ = l_Lean_Syntax_matchesNull(v___x_2922_, v___x_2380_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec(v___x_2922_);
lean_dec(v_only_2913_);
lean_dec(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2926_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2925_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___y_2430_ = v___y_2912_;
v_stx_2431_ = v_a_2927_;
v___y_2432_ = v___y_2920_;
v___y_2433_ = v___y_2921_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___y_2912_);
lean_dec(v_tk_2368_);
v_a_2928_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2926_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2926_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = l_Lean_Syntax_getArg(v___x_2922_, v___x_2381_);
lean_dec(v___x_2381_);
lean_dec(v___x_2922_);
v___x_2937_ = l_Lean_Syntax_getArgs(v___x_2936_);
lean_dec(v___x_2936_);
v___x_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
v___y_2866_ = v___y_2907_;
v___y_2867_ = v___y_2908_;
v___y_2868_ = v_only_2913_;
v___y_2869_ = v___y_2909_;
v___y_2870_ = v___y_2910_;
v___y_2871_ = v___y_2912_;
v___y_2872_ = v___y_2911_;
v_args_2873_ = v___x_2938_;
v___y_2874_ = v___y_2914_;
v___y_2875_ = v___y_2915_;
v___y_2876_ = v___y_2916_;
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2918_;
v___y_2879_ = v___y_2919_;
v___y_2880_ = v___y_2920_;
v___y_2881_ = v___y_2921_;
goto v___jp_2865_;
}
}
else
{
lean_object* v___x_2939_; 
lean_dec(v___x_2922_);
lean_dec(v___x_2381_);
v___x_2939_ = lean_box(0);
v___y_2866_ = v___y_2907_;
v___y_2867_ = v___y_2908_;
v___y_2868_ = v_only_2913_;
v___y_2869_ = v___y_2909_;
v___y_2870_ = v___y_2910_;
v___y_2871_ = v___y_2912_;
v___y_2872_ = v___y_2911_;
v_args_2873_ = v___x_2939_;
v___y_2874_ = v___y_2914_;
v___y_2875_ = v___y_2915_;
v___y_2876_ = v___y_2916_;
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2918_;
v___y_2879_ = v___y_2919_;
v___y_2880_ = v___y_2920_;
v___y_2881_ = v___y_2921_;
goto v___jp_2865_;
}
}
v___jp_2940_:
{
lean_object* v_usedTheorems_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_usedTheorems_2945_ = lean_ctor_get(v___y_2943_, 0);
v___x_2946_ = l_Lean_Syntax_unsetTrailing(v___y_2941_);
v___x_2947_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2946_, v_usedTheorems_2945_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; uint8_t v___x_2949_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc_n(v_a_2948_, 2);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2949_ = l_Lean_Syntax_isOfKind(v_a_2948_, v___x_2461_);
lean_dec(v___x_2461_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_inc(v_ref_2457_);
lean_dec(v_a_2948_);
lean_dec(v___y_2944_);
lean_dec(v___x_2383_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2951_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2950_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___y_2407_ = v___y_2943_;
v_stx_2408_ = v_a_2952_;
v___y_2409_ = v___y_2399_;
v_ref_2410_ = v_ref_2457_;
v___y_2411_ = v___y_2400_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v___y_2943_);
lean_dec(v_ref_2457_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v_tk_2368_);
v_a_2953_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2951_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2951_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
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
else
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = l_Lean_Syntax_getArg(v_a_2948_, v___x_2381_);
lean_inc(v___x_2961_);
v___x_2962_ = l_Lean_Syntax_isOfKind(v___x_2961_, v___x_2382_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_inc(v_ref_2457_);
lean_dec(v___x_2961_);
lean_dec(v_a_2948_);
lean_dec(v___y_2944_);
lean_dec(v___x_2383_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2963_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2964_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2963_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___y_2407_ = v___y_2943_;
v_stx_2408_ = v_a_2965_;
v___y_2409_ = v___y_2399_;
v_ref_2410_ = v_ref_2457_;
v___y_2411_ = v___y_2400_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v___y_2943_);
lean_dec(v_ref_2457_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v_tk_2368_);
v_a_2966_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2964_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v___x_2974_ = l_Lean_Syntax_getArg(v_a_2948_, v___x_2383_);
lean_dec(v___x_2383_);
v___x_2975_ = l_Lean_Syntax_getArg(v_a_2948_, v___x_2380_);
v___x_2976_ = l_Lean_Syntax_isNone(v___x_2975_);
if (v___x_2976_ == 0)
{
uint8_t v___x_2977_; 
lean_inc(v___x_2975_);
v___x_2977_ = l_Lean_Syntax_matchesNull(v___x_2975_, v___x_2381_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_inc(v_ref_2457_);
lean_dec(v___x_2975_);
lean_dec(v___x_2974_);
lean_dec(v___x_2961_);
lean_dec(v_a_2948_);
lean_dec(v___y_2944_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2978_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2979_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2978_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___y_2407_ = v___y_2943_;
v_stx_2408_ = v_a_2980_;
v___y_2409_ = v___y_2399_;
v_ref_2410_ = v_ref_2457_;
v___y_2411_ = v___y_2400_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v___y_2943_);
lean_dec(v_ref_2457_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v_tk_2368_);
v_a_2981_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = l_Lean_Syntax_getArg(v___x_2975_, v___x_2372_);
lean_dec(v___x_2975_);
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
v___y_2907_ = v___y_2944_;
v___y_2908_ = v___x_2974_;
v___y_2909_ = v_a_2948_;
v___y_2910_ = v___x_2961_;
v___y_2911_ = v___y_2942_;
v___y_2912_ = v___y_2943_;
v_only_2913_ = v___x_2990_;
v___y_2914_ = v___y_2393_;
v___y_2915_ = v___y_2394_;
v___y_2916_ = v___y_2395_;
v___y_2917_ = v___y_2396_;
v___y_2918_ = v___y_2397_;
v___y_2919_ = v___y_2398_;
v___y_2920_ = v___y_2399_;
v___y_2921_ = v___y_2400_;
goto v___jp_2906_;
}
}
else
{
lean_object* v___x_2991_; 
lean_dec(v___x_2975_);
v___x_2991_ = lean_box(0);
v___y_2907_ = v___y_2944_;
v___y_2908_ = v___x_2974_;
v___y_2909_ = v_a_2948_;
v___y_2910_ = v___x_2961_;
v___y_2911_ = v___y_2942_;
v___y_2912_ = v___y_2943_;
v_only_2913_ = v___x_2991_;
v___y_2914_ = v___y_2393_;
v___y_2915_ = v___y_2394_;
v___y_2916_ = v___y_2395_;
v___y_2917_ = v___y_2396_;
v___y_2918_ = v___y_2397_;
v___y_2919_ = v___y_2398_;
v___y_2920_ = v___y_2399_;
v___y_2921_ = v___y_2400_;
goto v___jp_2906_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___x_2461_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___x_2383_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v_a_2992_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2947_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2947_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
v___jp_3000_:
{
if (lean_obj_tag(v_usingArg_2384_) == 0)
{
v___y_2941_ = v___y_3001_;
v___y_2942_ = v___y_3003_;
v___y_2943_ = v___y_3002_;
v___y_2944_ = v_usingArg_2384_;
goto v___jp_2940_;
}
else
{
lean_object* v_val_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3012_; 
v_val_3004_ = lean_ctor_get(v_usingArg_2384_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_usingArg_2384_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3006_ = v_usingArg_2384_;
v_isShared_3007_ = v_isSharedCheck_3012_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_val_3004_);
lean_dec(v_usingArg_2384_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3012_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3008_ = l_Lean_Syntax_unsetTrailing(v_val_3004_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3008_);
v___x_3010_ = v___x_3006_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
v___y_2941_ = v___y_3001_;
v___y_2942_ = v___y_3003_;
v___y_2943_ = v___y_3002_;
v___y_2944_ = v___x_3010_;
goto v___jp_2940_;
}
}
}
}
v___jp_3013_:
{
if (v___y_3017_ == 0)
{
lean_dec(v___y_3014_);
lean_dec(v___x_2461_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v_usingArg_2384_);
lean_dec(v___x_2383_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v___y_2403_ = v___y_3016_;
goto v___jp_2402_;
}
else
{
v___y_3001_ = v___y_3014_;
v___y_3002_ = v___y_3016_;
v___y_3003_ = v___y_3015_;
goto v___jp_3000_;
}
}
v___jp_3018_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___f_3029_; lean_object* v___x_3030_; 
v___x_3024_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3023_, v___x_2458_);
v___x_3025_ = lean_box(v___x_2373_);
v___x_3026_ = lean_box(v___x_2458_);
v___x_3027_ = lean_box(v_useReducible_2376_);
v___x_3028_ = lean_box(v___x_2386_);
lean_inc(v___x_2381_);
lean_inc_ref(v___x_2378_);
lean_inc(v_usingArg_2384_);
lean_inc(v___x_2372_);
lean_inc(v_tk_2368_);
lean_inc(v___x_2383_);
v___f_3029_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 24, 14);
lean_closure_set(v___f_3029_, 0, v___x_2383_);
lean_closure_set(v___f_3029_, 1, v_tk_2368_);
lean_closure_set(v___f_3029_, 2, v___x_2463_);
lean_closure_set(v___f_3029_, 3, v___x_2372_);
lean_closure_set(v___f_3029_, 4, v___x_3024_);
lean_closure_set(v___f_3029_, 5, v___y_3019_);
lean_closure_set(v___f_3029_, 6, v___x_3025_);
lean_closure_set(v___f_3029_, 7, v_usingArg_2384_);
lean_closure_set(v___f_3029_, 8, v___x_3026_);
lean_closure_set(v___f_3029_, 9, v___x_2378_);
lean_closure_set(v___f_3029_, 10, v___x_3027_);
lean_closure_set(v___f_3029_, 11, v___x_3028_);
lean_closure_set(v___f_3029_, 12, v___x_2381_);
lean_closure_set(v___f_3029_, 13, v_usingTk_x3f_2387_);
v___x_3030_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3022_, v___f_3029_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_3022_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3033_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_2456_, v___x_3032_);
if (v___x_3033_ == 0)
{
if (lean_obj_tag(v_squeeze_2388_) == 0)
{
v___y_3014_ = v___y_3020_;
v___y_3015_ = v___y_3021_;
v___y_3016_ = v_a_3031_;
v___y_3017_ = v___x_3033_;
goto v___jp_3013_;
}
else
{
v___y_3014_ = v___y_3020_;
v___y_3015_ = v___y_3021_;
v___y_3016_ = v_a_3031_;
v___y_3017_ = v___x_2386_;
goto v___jp_3013_;
}
}
else
{
v___y_3001_ = v___y_3020_;
v___y_3002_ = v_a_3031_;
v___y_3003_ = v___y_3021_;
goto v___jp_3000_;
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v___y_3020_);
lean_dec(v___x_2461_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v_usingArg_2384_);
lean_dec(v___x_2383_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v_a_3034_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3030_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3030_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
v___jp_3042_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3046_ = l_Array_append___redArg(v___x_2464_, v___y_3045_);
lean_dec_ref(v___y_3045_);
lean_inc_n(v___x_2459_, 2);
v___x_3047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3047_, 0, v___x_2459_);
lean_ctor_set(v___x_3047_, 1, v___x_2463_);
lean_ctor_set(v___x_3047_, 2, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___x_2459_);
lean_ctor_set(v___x_3048_, 1, v___x_2463_);
lean_ctor_set(v___x_3048_, 2, v___x_2464_);
lean_inc(v___x_2461_);
v___x_3049_ = l_Lean_Syntax_node6(v___x_2459_, v___x_2461_, v___x_2462_, v___x_2385_, v___y_3044_, v___y_3043_, v___x_3047_, v___x_3048_);
v___x_3050_ = 0;
v___x_3051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23));
v___x_3052_ = lean_box(v___x_2458_);
v___x_3053_ = lean_box(v___x_3050_);
v___x_3054_ = lean_box(v___x_2458_);
lean_inc(v___x_3049_);
v___x_3055_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3055_, 0, v___x_3049_);
lean_closure_set(v___x_3055_, 1, v___x_3052_);
lean_closure_set(v___x_3055_, 2, v___x_3053_);
lean_closure_set(v___x_3055_, 3, v___x_3054_);
lean_closure_set(v___x_3055_, 4, v___x_3051_);
v___x_3056_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3055_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
if (lean_obj_tag(v_unfold_2389_) == 0)
{
lean_object* v_ctx_3058_; lean_object* v_simprocs_3059_; lean_object* v_dischargeWrapper_3060_; 
v_ctx_3058_ = lean_ctor_get(v_a_3057_, 0);
lean_inc_ref(v_ctx_3058_);
v_simprocs_3059_ = lean_ctor_get(v_a_3057_, 1);
lean_inc_ref(v_simprocs_3059_);
v_dischargeWrapper_3060_ = lean_ctor_get(v_a_3057_, 2);
lean_inc(v_dischargeWrapper_3060_);
lean_dec(v_a_3057_);
v___y_3019_ = v_simprocs_3059_;
v___y_3020_ = v___x_3049_;
v___y_3021_ = v___x_2458_;
v___y_3022_ = v_dischargeWrapper_3060_;
v___y_3023_ = v_ctx_3058_;
goto v___jp_3018_;
}
else
{
if (v___x_2386_ == 0)
{
lean_object* v_ctx_3061_; lean_object* v_simprocs_3062_; lean_object* v_dischargeWrapper_3063_; 
v_ctx_3061_ = lean_ctor_get(v_a_3057_, 0);
lean_inc_ref(v_ctx_3061_);
v_simprocs_3062_ = lean_ctor_get(v_a_3057_, 1);
lean_inc_ref(v_simprocs_3062_);
v_dischargeWrapper_3063_ = lean_ctor_get(v_a_3057_, 2);
lean_inc(v_dischargeWrapper_3063_);
lean_dec(v_a_3057_);
v___y_3019_ = v_simprocs_3062_;
v___y_3020_ = v___x_3049_;
v___y_3021_ = v___x_2386_;
v___y_3022_ = v_dischargeWrapper_3063_;
v___y_3023_ = v_ctx_3061_;
goto v___jp_3018_;
}
else
{
lean_object* v_ctx_3064_; lean_object* v_simprocs_3065_; lean_object* v_dischargeWrapper_3066_; lean_object* v___x_3067_; 
v_ctx_3064_ = lean_ctor_get(v_a_3057_, 0);
lean_inc_ref(v_ctx_3064_);
v_simprocs_3065_ = lean_ctor_get(v_a_3057_, 1);
lean_inc_ref(v_simprocs_3065_);
v_dischargeWrapper_3066_ = lean_ctor_get(v_a_3057_, 2);
lean_inc(v_dischargeWrapper_3066_);
lean_dec(v_a_3057_);
v___x_3067_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3064_);
v___y_3019_ = v_simprocs_3065_;
v___y_3020_ = v___x_3049_;
v___y_3021_ = v___x_2386_;
v___y_3022_ = v_dischargeWrapper_3066_;
v___y_3023_ = v___x_3067_;
goto v___jp_3018_;
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v___x_3049_);
lean_dec(v___x_2461_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v_usingTk_x3f_2387_);
lean_dec(v_usingArg_2384_);
lean_dec(v___x_2383_);
lean_dec(v___x_2381_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
lean_dec(v_tk_2368_);
v_a_3068_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3056_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3056_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
v___jp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = l_Array_append___redArg(v___x_2464_, v___y_3078_);
lean_dec_ref(v___y_3078_);
lean_inc(v___x_2459_);
v___x_3080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3080_, 0, v___x_2459_);
lean_ctor_set(v___x_3080_, 1, v___x_2463_);
lean_ctor_set(v___x_3080_, 2, v___x_3079_);
if (lean_obj_tag(v_args_2390_) == 1)
{
lean_object* v_val_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_val_3081_ = lean_ctor_get(v_args_2390_, 0);
v___x_3082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___x_2459_, 3);
v___x_3083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_2459_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Array_append___redArg(v___x_2464_, v_val_3081_);
v___x_3085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3085_, 0, v___x_2459_);
lean_ctor_set(v___x_3085_, 1, v___x_2463_);
lean_ctor_set(v___x_3085_, 2, v___x_3084_);
v___x_3086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_2459_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = l_Array_mkArray3___redArg(v___x_3083_, v___x_3085_, v___x_3087_);
v___y_3043_ = v___x_3080_;
v___y_3044_ = v___y_3077_;
v___y_3045_ = v___x_3088_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_3043_ = v___x_3080_;
v___y_3044_ = v___y_3077_;
v___y_3045_ = v___x_3089_;
goto v___jp_3042_;
}
}
v___jp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = l_Array_append___redArg(v___x_2464_, v___y_3091_);
lean_dec_ref(v___y_3091_);
lean_inc(v___x_2459_);
v___x_3093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3093_, 0, v___x_2459_);
lean_ctor_set(v___x_3093_, 1, v___x_2463_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
if (lean_obj_tag(v_only_2391_) == 1)
{
lean_object* v_val_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_val_3094_ = lean_ctor_get(v_only_2391_, 0);
v___x_3095_ = l_Lean_SourceInfo_fromRef(v_val_3094_, v___x_2373_);
v___x_3096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Array_mkArray1___redArg(v___x_3097_);
v___y_3077_ = v___x_3093_;
v___y_3078_ = v___x_3098_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_3077_ = v___x_3093_;
v___y_3078_ = v___x_3099_;
goto v___jp_3076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v_tk_3104_ = _args[0];
lean_object* v___x_3105_ = _args[1];
lean_object* v___x_3106_ = _args[2];
lean_object* v___x_3107_ = _args[3];
lean_object* v___x_3108_ = _args[4];
lean_object* v___x_3109_ = _args[5];
lean_object* v___x_3110_ = _args[6];
lean_object* v___x_3111_ = _args[7];
lean_object* v_useReducible_3112_ = _args[8];
lean_object* v___f_3113_ = _args[9];
lean_object* v___x_3114_ = _args[10];
lean_object* v___x_3115_ = _args[11];
lean_object* v___x_3116_ = _args[12];
lean_object* v___x_3117_ = _args[13];
lean_object* v___x_3118_ = _args[14];
lean_object* v___x_3119_ = _args[15];
lean_object* v_usingArg_3120_ = _args[16];
lean_object* v___x_3121_ = _args[17];
lean_object* v___x_3122_ = _args[18];
lean_object* v_usingTk_x3f_3123_ = _args[19];
lean_object* v_squeeze_3124_ = _args[20];
lean_object* v_unfold_3125_ = _args[21];
lean_object* v_args_3126_ = _args[22];
lean_object* v_only_3127_ = _args[23];
lean_object* v___y_3128_ = _args[24];
lean_object* v___y_3129_ = _args[25];
lean_object* v___y_3130_ = _args[26];
lean_object* v___y_3131_ = _args[27];
lean_object* v___y_3132_ = _args[28];
lean_object* v___y_3133_ = _args[29];
lean_object* v___y_3134_ = _args[30];
lean_object* v___y_3135_ = _args[31];
lean_object* v___y_3136_ = _args[32];
lean_object* v___y_3137_ = _args[33];
_start:
{
uint8_t v___x_97865__boxed_3138_; uint8_t v_useReducible_boxed_3139_; uint8_t v___x_97876__boxed_3140_; lean_object* v_res_3141_; 
v___x_97865__boxed_3138_ = lean_unbox(v___x_3109_);
v_useReducible_boxed_3139_ = lean_unbox(v_useReducible_3112_);
v___x_97876__boxed_3140_ = lean_unbox(v___x_3122_);
v_res_3141_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3104_, v___x_3105_, v___x_3106_, v___x_3107_, v___x_3108_, v___x_97865__boxed_3138_, v___x_3110_, v___x_3111_, v_useReducible_boxed_3139_, v___f_3113_, v___x_3114_, v___x_3115_, v___x_3116_, v___x_3117_, v___x_3118_, v___x_3119_, v_usingArg_3120_, v___x_3121_, v___x_97876__boxed_3140_, v_usingTk_x3f_3123_, v_squeeze_3124_, v_unfold_3125_, v_args_3126_, v_only_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v_only_3127_);
lean_dec(v_args_3126_);
lean_dec(v_unfold_3125_);
lean_dec(v_squeeze_3124_);
lean_dec(v___x_3118_);
lean_dec(v___x_3116_);
lean_dec(v___x_3115_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3168_, lean_object* v_stx_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3181_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_3182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
lean_inc(v_stx_3169_);
v___x_3184_ = l_Lean_Syntax_isOfKind(v_stx_3169_, v___x_3183_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
lean_dec(v_stx_3169_);
v___x_3185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3185_;
}
else
{
lean_object* v___f_3186_; lean_object* v___x_3187_; lean_object* v_tk_3188_; lean_object* v___x_3189_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; uint8_t v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; uint8_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v_usingTk_x3f_3240_; lean_object* v_usingArg_3241_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; uint8_t v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v_args_3273_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v_only_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v_unfold_3329_; lean_object* v_squeeze_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___f_3186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3187_ = lean_unsigned_to_nat(0u);
v_tk_3188_ = l_Lean_Syntax_getArg(v_stx_3169_, v___x_3187_);
v___x_3189_ = lean_unsigned_to_nat(1u);
v___x_3365_ = l_Lean_Syntax_getArg(v_stx_3169_, v___x_3189_);
v___x_3366_ = l_Lean_Syntax_isNone(v___x_3365_);
if (v___x_3366_ == 0)
{
uint8_t v___x_3367_; 
lean_inc(v___x_3365_);
v___x_3367_ = l_Lean_Syntax_matchesNull(v___x_3365_, v___x_3189_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_dec(v___x_3365_);
lean_dec(v_tk_3188_);
lean_dec(v_stx_3169_);
v___x_3368_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3368_;
}
else
{
lean_object* v_squeeze_3369_; lean_object* v___x_3370_; 
v_squeeze_3369_ = l_Lean_Syntax_getArg(v___x_3365_, v___x_3187_);
lean_dec(v___x_3365_);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_squeeze_3369_);
v_squeeze_3348_ = v___x_3370_;
v___y_3349_ = v_a_3170_;
v___y_3350_ = v_a_3171_;
v___y_3351_ = v_a_3172_;
v___y_3352_ = v_a_3173_;
v___y_3353_ = v_a_3174_;
v___y_3354_ = v_a_3175_;
v___y_3355_ = v_a_3176_;
v___y_3356_ = v_a_3177_;
goto v___jp_3347_;
}
}
else
{
lean_object* v___x_3371_; 
lean_dec(v___x_3365_);
v___x_3371_ = lean_box(0);
v_squeeze_3348_ = v___x_3371_;
v___y_3349_ = v_a_3170_;
v___y_3350_ = v_a_3171_;
v___y_3351_ = v_a_3172_;
v___y_3352_ = v_a_3173_;
v___y_3353_ = v_a_3174_;
v___y_3354_ = v_a_3175_;
v___y_3355_ = v_a_3176_;
v___y_3356_ = v_a_3177_;
goto v___jp_3347_;
}
v___jp_3190_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3213_ = lean_box(v___x_3184_);
v___x_3214_ = lean_box(v_useReducible_3168_);
v___x_3215_ = lean_box(v___y_3202_);
lean_inc(v___y_3198_);
lean_inc(v___y_3206_);
v___f_3216_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3216_, 0, v_tk_3188_);
lean_closure_set(v___f_3216_, 1, v___x_3179_);
lean_closure_set(v___f_3216_, 2, v___x_3180_);
lean_closure_set(v___f_3216_, 3, v___x_3181_);
lean_closure_set(v___f_3216_, 4, v___x_3187_);
lean_closure_set(v___f_3216_, 5, v___x_3213_);
lean_closure_set(v___f_3216_, 6, v___y_3206_);
lean_closure_set(v___f_3216_, 7, v___x_3183_);
lean_closure_set(v___f_3216_, 8, v___x_3214_);
lean_closure_set(v___f_3216_, 9, v___f_3186_);
lean_closure_set(v___f_3216_, 10, v___x_3182_);
lean_closure_set(v___f_3216_, 11, v___y_3194_);
lean_closure_set(v___f_3216_, 12, v___y_3197_);
lean_closure_set(v___f_3216_, 13, v___x_3189_);
lean_closure_set(v___f_3216_, 14, v___y_3198_);
lean_closure_set(v___f_3216_, 15, v___y_3208_);
lean_closure_set(v___f_3216_, 16, v___y_3192_);
lean_closure_set(v___f_3216_, 17, v___y_3199_);
lean_closure_set(v___f_3216_, 18, v___x_3215_);
lean_closure_set(v___f_3216_, 19, v___y_3203_);
lean_closure_set(v___f_3216_, 20, v___y_3210_);
lean_closure_set(v___f_3216_, 21, v___y_3193_);
lean_closure_set(v___f_3216_, 22, v___y_3196_);
lean_closure_set(v___f_3216_, 23, v___y_3204_);
lean_closure_set(v___f_3216_, 24, v___y_3212_);
v___x_3217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3217_, 0, v___f_3216_);
v___x_3218_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3217_, v___y_3201_, v___y_3200_, v___y_3195_, v___y_3211_, v___y_3207_, v___y_3205_, v___y_3191_, v___y_3209_);
return v___x_3218_;
}
v___jp_3219_:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Syntax_getOptional_x3f(v___y_3238_);
lean_dec(v___y_3238_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_box(0);
v___y_3191_ = v___y_3220_;
v___y_3192_ = v_usingArg_3241_;
v___y_3193_ = v___y_3221_;
v___y_3194_ = v___y_3222_;
v___y_3195_ = v___y_3223_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3225_;
v___y_3198_ = v___y_3226_;
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3229_;
v___y_3202_ = v___y_3230_;
v___y_3203_ = v_usingTk_x3f_3240_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3234_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___x_3243_;
goto v___jp_3190_;
}
else
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
v_val_3244_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3242_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v___x_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_val_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
v___y_3191_ = v___y_3220_;
v___y_3192_ = v_usingArg_3241_;
v___y_3193_ = v___y_3221_;
v___y_3194_ = v___y_3222_;
v___y_3195_ = v___y_3223_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3225_;
v___y_3198_ = v___y_3226_;
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3229_;
v___y_3202_ = v___y_3230_;
v___y_3203_ = v_usingTk_x3f_3240_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3234_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3236_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___x_3249_;
goto v___jp_3190_;
}
}
}
}
v___jp_3252_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3274_ = lean_unsigned_to_nat(4u);
v___x_3275_ = l_Lean_Syntax_getArg(v___y_3268_, v___x_3274_);
lean_dec(v___y_3268_);
v___x_3276_ = l_Lean_Syntax_isNone(v___x_3275_);
if (v___x_3276_ == 0)
{
uint8_t v___x_3277_; 
lean_inc(v___x_3275_);
v___x_3277_ = l_Lean_Syntax_matchesNull(v___x_3275_, v___y_3263_);
lean_dec(v___y_3263_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_dec(v___x_3275_);
lean_dec(v_args_3273_);
lean_dec(v___y_3272_);
lean_dec(v___y_3270_);
lean_dec(v___y_3267_);
lean_dec(v___y_3262_);
lean_dec(v___y_3258_);
lean_dec(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec(v_tk_3188_);
v___x_3278_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3278_;
}
else
{
lean_object* v_usingTk_x3f_3279_; lean_object* v_usingArg_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_usingTk_x3f_3279_ = l_Lean_Syntax_getArg(v___x_3275_, v___x_3187_);
v_usingArg_3280_ = l_Lean_Syntax_getArg(v___x_3275_, v___x_3189_);
lean_dec(v___x_3275_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_usingTk_x3f_3279_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_usingArg_3280_);
v___y_3220_ = v___y_3253_;
v___y_3221_ = v___y_3254_;
v___y_3222_ = v___x_3274_;
v___y_3223_ = v___y_3255_;
v___y_3224_ = v_args_3273_;
v___y_3225_ = v___y_3256_;
v___y_3226_ = v___y_3257_;
v___y_3227_ = v___y_3258_;
v___y_3228_ = v___y_3259_;
v___y_3229_ = v___y_3260_;
v___y_3230_ = v___y_3261_;
v___y_3231_ = v___y_3262_;
v___y_3232_ = v___y_3264_;
v___y_3233_ = v___y_3265_;
v___y_3234_ = v___y_3267_;
v___y_3235_ = v___y_3266_;
v___y_3236_ = v___y_3270_;
v___y_3237_ = v___y_3269_;
v___y_3238_ = v___y_3272_;
v___y_3239_ = v___y_3271_;
v_usingTk_x3f_3240_ = v___x_3281_;
v_usingArg_3241_ = v___x_3282_;
goto v___jp_3219_;
}
}
else
{
lean_object* v___x_3283_; 
lean_dec(v___x_3275_);
lean_dec(v___y_3263_);
v___x_3283_ = lean_box(0);
v___y_3220_ = v___y_3253_;
v___y_3221_ = v___y_3254_;
v___y_3222_ = v___x_3274_;
v___y_3223_ = v___y_3255_;
v___y_3224_ = v_args_3273_;
v___y_3225_ = v___y_3256_;
v___y_3226_ = v___y_3257_;
v___y_3227_ = v___y_3258_;
v___y_3228_ = v___y_3259_;
v___y_3229_ = v___y_3260_;
v___y_3230_ = v___y_3261_;
v___y_3231_ = v___y_3262_;
v___y_3232_ = v___y_3264_;
v___y_3233_ = v___y_3265_;
v___y_3234_ = v___y_3267_;
v___y_3235_ = v___y_3266_;
v___y_3236_ = v___y_3270_;
v___y_3237_ = v___y_3269_;
v___y_3238_ = v___y_3272_;
v___y_3239_ = v___y_3271_;
v_usingTk_x3f_3240_ = v___x_3283_;
v_usingArg_3241_ = v___x_3283_;
goto v___jp_3219_;
}
}
v___jp_3284_:
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = l_Lean_Syntax_getArg(v___y_3296_, v___y_3295_);
lean_dec(v___y_3295_);
v___x_3307_ = l_Lean_Syntax_isNone(v___x_3306_);
if (v___x_3307_ == 0)
{
uint8_t v___x_3308_; 
lean_inc(v___x_3306_);
v___x_3308_ = l_Lean_Syntax_matchesNull(v___x_3306_, v___x_3189_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; 
lean_dec(v___x_3306_);
lean_dec(v_only_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec(v___y_3285_);
lean_dec(v_tk_3188_);
v___x_3309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3309_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3310_ = l_Lean_Syntax_getArg(v___x_3306_, v___x_3187_);
lean_dec(v___x_3306_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
lean_inc(v___x_3310_);
v___x_3312_ = l_Lean_Syntax_isOfKind(v___x_3310_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec(v___x_3310_);
lean_dec(v_only_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec(v___y_3285_);
lean_dec(v_tk_3188_);
v___x_3313_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; lean_object* v_args_3315_; lean_object* v___x_3316_; 
v___x_3314_ = l_Lean_Syntax_getArg(v___x_3310_, v___x_3189_);
lean_dec(v___x_3310_);
v_args_3315_ = l_Lean_Syntax_getArgs(v___x_3314_);
lean_dec(v___x_3314_);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_args_3315_);
v___y_3253_ = v___y_3304_;
v___y_3254_ = v___y_3285_;
v___y_3255_ = v___y_3300_;
v___y_3256_ = v___y_3290_;
v___y_3257_ = v___y_3289_;
v___y_3258_ = v___y_3288_;
v___y_3259_ = v___y_3299_;
v___y_3260_ = v___y_3298_;
v___y_3261_ = v___y_3292_;
v___y_3262_ = v_only_3297_;
v___y_3263_ = v___y_3294_;
v___y_3264_ = v___y_3303_;
v___y_3265_ = v___y_3286_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___y_3287_;
v___y_3268_ = v___y_3296_;
v___y_3269_ = v___y_3305_;
v___y_3270_ = v___y_3291_;
v___y_3271_ = v___y_3301_;
v___y_3272_ = v___y_3293_;
v_args_3273_ = v___x_3316_;
goto v___jp_3252_;
}
}
}
else
{
lean_object* v___x_3317_; 
lean_dec(v___x_3306_);
v___x_3317_ = lean_box(0);
v___y_3253_ = v___y_3304_;
v___y_3254_ = v___y_3285_;
v___y_3255_ = v___y_3300_;
v___y_3256_ = v___y_3290_;
v___y_3257_ = v___y_3289_;
v___y_3258_ = v___y_3288_;
v___y_3259_ = v___y_3299_;
v___y_3260_ = v___y_3298_;
v___y_3261_ = v___y_3292_;
v___y_3262_ = v_only_3297_;
v___y_3263_ = v___y_3294_;
v___y_3264_ = v___y_3303_;
v___y_3265_ = v___y_3286_;
v___y_3266_ = v___y_3302_;
v___y_3267_ = v___y_3287_;
v___y_3268_ = v___y_3296_;
v___y_3269_ = v___y_3305_;
v___y_3270_ = v___y_3291_;
v___y_3271_ = v___y_3301_;
v___y_3272_ = v___y_3293_;
v_args_3273_ = v___x_3317_;
goto v___jp_3252_;
}
}
v___jp_3318_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3330_ = lean_unsigned_to_nat(3u);
v___x_3331_ = l_Lean_Syntax_getArg(v_stx_3169_, v___x_3330_);
lean_dec(v_stx_3169_);
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7));
lean_inc(v___x_3331_);
v___x_3333_ = l_Lean_Syntax_isOfKind(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
lean_dec(v___x_3331_);
lean_dec(v_unfold_3329_);
lean_dec(v___y_3326_);
lean_dec(v___y_3323_);
lean_dec(v_tk_3188_);
v___x_3334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3335_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3187_);
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9));
lean_inc(v___x_3335_);
v___x_3337_ = l_Lean_Syntax_isOfKind(v___x_3335_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_dec(v___x_3335_);
lean_dec(v___x_3331_);
lean_dec(v_unfold_3329_);
lean_dec(v___y_3326_);
lean_dec(v___y_3323_);
lean_dec(v_tk_3188_);
v___x_3338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3339_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3189_);
v___x_3340_ = l_Lean_Syntax_getArg(v___x_3331_, v___y_3323_);
v___x_3341_ = l_Lean_Syntax_isNone(v___x_3340_);
if (v___x_3341_ == 0)
{
uint8_t v___x_3342_; 
lean_inc(v___x_3340_);
v___x_3342_ = l_Lean_Syntax_matchesNull(v___x_3340_, v___x_3189_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; 
lean_dec(v___x_3340_);
lean_dec(v___x_3339_);
lean_dec(v___x_3335_);
lean_dec(v___x_3331_);
lean_dec(v_unfold_3329_);
lean_dec(v___y_3326_);
lean_dec(v___y_3323_);
lean_dec(v_tk_3188_);
v___x_3343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3343_;
}
else
{
lean_object* v_only_3344_; lean_object* v___x_3345_; 
v_only_3344_ = l_Lean_Syntax_getArg(v___x_3340_, v___x_3187_);
lean_dec(v___x_3340_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v_only_3344_);
lean_inc(v___y_3323_);
v___y_3285_ = v_unfold_3329_;
v___y_3286_ = v___x_3332_;
v___y_3287_ = v___y_3323_;
v___y_3288_ = v___x_3335_;
v___y_3289_ = v___x_3336_;
v___y_3290_ = v___x_3330_;
v___y_3291_ = v___y_3326_;
v___y_3292_ = v___x_3337_;
v___y_3293_ = v___x_3339_;
v___y_3294_ = v___y_3323_;
v___y_3295_ = v___x_3330_;
v___y_3296_ = v___x_3331_;
v_only_3297_ = v___x_3345_;
v___y_3298_ = v___y_3322_;
v___y_3299_ = v___y_3320_;
v___y_3300_ = v___y_3327_;
v___y_3301_ = v___y_3321_;
v___y_3302_ = v___y_3325_;
v___y_3303_ = v___y_3319_;
v___y_3304_ = v___y_3324_;
v___y_3305_ = v___y_3328_;
goto v___jp_3284_;
}
}
else
{
lean_object* v___x_3346_; 
lean_dec(v___x_3340_);
v___x_3346_ = lean_box(0);
lean_inc(v___y_3323_);
v___y_3285_ = v_unfold_3329_;
v___y_3286_ = v___x_3332_;
v___y_3287_ = v___y_3323_;
v___y_3288_ = v___x_3335_;
v___y_3289_ = v___x_3336_;
v___y_3290_ = v___x_3330_;
v___y_3291_ = v___y_3326_;
v___y_3292_ = v___x_3337_;
v___y_3293_ = v___x_3339_;
v___y_3294_ = v___y_3323_;
v___y_3295_ = v___x_3330_;
v___y_3296_ = v___x_3331_;
v_only_3297_ = v___x_3346_;
v___y_3298_ = v___y_3322_;
v___y_3299_ = v___y_3320_;
v___y_3300_ = v___y_3327_;
v___y_3301_ = v___y_3321_;
v___y_3302_ = v___y_3325_;
v___y_3303_ = v___y_3319_;
v___y_3304_ = v___y_3324_;
v___y_3305_ = v___y_3328_;
goto v___jp_3284_;
}
}
}
}
v___jp_3347_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3357_ = lean_unsigned_to_nat(2u);
v___x_3358_ = l_Lean_Syntax_getArg(v_stx_3169_, v___x_3357_);
v___x_3359_ = l_Lean_Syntax_isNone(v___x_3358_);
if (v___x_3359_ == 0)
{
uint8_t v___x_3360_; 
lean_inc(v___x_3358_);
v___x_3360_ = l_Lean_Syntax_matchesNull(v___x_3358_, v___x_3189_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
lean_dec(v___x_3358_);
lean_dec(v_squeeze_3348_);
lean_dec(v_tk_3188_);
lean_dec(v_stx_3169_);
v___x_3361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3361_;
}
else
{
lean_object* v_unfold_3362_; lean_object* v___x_3363_; 
v_unfold_3362_ = l_Lean_Syntax_getArg(v___x_3358_, v___x_3187_);
lean_dec(v___x_3358_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_unfold_3362_);
v___y_3319_ = v___y_3354_;
v___y_3320_ = v___y_3350_;
v___y_3321_ = v___y_3352_;
v___y_3322_ = v___y_3349_;
v___y_3323_ = v___x_3357_;
v___y_3324_ = v___y_3355_;
v___y_3325_ = v___y_3353_;
v___y_3326_ = v_squeeze_3348_;
v___y_3327_ = v___y_3351_;
v___y_3328_ = v___y_3356_;
v_unfold_3329_ = v___x_3363_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3364_; 
lean_dec(v___x_3358_);
v___x_3364_ = lean_box(0);
v___y_3319_ = v___y_3354_;
v___y_3320_ = v___y_3350_;
v___y_3321_ = v___y_3352_;
v___y_3322_ = v___y_3349_;
v___y_3323_ = v___x_3357_;
v___y_3324_ = v___y_3355_;
v___y_3325_ = v___y_3353_;
v___y_3326_ = v_squeeze_3348_;
v___y_3327_ = v___y_3351_;
v___y_3328_ = v___y_3356_;
v_unfold_3329_ = v___x_3364_;
goto v___jp_3318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3372_, lean_object* v_stx_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
uint8_t v_useReducible_boxed_3383_; lean_object* v_res_3384_; 
v_useReducible_boxed_3383_ = lean_unbox(v_useReducible_3372_);
v_res_3384_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3383_, v_stx_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3385_, lean_object* v_val_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3385_, v_val_3386_, v___y_3392_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3397_, lean_object* v_val_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3397_, v_val_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3409_, v___y_3417_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v_00_u03b1_3431_, lean_object* v_msg_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_3432_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v_00_u03b1_3443_, lean_object* v_msg_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_3443_, v_msg_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_00_u03b1_3455_, lean_object* v_x_3456_, lean_object* v_mkInfoTree_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_3456_, v_mkInfoTree_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_00_u03b1_3468_, lean_object* v_x_3469_, lean_object* v_mkInfoTree_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_3468_, v_x_3469_, v_mkInfoTree_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3481_, lean_object* v_x_3482_, lean_object* v_x_3483_, lean_object* v_x_3484_){
_start:
{
lean_object* v___x_3485_; 
v___x_3485_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3482_, v_x_3483_, v_x_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3486_, lean_object* v_m_3487_, lean_object* v_a_3488_){
_start:
{
uint8_t v___x_3489_; 
v___x_3489_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3487_, v_a_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3490_, lean_object* v_m_3491_, lean_object* v_a_3492_){
_start:
{
uint8_t v_res_3493_; lean_object* v_r_3494_; 
v_res_3493_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_3490_, v_m_3491_, v_a_3492_);
lean_dec_ref(v_a_3492_);
lean_dec_ref(v_m_3491_);
v_r_3494_ = lean_box(v_res_3493_);
return v_r_3494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3495_, lean_object* v_m_3496_, lean_object* v_a_3497_, lean_object* v_b_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_m_3496_, v_a_3497_, v_b_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3500_, v___y_3501_, v___y_3507_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(v_mvarId_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v_mvarId_3512_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3524_, v___y_3525_, v___y_3531_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_mvarId_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v_mvarId_3536_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3548_, lean_object* v_x_3549_, size_t v_x_3550_, size_t v_x_3551_, lean_object* v_x_3552_, lean_object* v_x_3553_){
_start:
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_3549_, v_x_3550_, v_x_3551_, v_x_3552_, v_x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_, lean_object* v_x_3560_){
_start:
{
size_t v_x_100080__boxed_3561_; size_t v_x_100081__boxed_3562_; lean_object* v_res_3563_; 
v_x_100080__boxed_3561_ = lean_unbox_usize(v_x_3557_);
lean_dec(v_x_3557_);
v_x_100081__boxed_3562_ = lean_unbox_usize(v_x_3558_);
lean_dec(v_x_3558_);
v_res_3563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_3555_, v_x_3556_, v_x_100080__boxed_3561_, v_x_100081__boxed_3562_, v_x_3559_, v_x_3560_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(lean_object* v_ref_3564_, lean_object* v_msgData_3565_, uint8_t v_severity_3566_, uint8_t v_isSilent_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_3564_, v_msgData_3565_, v_severity_3566_, v_isSilent_3567_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3578_, lean_object* v_msgData_3579_, lean_object* v_severity_3580_, lean_object* v_isSilent_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
uint8_t v_severity_boxed_3591_; uint8_t v_isSilent_boxed_3592_; lean_object* v_res_3593_; 
v_severity_boxed_3591_ = lean_unbox(v_severity_3580_);
v_isSilent_boxed_3592_ = lean_unbox(v_isSilent_3581_);
v_res_3593_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(v_ref_3578_, v_msgData_3579_, v_severity_boxed_3591_, v_isSilent_boxed_3592_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v_ref_3578_);
return v_res_3593_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3594_, lean_object* v_a_3595_, lean_object* v_x_3596_){
_start:
{
uint8_t v___x_3597_; 
v___x_3597_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3595_, v_x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3598_, lean_object* v_a_3599_, lean_object* v_x_3600_){
_start:
{
uint8_t v_res_3601_; lean_object* v_r_3602_; 
v_res_3601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3598_, v_a_3599_, v_x_3600_);
lean_dec(v_x_3600_);
lean_dec_ref(v_a_3599_);
v_r_3602_ = lean_box(v_res_3601_);
return v_r_3602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3603_, lean_object* v_data_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3606_, lean_object* v_n_3607_, lean_object* v_k_3608_, lean_object* v_v_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3607_, v_k_3608_, v_v_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3611_, size_t v_depth_3612_, lean_object* v_keys_3613_, lean_object* v_vals_3614_, lean_object* v_heq_3615_, lean_object* v_i_3616_, lean_object* v_entries_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3612_, v_keys_3613_, v_vals_3614_, v_i_3616_, v_entries_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3619_, lean_object* v_depth_3620_, lean_object* v_keys_3621_, lean_object* v_vals_3622_, lean_object* v_heq_3623_, lean_object* v_i_3624_, lean_object* v_entries_3625_){
_start:
{
size_t v_depth_boxed_3626_; lean_object* v_res_3627_; 
v_depth_boxed_3626_ = lean_unbox_usize(v_depth_3620_);
lean_dec(v_depth_3620_);
v_res_3627_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3619_, v_depth_boxed_3626_, v_keys_3621_, v_vals_3622_, v_heq_3623_, v_i_3624_, v_entries_3625_);
lean_dec_ref(v_vals_3622_);
lean_dec_ref(v_keys_3621_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3628_, lean_object* v_i_3629_, lean_object* v_source_3630_, lean_object* v_target_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3629_, v_source_3630_, v_target_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_, lean_object* v_x_3636_, lean_object* v_x_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3634_, v_x_3635_, v_x_3636_, v_x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3639_, lean_object* v_x_3640_, lean_object* v_x_3641_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3640_, v_x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_){
_start:
{
uint8_t v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = 1;
v___x_3654_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_3653_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_a_3657_);
lean_dec_ref(v_a_3656_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3675_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3678_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3679_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3675_, v___x_3676_, v___x_3677_, v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3710_ = l_Lean_addBuiltinDeclarationRanges(v___x_3708_, v___x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_3717_);
lean_dec(v_x_3717_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; uint8_t v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3771_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_3730_);
v___x_3772_ = l_Lean_Syntax_isOfKind(v_stx_3730_, v___x_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; 
lean_dec(v_stx_3730_);
v___x_3773_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; uint8_t v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; uint8_t v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; uint8_t v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; uint8_t v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v_tk_3901_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v_args_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___x_3961_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v_only_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v_unfold_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v_squeeze_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v___x_3774_ = lean_unsigned_to_nat(0u);
v_tk_3901_ = l_Lean_Syntax_getArg(v_stx_3730_, v___x_3774_);
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_4037_ = l_Lean_Syntax_getArg(v_stx_3730_, v___x_3961_);
v___x_4038_ = l_Lean_Syntax_isNone(v___x_4037_);
if (v___x_4038_ == 0)
{
uint8_t v___x_4039_; 
lean_inc(v___x_4037_);
v___x_4039_ = l_Lean_Syntax_matchesNull(v___x_4037_, v___x_3961_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; 
lean_dec(v___x_4037_);
lean_dec(v_tk_3901_);
lean_dec(v_stx_3730_);
v___x_4040_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4040_;
}
else
{
lean_object* v_squeeze_4041_; lean_object* v___x_4042_; 
v_squeeze_4041_ = l_Lean_Syntax_getArg(v___x_4037_, v___x_3774_);
lean_dec(v___x_4037_);
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v_squeeze_4041_);
v_squeeze_4020_ = v___x_4042_;
v___y_4021_ = v_a_3731_;
v___y_4022_ = v_a_3732_;
v___y_4023_ = v_a_3733_;
v___y_4024_ = v_a_3734_;
v___y_4025_ = v_a_3735_;
v___y_4026_ = v_a_3736_;
v___y_4027_ = v_a_3737_;
v___y_4028_ = v_a_3738_;
goto v___jp_4019_;
}
}
else
{
lean_object* v___x_4043_; 
lean_dec(v___x_4037_);
v___x_4043_ = lean_box(0);
v_squeeze_4020_ = v___x_4043_;
v___y_4021_ = v_a_3731_;
v___y_4022_ = v_a_3732_;
v___y_4023_ = v_a_3733_;
v___y_4024_ = v_a_3734_;
v___y_4025_ = v_a_3735_;
v___y_4026_ = v_a_3736_;
v___y_4027_ = v_a_3737_;
v___y_4028_ = v_a_3738_;
goto v___jp_4019_;
}
v___jp_3775_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_inc_ref(v___y_3788_);
v___x_3798_ = l_Array_append___redArg(v___y_3788_, v___y_3797_);
lean_dec_ref(v___y_3797_);
lean_inc(v___y_3782_);
lean_inc(v___y_3785_);
v___x_3799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3799_, 0, v___y_3785_);
lean_ctor_set(v___x_3799_, 1, v___y_3782_);
lean_ctor_set(v___x_3799_, 2, v___x_3798_);
if (lean_obj_tag(v___y_3784_) == 1)
{
lean_object* v_val_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_val_3800_ = lean_ctor_get(v___y_3784_, 0);
lean_inc(v_val_3800_);
lean_dec_ref_known(v___y_3784_, 1);
v___x_3801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
v___x_3802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3785_, 4);
v___x_3803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___y_3785_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
lean_inc_ref(v___y_3788_);
v___x_3804_ = l_Array_append___redArg(v___y_3788_, v_val_3800_);
lean_dec(v_val_3800_);
lean_inc(v___y_3782_);
v___x_3805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3805_, 0, v___y_3785_);
lean_ctor_set(v___x_3805_, 1, v___y_3782_);
lean_ctor_set(v___x_3805_, 2, v___x_3804_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___y_3785_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = l_Lean_Syntax_node3(v___y_3785_, v___x_3801_, v___x_3803_, v___x_3805_, v___x_3807_);
v___x_3809_ = l_Array_mkArray1___redArg(v___x_3808_);
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3777_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3782_;
v___y_3748_ = v___y_3783_;
v___y_3749_ = v___y_3785_;
v___y_3750_ = v___y_3786_;
v___y_3751_ = v___y_3787_;
v___y_3752_ = v___y_3788_;
v___y_3753_ = v___y_3789_;
v___y_3754_ = v___y_3791_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3792_;
v___y_3757_ = v___y_3794_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3795_;
v___y_3760_ = v___x_3799_;
v___y_3761_ = v___y_3796_;
v___y_3762_ = v___x_3809_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3810_; 
lean_dec(v___y_3784_);
v___x_3810_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3777_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3782_;
v___y_3748_ = v___y_3783_;
v___y_3749_ = v___y_3785_;
v___y_3750_ = v___y_3786_;
v___y_3751_ = v___y_3787_;
v___y_3752_ = v___y_3788_;
v___y_3753_ = v___y_3789_;
v___y_3754_ = v___y_3791_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3792_;
v___y_3757_ = v___y_3794_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3795_;
v___y_3760_ = v___x_3799_;
v___y_3761_ = v___y_3796_;
v___y_3762_ = v___x_3810_;
goto v___jp_3740_;
}
}
v___jp_3811_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_inc_ref(v___y_3824_);
v___x_3834_ = l_Array_append___redArg(v___y_3824_, v___y_3833_);
lean_dec_ref(v___y_3833_);
lean_inc(v___y_3819_);
lean_inc(v___y_3821_);
v___x_3835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3835_, 0, v___y_3821_);
lean_ctor_set(v___x_3835_, 1, v___y_3819_);
lean_ctor_set(v___x_3835_, 2, v___x_3834_);
if (lean_obj_tag(v___y_3813_) == 1)
{
lean_object* v_val_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_val_3836_ = lean_ctor_get(v___y_3813_, 0);
lean_inc(v_val_3836_);
lean_dec_ref_known(v___y_3813_, 1);
v___x_3837_ = l_Lean_SourceInfo_fromRef(v_val_3836_, v___x_3772_);
lean_dec(v_val_3836_);
v___x_3838_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3837_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___x_3840_ = l_Array_mkArray1___redArg(v___x_3839_);
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3814_;
v___y_3778_ = v___y_3815_;
v___y_3779_ = v___y_3816_;
v___y_3780_ = v___y_3817_;
v___y_3781_ = v___y_3818_;
v___y_3782_ = v___y_3819_;
v___y_3783_ = v___x_3835_;
v___y_3784_ = v___y_3820_;
v___y_3785_ = v___y_3821_;
v___y_3786_ = v___y_3822_;
v___y_3787_ = v___y_3823_;
v___y_3788_ = v___y_3824_;
v___y_3789_ = v___y_3825_;
v___y_3790_ = v___y_3827_;
v___y_3791_ = v___y_3826_;
v___y_3792_ = v___y_3828_;
v___y_3793_ = v___y_3830_;
v___y_3794_ = v___y_3829_;
v___y_3795_ = v___y_3831_;
v___y_3796_ = v___y_3832_;
v___y_3797_ = v___x_3840_;
goto v___jp_3775_;
}
else
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3813_);
lean_dec(v___y_3813_);
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3814_;
v___y_3778_ = v___y_3815_;
v___y_3779_ = v___y_3816_;
v___y_3780_ = v___y_3817_;
v___y_3781_ = v___y_3818_;
v___y_3782_ = v___y_3819_;
v___y_3783_ = v___x_3835_;
v___y_3784_ = v___y_3820_;
v___y_3785_ = v___y_3821_;
v___y_3786_ = v___y_3822_;
v___y_3787_ = v___y_3823_;
v___y_3788_ = v___y_3824_;
v___y_3789_ = v___y_3825_;
v___y_3790_ = v___y_3827_;
v___y_3791_ = v___y_3826_;
v___y_3792_ = v___y_3828_;
v___y_3793_ = v___y_3830_;
v___y_3794_ = v___y_3829_;
v___y_3795_ = v___y_3831_;
v___y_3796_ = v___y_3832_;
v___y_3797_ = v___x_3841_;
goto v___jp_3775_;
}
}
v___jp_3842_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_inc_ref(v___y_3854_);
v___x_3864_ = l_Array_append___redArg(v___y_3854_, v___y_3863_);
lean_dec_ref(v___y_3863_);
lean_inc(v___y_3849_);
lean_inc(v___y_3851_);
v___x_3865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3865_, 0, v___y_3851_);
lean_ctor_set(v___x_3865_, 1, v___y_3849_);
lean_ctor_set(v___x_3865_, 2, v___x_3864_);
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7));
if (lean_obj_tag(v___y_3862_) == 0)
{
lean_object* v___x_3867_; 
v___x_3867_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3812_ = v___x_3866_;
v___y_3813_ = v___y_3843_;
v___y_3814_ = v___y_3844_;
v___y_3815_ = v___y_3845_;
v___y_3816_ = v___y_3846_;
v___y_3817_ = v___y_3847_;
v___y_3818_ = v___y_3848_;
v___y_3819_ = v___y_3849_;
v___y_3820_ = v___y_3850_;
v___y_3821_ = v___y_3851_;
v___y_3822_ = v___y_3852_;
v___y_3823_ = v___y_3853_;
v___y_3824_ = v___y_3854_;
v___y_3825_ = v___y_3855_;
v___y_3826_ = v___y_3857_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3860_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___x_3865_;
v___y_3832_ = v___y_3861_;
v___y_3833_ = v___x_3867_;
goto v___jp_3811_;
}
else
{
lean_object* v_val_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_val_3868_ = lean_ctor_get(v___y_3862_, 0);
lean_inc(v_val_3868_);
lean_dec_ref_known(v___y_3862_, 1);
v___x_3869_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3870_ = lean_array_push(v___x_3869_, v_val_3868_);
v___y_3812_ = v___x_3866_;
v___y_3813_ = v___y_3843_;
v___y_3814_ = v___y_3844_;
v___y_3815_ = v___y_3845_;
v___y_3816_ = v___y_3846_;
v___y_3817_ = v___y_3847_;
v___y_3818_ = v___y_3848_;
v___y_3819_ = v___y_3849_;
v___y_3820_ = v___y_3850_;
v___y_3821_ = v___y_3851_;
v___y_3822_ = v___y_3852_;
v___y_3823_ = v___y_3853_;
v___y_3824_ = v___y_3854_;
v___y_3825_ = v___y_3855_;
v___y_3826_ = v___y_3857_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3860_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___x_3865_;
v___y_3832_ = v___y_3861_;
v___y_3833_ = v___x_3870_;
goto v___jp_3811_;
}
}
v___jp_3871_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_inc_ref(v___y_3882_);
v___x_3893_ = l_Array_append___redArg(v___y_3882_, v___y_3892_);
lean_dec_ref(v___y_3892_);
lean_inc(v___y_3877_);
lean_inc(v___y_3879_);
v___x_3894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3894_, 0, v___y_3879_);
lean_ctor_set(v___x_3894_, 1, v___y_3877_);
lean_ctor_set(v___x_3894_, 2, v___x_3893_);
if (lean_obj_tag(v___y_3886_) == 1)
{
lean_object* v_val_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_val_3895_ = lean_ctor_get(v___y_3886_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___y_3886_, 1);
v___x_3896_ = l_Lean_SourceInfo_fromRef(v_val_3895_, v___x_3772_);
lean_dec(v_val_3895_);
v___x_3897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_3898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = l_Array_mkArray1___redArg(v___x_3898_);
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___x_3894_;
v___y_3846_ = v___y_3874_;
v___y_3847_ = v___y_3875_;
v___y_3848_ = v___y_3876_;
v___y_3849_ = v___y_3877_;
v___y_3850_ = v___y_3878_;
v___y_3851_ = v___y_3879_;
v___y_3852_ = v___y_3880_;
v___y_3853_ = v___y_3881_;
v___y_3854_ = v___y_3882_;
v___y_3855_ = v___y_3883_;
v___y_3856_ = v___y_3885_;
v___y_3857_ = v___y_3884_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3889_;
v___y_3860_ = v___y_3888_;
v___y_3861_ = v___y_3890_;
v___y_3862_ = v___y_3891_;
v___y_3863_ = v___x_3899_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3886_);
lean_dec(v___y_3886_);
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___x_3894_;
v___y_3846_ = v___y_3874_;
v___y_3847_ = v___y_3875_;
v___y_3848_ = v___y_3876_;
v___y_3849_ = v___y_3877_;
v___y_3850_ = v___y_3878_;
v___y_3851_ = v___y_3879_;
v___y_3852_ = v___y_3880_;
v___y_3853_ = v___y_3881_;
v___y_3854_ = v___y_3882_;
v___y_3855_ = v___y_3883_;
v___y_3856_ = v___y_3885_;
v___y_3857_ = v___y_3884_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3889_;
v___y_3860_ = v___y_3888_;
v___y_3861_ = v___y_3890_;
v___y_3862_ = v___y_3891_;
v___y_3863_ = v___x_3900_;
goto v___jp_3842_;
}
}
v___jp_3902_:
{
lean_object* v_ref_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_ref_3918_ = lean_ctor_get(v___y_3909_, 5);
v___x_3919_ = 0;
v___x_3920_ = l_Lean_SourceInfo_fromRef(v_ref_3918_, v___x_3919_);
v___x_3921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3923_ = l_Lean_SourceInfo_fromRef(v_tk_3901_, v___x_3772_);
lean_dec(v_tk_3901_);
v___x_3924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v___x_3921_);
v___x_3925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_3926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_3908_) == 1)
{
lean_object* v_val_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_val_3927_ = lean_ctor_get(v___y_3908_, 0);
lean_inc(v_val_3927_);
lean_dec_ref_known(v___y_3908_, 1);
v___x_3928_ = l_Lean_SourceInfo_fromRef(v_val_3927_, v___x_3772_);
lean_dec(v_val_3927_);
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_3930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l_Array_mkArray1___redArg(v___x_3930_);
v___y_3872_ = v___y_3903_;
v___y_3873_ = v___y_3904_;
v___y_3874_ = v___y_3905_;
v___y_3875_ = v___y_3906_;
v___y_3876_ = v___x_3924_;
v___y_3877_ = v___x_3925_;
v___y_3878_ = v___y_3907_;
v___y_3879_ = v___x_3920_;
v___y_3880_ = v___y_3909_;
v___y_3881_ = v___y_3910_;
v___y_3882_ = v___x_3926_;
v___y_3883_ = v___x_3919_;
v___y_3884_ = v___y_3911_;
v___y_3885_ = v___y_3912_;
v___y_3886_ = v___y_3913_;
v___y_3887_ = v___y_3914_;
v___y_3888_ = v___y_3915_;
v___y_3889_ = v___x_3922_;
v___y_3890_ = v___y_3916_;
v___y_3891_ = v___y_3917_;
v___y_3892_ = v___x_3931_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3908_);
lean_dec(v___y_3908_);
v___y_3872_ = v___y_3903_;
v___y_3873_ = v___y_3904_;
v___y_3874_ = v___y_3905_;
v___y_3875_ = v___y_3906_;
v___y_3876_ = v___x_3924_;
v___y_3877_ = v___x_3925_;
v___y_3878_ = v___y_3907_;
v___y_3879_ = v___x_3920_;
v___y_3880_ = v___y_3909_;
v___y_3881_ = v___y_3910_;
v___y_3882_ = v___x_3926_;
v___y_3883_ = v___x_3919_;
v___y_3884_ = v___y_3911_;
v___y_3885_ = v___y_3912_;
v___y_3886_ = v___y_3913_;
v___y_3887_ = v___y_3914_;
v___y_3888_ = v___y_3915_;
v___y_3889_ = v___x_3922_;
v___y_3890_ = v___y_3916_;
v___y_3891_ = v___y_3917_;
v___y_3892_ = v___x_3932_;
goto v___jp_3871_;
}
}
v___jp_3933_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = lean_unsigned_to_nat(5u);
v___x_3950_ = l_Lean_Syntax_getArg(v___y_3936_, v___x_3949_);
lean_dec(v___y_3936_);
v___x_3951_ = l_Lean_Syntax_getOptional_x3f(v___y_3938_);
lean_dec(v___y_3938_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_box(0);
v___y_3903_ = v___y_3935_;
v___y_3904_ = v___y_3934_;
v___y_3905_ = v___y_3945_;
v___y_3906_ = v___y_3941_;
v___y_3907_ = v_args_3940_;
v___y_3908_ = v___y_3939_;
v___y_3909_ = v___y_3947_;
v___y_3910_ = v___y_3948_;
v___y_3911_ = v___y_3944_;
v___y_3912_ = v___x_3950_;
v___y_3913_ = v___y_3937_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3946_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___x_3952_;
goto v___jp_3902_;
}
else
{
lean_object* v_val_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
v_val_3953_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3951_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_val_3953_);
lean_dec(v___x_3951_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_val_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
v___y_3903_ = v___y_3935_;
v___y_3904_ = v___y_3934_;
v___y_3905_ = v___y_3945_;
v___y_3906_ = v___y_3941_;
v___y_3907_ = v_args_3940_;
v___y_3908_ = v___y_3939_;
v___y_3909_ = v___y_3947_;
v___y_3910_ = v___y_3948_;
v___y_3911_ = v___y_3944_;
v___y_3912_ = v___x_3950_;
v___y_3913_ = v___y_3937_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3946_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___x_3958_;
goto v___jp_3902_;
}
}
}
}
v___jp_3962_:
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3978_ = l_Lean_Syntax_getArg(v___y_3964_, v___y_3966_);
v___x_3979_ = l_Lean_Syntax_isNone(v___x_3978_);
if (v___x_3979_ == 0)
{
uint8_t v___x_3980_; 
lean_inc(v___x_3978_);
v___x_3980_ = l_Lean_Syntax_matchesNull(v___x_3978_, v___x_3961_);
if (v___x_3980_ == 0)
{
lean_object* v___x_3981_; 
lean_dec(v___x_3978_);
lean_dec(v_only_3969_);
lean_dec(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec(v_tk_3901_);
v___x_3981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3982_ = l_Lean_Syntax_getArg(v___x_3978_, v___x_3774_);
lean_dec(v___x_3978_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
lean_inc(v___x_3982_);
v___x_3984_ = l_Lean_Syntax_isOfKind(v___x_3982_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; 
lean_dec(v___x_3982_);
lean_dec(v_only_3969_);
lean_dec(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec(v_tk_3901_);
v___x_3985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3985_;
}
else
{
lean_object* v___x_3986_; lean_object* v_args_3987_; lean_object* v___x_3988_; 
v___x_3986_ = l_Lean_Syntax_getArg(v___x_3982_, v___x_3961_);
lean_dec(v___x_3982_);
v_args_3987_ = l_Lean_Syntax_getArgs(v___x_3986_);
lean_dec(v___x_3986_);
v___x_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3988_, 0, v_args_3987_);
v___y_3934_ = v___y_3963_;
v___y_3935_ = v_only_3969_;
v___y_3936_ = v___y_3964_;
v___y_3937_ = v___y_3965_;
v___y_3938_ = v___y_3967_;
v___y_3939_ = v___y_3968_;
v_args_3940_ = v___x_3988_;
v___y_3941_ = v___y_3970_;
v___y_3942_ = v___y_3971_;
v___y_3943_ = v___y_3972_;
v___y_3944_ = v___y_3973_;
v___y_3945_ = v___y_3974_;
v___y_3946_ = v___y_3975_;
v___y_3947_ = v___y_3976_;
v___y_3948_ = v___y_3977_;
goto v___jp_3933_;
}
}
}
else
{
lean_object* v___x_3989_; 
lean_dec(v___x_3978_);
v___x_3989_ = lean_box(0);
v___y_3934_ = v___y_3963_;
v___y_3935_ = v_only_3969_;
v___y_3936_ = v___y_3964_;
v___y_3937_ = v___y_3965_;
v___y_3938_ = v___y_3967_;
v___y_3939_ = v___y_3968_;
v_args_3940_ = v___x_3989_;
v___y_3941_ = v___y_3970_;
v___y_3942_ = v___y_3971_;
v___y_3943_ = v___y_3972_;
v___y_3944_ = v___y_3973_;
v___y_3945_ = v___y_3974_;
v___y_3946_ = v___y_3975_;
v___y_3947_ = v___y_3976_;
v___y_3948_ = v___y_3977_;
goto v___jp_3933_;
}
}
v___jp_3990_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4002_ = lean_unsigned_to_nat(3u);
v___x_4003_ = l_Lean_Syntax_getArg(v_stx_3730_, v___x_4002_);
lean_dec(v_stx_3730_);
v___x_4004_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4003_);
v___x_4005_ = l_Lean_Syntax_isOfKind(v___x_4003_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; 
lean_dec(v___x_4003_);
lean_dec(v_unfold_3993_);
lean_dec(v___y_3992_);
lean_dec(v_tk_3901_);
v___x_4006_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4006_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4007_ = l_Lean_Syntax_getArg(v___x_4003_, v___x_3774_);
v___x_4008_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9));
lean_inc(v___x_4007_);
v___x_4009_ = l_Lean_Syntax_isOfKind(v___x_4007_, v___x_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; 
lean_dec(v___x_4007_);
lean_dec(v___x_4003_);
lean_dec(v_unfold_3993_);
lean_dec(v___y_3992_);
lean_dec(v_tk_3901_);
v___x_4010_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4010_;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4011_ = l_Lean_Syntax_getArg(v___x_4003_, v___x_3961_);
v___x_4012_ = l_Lean_Syntax_getArg(v___x_4003_, v___y_3991_);
v___x_4013_ = l_Lean_Syntax_isNone(v___x_4012_);
if (v___x_4013_ == 0)
{
uint8_t v___x_4014_; 
lean_inc(v___x_4012_);
v___x_4014_ = l_Lean_Syntax_matchesNull(v___x_4012_, v___x_3961_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec(v___x_4012_);
lean_dec(v___x_4011_);
lean_dec(v___x_4007_);
lean_dec(v___x_4003_);
lean_dec(v_unfold_3993_);
lean_dec(v___y_3992_);
lean_dec(v_tk_3901_);
v___x_4015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4015_;
}
else
{
lean_object* v_only_4016_; lean_object* v___x_4017_; 
v_only_4016_ = l_Lean_Syntax_getArg(v___x_4012_, v___x_3774_);
lean_dec(v___x_4012_);
v___x_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4017_, 0, v_only_4016_);
v___y_3963_ = v___x_4007_;
v___y_3964_ = v___x_4003_;
v___y_3965_ = v_unfold_3993_;
v___y_3966_ = v___x_4002_;
v___y_3967_ = v___x_4011_;
v___y_3968_ = v___y_3992_;
v_only_3969_ = v___x_4017_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___y_3996_;
v___y_3973_ = v___y_3997_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3999_;
v___y_3976_ = v___y_4000_;
v___y_3977_ = v___y_4001_;
goto v___jp_3962_;
}
}
else
{
lean_object* v___x_4018_; 
lean_dec(v___x_4012_);
v___x_4018_ = lean_box(0);
v___y_3963_ = v___x_4007_;
v___y_3964_ = v___x_4003_;
v___y_3965_ = v_unfold_3993_;
v___y_3966_ = v___x_4002_;
v___y_3967_ = v___x_4011_;
v___y_3968_ = v___y_3992_;
v_only_3969_ = v___x_4018_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___y_3996_;
v___y_3973_ = v___y_3997_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3999_;
v___y_3976_ = v___y_4000_;
v___y_3977_ = v___y_4001_;
goto v___jp_3962_;
}
}
}
}
v___jp_4019_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v___x_4029_ = lean_unsigned_to_nat(2u);
v___x_4030_ = l_Lean_Syntax_getArg(v_stx_3730_, v___x_4029_);
v___x_4031_ = l_Lean_Syntax_isNone(v___x_4030_);
if (v___x_4031_ == 0)
{
uint8_t v___x_4032_; 
lean_inc(v___x_4030_);
v___x_4032_ = l_Lean_Syntax_matchesNull(v___x_4030_, v___x_3961_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; 
lean_dec(v___x_4030_);
lean_dec(v_squeeze_4020_);
lean_dec(v_tk_3901_);
lean_dec(v_stx_3730_);
v___x_4033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4033_;
}
else
{
lean_object* v_unfold_4034_; lean_object* v___x_4035_; 
v_unfold_4034_ = l_Lean_Syntax_getArg(v___x_4030_, v___x_3774_);
lean_dec(v___x_4030_);
v___x_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4035_, 0, v_unfold_4034_);
v___y_3991_ = v___x_4029_;
v___y_3992_ = v_squeeze_4020_;
v_unfold_3993_ = v___x_4035_;
v___y_3994_ = v___y_4021_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4023_;
v___y_3997_ = v___y_4024_;
v___y_3998_ = v___y_4025_;
v___y_3999_ = v___y_4026_;
v___y_4000_ = v___y_4027_;
v___y_4001_ = v___y_4028_;
goto v___jp_3990_;
}
}
else
{
lean_object* v___x_4036_; 
lean_dec(v___x_4030_);
v___x_4036_ = lean_box(0);
v___y_3991_ = v___x_4029_;
v___y_3992_ = v_squeeze_4020_;
v_unfold_3993_ = v___x_4036_;
v___y_3994_ = v___y_4021_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4023_;
v___y_3997_ = v___y_4024_;
v___y_3998_ = v___y_4025_;
v___y_3999_ = v___y_4026_;
v___y_4000_ = v___y_4027_;
v___y_4001_ = v___y_4028_;
goto v___jp_3990_;
}
}
}
v___jp_3740_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_inc_ref(v___y_3752_);
v___x_3763_ = l_Array_append___redArg(v___y_3752_, v___y_3762_);
lean_dec_ref(v___y_3762_);
lean_inc_n(v___y_3747_, 2);
lean_inc_n(v___y_3749_, 4);
v___x_3764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3764_, 0, v___y_3749_);
lean_ctor_set(v___x_3764_, 1, v___y_3747_);
lean_ctor_set(v___x_3764_, 2, v___x_3763_);
v___x_3765_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___y_3749_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = l_Lean_Syntax_node2(v___y_3749_, v___y_3747_, v___x_3766_, v___y_3755_);
lean_inc(v___y_3741_);
v___x_3768_ = l_Lean_Syntax_node5(v___y_3749_, v___y_3741_, v___y_3742_, v___y_3748_, v___y_3760_, v___x_3764_, v___x_3767_);
lean_inc(v___y_3758_);
v___x_3769_ = l_Lean_Syntax_node4(v___y_3749_, v___y_3758_, v___y_3746_, v___y_3743_, v___y_3759_, v___x_3768_);
v___x_3770_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3753_, v___x_3769_, v___y_3745_, v___y_3761_, v___y_3756_, v___y_3754_, v___y_3744_, v___y_3757_, v___y_3750_, v___y_3751_);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
lean_dec(v_a_4046_);
lean_dec_ref(v_a_4045_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4063_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4064_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4066_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4067_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4063_, v___x_4064_, v___x_4065_, v___x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4069_;
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
