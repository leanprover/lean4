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
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_93519__boxed_596_; uint8_t v___x_93520__boxed_597_; uint8_t v_useReducible_boxed_598_; uint8_t v___x_93524__boxed_599_; lean_object* v_res_600_; 
v___x_93519__boxed_596_ = lean_unbox(v___x_579_);
v___x_93520__boxed_597_ = lean_unbox(v___x_580_);
v_useReducible_boxed_598_ = lean_unbox(v_useReducible_585_);
v___x_93524__boxed_599_ = lean_unbox(v___x_586_);
v_res_600_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_577_, v_a_578_, v___x_93519__boxed_596_, v___x_93520__boxed_597_, v_a_581_, v_mvarCounter_582_, v___x_583_, v___x_584_, v_useReducible_boxed_598_, v___x_93524__boxed_599_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
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
size_t v_x_94802__boxed_1260_; size_t v_x_94803__boxed_1261_; lean_object* v_res_1262_; 
v_x_94802__boxed_1260_ = lean_unbox_usize(v_x_1256_);
lean_dec(v_x_1256_);
v_x_94803__boxed_1261_ = lean_unbox_usize(v_x_1257_);
lean_dec(v_x_1257_);
v_res_1262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1255_, v_x_94802__boxed_1260_, v_x_94803__boxed_1261_, v_x_1258_, v_x_1259_);
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
uint8_t v___y_95037__boxed_1352_; uint8_t v_suppressElabErrors_boxed_1353_; uint8_t v_res_1354_; lean_object* v_r_1355_; 
v___y_95037__boxed_1352_ = lean_unbox(v___y_1349_);
v_suppressElabErrors_boxed_1353_ = lean_unbox(v_suppressElabErrors_1350_);
v_res_1354_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v___y_95037__boxed_1352_, v_suppressElabErrors_boxed_1353_, v_x_1351_);
lean_dec(v_x_1351_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1357_, lean_object* v_msgData_1358_, uint8_t v_severity_1359_, uint8_t v_isSilent_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; uint8_t v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; uint8_t v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; uint8_t v___y_1431_; uint8_t v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; uint8_t v___y_1442_; uint8_t v___y_1443_; lean_object* v___y_1444_; uint8_t v___y_1445_; uint8_t v___x_1450_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1458_; uint8_t v___y_1460_; uint8_t v___x_1475_; 
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
lean_ctor_set(v___x_1392_, 1, v___y_1373_);
lean_inc_ref(v___y_1368_);
lean_inc_ref(v___y_1369_);
v___x_1393_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1393_, 0, v___y_1369_);
lean_ctor_set(v___x_1393_, 1, v___y_1367_);
lean_ctor_set(v___x_1393_, 2, v___y_1372_);
lean_ctor_set(v___x_1393_, 3, v___y_1368_);
lean_ctor_set(v___x_1393_, 4, v___x_1392_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*5, v___y_1371_);
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*5 + 1, v___y_1370_);
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
lean_inc_ref_n(v___y_1409_, 2);
v___x_1417_ = l_Lean_FileMap_toPosition(v___y_1409_, v___y_1404_);
lean_dec(v___y_1404_);
v___x_1418_ = l_Lean_FileMap_toPosition(v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
v___x_1420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1406_ == 0)
{
lean_del_object(v___x_1415_);
lean_dec_ref(v___y_1403_);
v___y_1367_ = v___x_1417_;
v___y_1368_ = v___x_1420_;
v___y_1369_ = v___y_1405_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1407_;
v___y_1372_ = v___x_1419_;
v___y_1373_ = v_a_1413_;
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
v___y_1368_ = v___x_1420_;
v___y_1369_ = v___y_1405_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1407_;
v___y_1372_ = v___x_1419_;
v___y_1373_ = v_a_1413_;
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
v___x_1436_ = l_Lean_Syntax_getTailPos_x3f(v___y_1430_, v___y_1432_);
lean_dec(v___y_1430_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_inc(v___y_1435_);
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1435_;
v___y_1405_ = v___y_1429_;
v___y_1406_ = v___y_1433_;
v___y_1407_ = v___y_1432_;
v___y_1408_ = v___y_1431_;
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
v___y_1404_ = v___y_1435_;
v___y_1405_ = v___y_1429_;
v___y_1406_ = v___y_1433_;
v___y_1407_ = v___y_1432_;
v___y_1408_ = v___y_1431_;
v___y_1409_ = v___y_1434_;
v___y_1410_ = v_val_1437_;
goto v___jp_1402_;
}
}
v___jp_1438_:
{
lean_object* v_ref_1446_; lean_object* v___x_1447_; 
v_ref_1446_ = l_Lean_replaceRef(v_ref_1357_, v___y_1440_);
v___x_1447_ = l_Lean_Syntax_getPos_x3f(v_ref_1446_, v___y_1443_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___y_1428_ = v___y_1439_;
v___y_1429_ = v___y_1441_;
v___y_1430_ = v_ref_1446_;
v___y_1431_ = v___y_1445_;
v___y_1432_ = v___y_1443_;
v___y_1433_ = v___y_1442_;
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
v___y_1429_ = v___y_1441_;
v___y_1430_ = v_ref_1446_;
v___y_1431_ = v___y_1445_;
v___y_1432_ = v___y_1443_;
v___y_1433_ = v___y_1442_;
v___y_1434_ = v___y_1444_;
v___y_1435_ = v_val_1449_;
goto v___jp_1427_;
}
}
v___jp_1451_:
{
if (v___y_1458_ == 0)
{
v___y_1439_ = v___y_1456_;
v___y_1440_ = v___y_1452_;
v___y_1441_ = v___y_1453_;
v___y_1442_ = v___y_1454_;
v___y_1443_ = v___y_1457_;
v___y_1444_ = v___y_1455_;
v___y_1445_ = v_severity_1359_;
goto v___jp_1438_;
}
else
{
v___y_1439_ = v___y_1456_;
v___y_1440_ = v___y_1452_;
v___y_1441_ = v___y_1453_;
v___y_1442_ = v___y_1454_;
v___y_1443_ = v___y_1457_;
v___y_1444_ = v___y_1455_;
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
v___y_1452_ = v_ref_1464_;
v___y_1453_ = v_fileName_1461_;
v___y_1454_ = v_suppressElabErrors_1465_;
v___y_1455_ = v_fileMap_1462_;
v___y_1456_ = v___f_1468_;
v___y_1457_ = v___y_1460_;
v___y_1458_ = v___x_1470_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = l_Lean_warningAsError;
v___x_1472_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_1463_, v___x_1471_);
v___y_1452_ = v_ref_1464_;
v___y_1453_ = v_fileName_1461_;
v___y_1454_ = v_suppressElabErrors_1465_;
v___y_1455_ = v_fileMap_1462_;
v___y_1456_ = v___f_1468_;
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
lean_object* v___x_1718_; lean_object* v_env_1719_; lean_object* v___x_1720_; lean_object* v_toEnvExtension_1721_; lean_object* v_asyncMode_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v_linterSets_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1718_ = lean_st_ref_get(v___y_1716_);
v_env_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc_ref(v_env_1719_);
lean_dec(v___x_1718_);
v___x_1720_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1721_ = lean_ctor_get(v___x_1720_, 0);
v_asyncMode_1722_ = lean_ctor_get(v_toEnvExtension_1721_, 2);
v___x_1723_ = lean_box(1);
v___x_1724_ = lean_box(0);
v_linterSets_1725_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1723_, v___x_1720_, v_env_1719_, v_asyncMode_1722_, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_o_1715_);
lean_ctor_set(v___x_1726_, 1, v_linterSets_1725_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_1728_, v___y_1729_);
lean_dec(v___y_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_options_1741_; lean_object* v___x_1742_; 
v_options_1741_ = lean_ctor_get(v___y_1738_, 2);
lean_inc_ref(v_options_1741_);
v___x_1742_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_1741_, v___y_1739_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1752_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2));
v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
return v___x_1758_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4));
v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6));
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_usingArg_1774_, lean_object* v_snd_1775_, uint8_t v___x_1776_, uint8_t v___x_1777_, lean_object* v___x_1778_, uint8_t v_useReducible_1779_, uint8_t v___x_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v_simprocs_1783_, lean_object* v_discharge_x3f_1784_, lean_object* v_snd_1785_, lean_object* v___x_1786_, lean_object* v___f_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; 
if (lean_obj_tag(v_usingArg_1774_) == 1)
{
lean_object* v_val_1978_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___x_2030_; lean_object* v_infoState_2031_; uint8_t v_enabled_2032_; 
v_val_1978_ = lean_ctor_get(v_usingArg_1774_, 0);
lean_inc(v_val_1978_);
lean_dec_ref_known(v_usingArg_1774_, 1);
v___x_2030_ = lean_st_ref_get(v___y_1795_);
v_infoState_2031_ = lean_ctor_get(v___x_2030_, 7);
lean_inc_ref(v_infoState_2031_);
lean_dec(v___x_2030_);
v_enabled_2032_ = lean_ctor_get_uint8(v_infoState_2031_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2031_);
if (v_enabled_2032_ == 0)
{
lean_dec_ref(v___f_1787_);
v___y_1980_ = v___y_1788_;
v___y_1981_ = v___y_1789_;
v___y_1982_ = v___y_1790_;
v___y_1983_ = v___y_1791_;
v___y_1984_ = v___y_1792_;
v___y_1985_ = v___y_1793_;
v___y_1986_ = v___y_1794_;
v___y_1987_ = v___y_1795_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_2033_; lean_object* v_a_2034_; lean_object* v___f_2035_; lean_object* v___x_2036_; 
v___x_2033_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1795_);
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___f_2035_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2035_, 0, v_a_2034_);
v___x_2036_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_2035_, v___f_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_dec_ref_known(v___x_2036_, 1);
v___y_1980_ = v___y_1788_;
v___y_1981_ = v___y_1789_;
v___y_1982_ = v___y_1790_;
v___y_1983_ = v___y_1791_;
v___y_1984_ = v___y_1792_;
v___y_1985_ = v___y_1793_;
v___y_1986_ = v___y_1794_;
v___y_1987_ = v___y_1795_;
goto v___jp_1979_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_val_1978_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
v___jp_1979_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_st_ref_get(v___y_1985_);
v___x_1989_ = lean_box(0);
v___x_1990_ = l_Lean_Elab_Tactic_elabTerm(v_val_1978_, v___x_1989_, v___x_1776_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_n(v_a_1991_, 2);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_1775_, v_a_1991_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_mctx_1993_; lean_object* v_a_1994_; uint8_t v___x_1995_; 
v_mctx_1993_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_mctx_1993_);
lean_dec(v___x_1988_);
v_a_1994_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1995_ = lean_unbox(v_a_1994_);
lean_dec(v_a_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v_mctx_1993_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
v___x_1996_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
v___x_1997_ = l_Lean_indentExpr(v_a_1991_);
v___x_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
v___x_2000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1998_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = l_Lean_Expr_mvar___override(v_snd_1775_);
v___x_2002_ = l_Lean_MessageData_ofExpr(v___x_2001_);
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_2003_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_object* v_mvarCounter_2013_; 
v_mvarCounter_2013_ = lean_ctor_get(v_mctx_1993_, 3);
lean_inc(v_mvarCounter_2013_);
lean_dec_ref(v_mctx_1993_);
lean_inc(v_a_1991_);
v___y_1862_ = v_a_1991_;
v___y_1863_ = v_mvarCounter_2013_;
v___y_1864_ = v___x_1989_;
v___y_1865_ = v_a_1991_;
v___y_1866_ = v___x_1989_;
v___y_1867_ = v___y_1980_;
v___y_1868_ = v___y_1981_;
v___y_1869_ = v___y_1982_;
v___y_1870_ = v___y_1983_;
v___y_1871_ = v___y_1984_;
v___y_1872_ = v___y_1985_;
v___y_1873_ = v___y_1986_;
v___y_1874_ = v___y_1987_;
goto v___jp_1861_;
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_a_1991_);
lean_dec(v___x_1988_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_2014_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1992_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1992_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v___x_1988_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_2022_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1990_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1990_);
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
}
else
{
lean_object* v_lctx_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec_ref(v___f_1787_);
lean_dec_ref(v___x_1778_);
lean_dec(v_usingArg_1774_);
v_lctx_2045_ = lean_ctor_get(v___y_1792_, 2);
v___x_2046_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13));
v___x_2047_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2045_, v___x_2046_);
if (lean_obj_tag(v___x_2047_) == 1)
{
lean_object* v_val_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_val_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_LocalDecl_fvarId(v_val_2048_);
lean_dec(v_val_2048_);
v___x_2050_ = lean_mk_empty_array_with_capacity(v___x_1781_);
v___x_2051_ = lean_array_push(v___x_2050_, v___x_2049_);
lean_inc_ref(v_snd_1785_);
v___x_2052_ = l_Lean_Meta_simpGoal(v_snd_1775_, v___x_1782_, v_simprocs_1783_, v_discharge_x3f_1784_, v___x_1777_, v___x_2051_, v_snd_1785_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2081_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2081_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2081_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_fst_2057_; 
v_fst_2057_ = lean_ctor_get(v_a_2053_, 0);
if (lean_obj_tag(v_fst_2057_) == 1)
{
lean_object* v_val_2058_; lean_object* v_snd_2059_; lean_object* v_snd_2060_; lean_object* v___x_2061_; 
lean_del_object(v___x_2055_);
lean_dec_ref(v_snd_1785_);
v_val_2058_ = lean_ctor_get(v_fst_2057_, 0);
lean_inc(v_val_2058_);
v_snd_2059_ = lean_ctor_get(v_a_2053_, 1);
lean_inc(v_snd_2059_);
lean_dec(v_a_2053_);
v_snd_2060_ = lean_ctor_get(v_val_2058_, 1);
lean_inc(v_snd_2060_);
lean_dec(v_val_2058_);
v___x_2061_ = l_Lean_MVarId_assumption(v_snd_2060_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v___x_2061_, 0);
lean_dec(v_unused_2069_);
v___x_2063_ = v___x_2061_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_dec(v___x_2061_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v_snd_2059_);
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_snd_2059_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_snd_2059_);
v_a_2070_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2061_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2061_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v___x_2079_; 
lean_dec(v_a_2053_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v_snd_1785_);
v___x_2079_ = v___x_2055_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_snd_1785_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_snd_1785_);
v_a_2082_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2052_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2052_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
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
lean_object* v___x_2090_; 
lean_dec(v___x_2047_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
v___x_2090_ = l_Lean_MVarId_assumption(v_snd_1775_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v___x_2090_, 0);
lean_dec(v_unused_2098_);
v___x_2092_ = v___x_2090_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_dec(v___x_2090_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v_snd_1785_);
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_snd_1785_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_snd_1785_);
v_a_2099_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2090_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2090_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
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
}
v___jp_1797_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v___x_1801_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_1775_, v___y_1798_, v___y_1800_);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1801_, 0);
lean_dec(v_unused_1809_);
v___x_1803_ = v___x_1801_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v___x_1801_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___y_1799_);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___y_1799_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
v___jp_1810_:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Core_mkFreshUserName(v___y_1820_, v___y_1815_, v___y_1825_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc_n(v_a_1828_, 2);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = l_Lean_MVarId_rename(v___y_1818_, v___y_1826_, v_a_1828_, v___y_1819_, v___y_1824_, v___y_1815_, v___y_1825_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___f_1835_; lean_object* v___x_1836_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc_n(v_a_1830_, 2);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = lean_box(v___x_1776_);
v___x_1832_ = lean_box(v___x_1777_);
v___x_1833_ = lean_box(v_useReducible_1779_);
v___x_1834_ = lean_box(v___x_1780_);
v___f_1835_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 19, 10);
lean_closure_set(v___f_1835_, 0, v_a_1830_);
lean_closure_set(v___f_1835_, 1, v_a_1828_);
lean_closure_set(v___f_1835_, 2, v___x_1831_);
lean_closure_set(v___f_1835_, 3, v___x_1832_);
lean_closure_set(v___f_1835_, 4, v___y_1811_);
lean_closure_set(v___f_1835_, 5, v___y_1812_);
lean_closure_set(v___f_1835_, 6, v___x_1778_);
lean_closure_set(v___f_1835_, 7, v___y_1813_);
lean_closure_set(v___f_1835_, 8, v___x_1833_);
lean_closure_set(v___f_1835_, 9, v___x_1834_);
v___x_1836_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1830_, v___f_1835_, v___y_1822_, v___y_1821_, v___y_1814_, v___y_1817_, v___y_1819_, v___y_1824_, v___y_1815_, v___y_1825_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_dec_ref_known(v___x_1836_, 1);
v___y_1798_ = v___y_1816_;
v___y_1799_ = v___y_1823_;
v___y_1800_ = v___y_1824_;
goto v___jp_1797_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v___y_1823_);
lean_dec_ref(v___y_1816_);
lean_dec(v_snd_1775_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_a_1828_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_1845_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1829_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1829_);
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
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_1853_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1827_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1827_);
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
v___jp_1861_:
{
lean_object* v___x_1875_; 
lean_inc(v_snd_1775_);
v___x_1875_ = l_Lean_MVarId_getType(v_snd_1775_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
lean_inc(v_snd_1775_);
v___x_1877_ = l_Lean_MVarId_getTag(v_snd_1775_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1876_, v_a_1878_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1881_ = l_Lean_Expr_mvarId_x21(v_a_1880_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1));
lean_inc_ref(v___y_1865_);
v___x_1883_ = l_Lean_MVarId_note(v___x_1881_, v___x_1882_, v___y_1865_, v___y_1866_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_fst_1885_; lean_object* v_snd_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1945_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_fst_1885_ = lean_ctor_get(v_a_1884_, 0);
v_snd_1886_ = lean_ctor_get(v_a_1884_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1888_ = v_a_1884_;
v_isShared_1889_ = v_isSharedCheck_1945_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snd_1886_);
lean_inc(v_fst_1885_);
lean_dec(v_a_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1945_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_mk_empty_array_with_capacity(v___x_1781_);
lean_inc(v_fst_1885_);
v___x_1891_ = lean_array_push(v___x_1890_, v_fst_1885_);
v___x_1892_ = l_Lean_Meta_simpGoal(v_snd_1886_, v___x_1782_, v_simprocs_1783_, v_discharge_x3f_1784_, v___x_1777_, v___x_1891_, v_snd_1785_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v_fst_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v_fst_1894_ = lean_ctor_get(v_a_1893_, 0);
if (lean_obj_tag(v_fst_1894_) == 0)
{
lean_object* v_snd_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_fst_1885_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___x_1778_);
v_snd_1895_ = lean_ctor_get(v_a_1893_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_a_1893_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v_a_1893_, 0);
lean_dec(v_unused_1929_);
v___x_1897_ = v_a_1893_;
v_isShared_1898_ = v_isSharedCheck_1928_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_snd_1895_);
lean_dec(v_a_1893_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1928_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v_a_1900_; uint8_t v___x_1901_; 
v___x_1899_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1900_);
lean_dec(v_a_1900_);
if (v___x_1901_ == 0)
{
lean_del_object(v___x_1897_);
lean_del_object(v___x_1888_);
lean_dec_ref(v___y_1865_);
v___y_1798_ = v_a_1880_;
v___y_1799_ = v_snd_1895_;
v___y_1800_ = v___y_1872_;
goto v___jp_1797_;
}
else
{
if (lean_obj_tag(v___y_1865_) == 1)
{
lean_object* v_fvarId_1902_; lean_object* v_lctx_1903_; lean_object* v___x_1904_; 
v_fvarId_1902_ = lean_ctor_get(v___y_1865_, 0);
v_lctx_1903_ = lean_ctor_get(v___y_1871_, 2);
lean_inc(v_fvarId_1902_);
lean_inc_ref(v_lctx_1903_);
v___x_1904_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1903_, v_fvarId_1902_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_dec_ref_known(v___y_1865_, 1);
lean_del_object(v___x_1897_);
lean_del_object(v___x_1888_);
v___y_1798_ = v_a_1880_;
v___y_1799_ = v_snd_1895_;
v___y_1800_ = v___y_1872_;
goto v___jp_1797_;
}
else
{
lean_dec_ref_known(v___x_1904_, 1);
if (v___x_1780_ == 0)
{
lean_dec_ref_known(v___y_1865_, 1);
lean_del_object(v___x_1897_);
lean_del_object(v___x_1888_);
v___y_1798_ = v_a_1880_;
v___y_1799_ = v_snd_1895_;
v___y_1800_ = v___y_1872_;
goto v___jp_1797_;
}
else
{
lean_object* v_ref_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v_ref_1905_ = lean_ctor_get(v___y_1873_, 5);
v___x_1906_ = l_linter_unnecessarySimpa;
v___x_1907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_1908_ = l_Lean_MessageData_ofExpr(v___y_1865_);
lean_inc_ref(v___x_1908_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set_tag(v___x_1897_, 7);
lean_ctor_set(v___x_1897_, 1, v___x_1908_);
lean_ctor_set(v___x_1897_, 0, v___x_1907_);
v___x_1910_ = v___x_1897_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 7);
lean_ctor_set(v___x_1888_, 1, v___x_1911_);
lean_ctor_set(v___x_1888_, 0, v___x_1910_);
v___x_1913_ = v___x_1888_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___x_1908_);
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_1906_, v_ref_1905_, v___x_1916_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_dec_ref_known(v___x_1917_, 1);
v___y_1798_ = v_a_1880_;
v___y_1799_ = v_snd_1895_;
v___y_1800_ = v___y_1872_;
goto v___jp_1797_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_snd_1895_);
lean_dec(v_a_1880_);
lean_dec(v_snd_1775_);
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
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
lean_del_object(v___x_1897_);
lean_del_object(v___x_1888_);
lean_dec_ref(v___y_1865_);
v___y_1798_ = v_a_1880_;
v___y_1799_ = v_snd_1895_;
v___y_1800_ = v___y_1872_;
goto v___jp_1797_;
}
}
}
}
else
{
lean_object* v_val_1930_; lean_object* v_snd_1931_; lean_object* v_fst_1932_; lean_object* v_snd_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
lean_del_object(v___x_1888_);
lean_dec_ref(v___y_1865_);
v_val_1930_ = lean_ctor_get(v_fst_1894_, 0);
lean_inc(v_val_1930_);
v_snd_1931_ = lean_ctor_get(v_a_1893_, 1);
lean_inc(v_snd_1931_);
lean_dec(v_a_1893_);
v_fst_1932_ = lean_ctor_get(v_val_1930_, 0);
lean_inc(v_fst_1932_);
v_snd_1933_ = lean_ctor_get(v_val_1930_, 1);
lean_inc(v_snd_1933_);
lean_dec(v_val_1930_);
v___x_1934_ = lean_array_get_size(v_fst_1932_);
v___x_1935_ = lean_nat_dec_lt(v___x_1786_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_dec(v_fst_1932_);
v___y_1811_ = v___y_1862_;
v___y_1812_ = v___y_1863_;
v___y_1813_ = v___y_1864_;
v___y_1814_ = v___y_1869_;
v___y_1815_ = v___y_1873_;
v___y_1816_ = v_a_1880_;
v___y_1817_ = v___y_1870_;
v___y_1818_ = v_snd_1933_;
v___y_1819_ = v___y_1871_;
v___y_1820_ = v___x_1882_;
v___y_1821_ = v___y_1868_;
v___y_1822_ = v___y_1867_;
v___y_1823_ = v_snd_1931_;
v___y_1824_ = v___y_1872_;
v___y_1825_ = v___y_1874_;
v___y_1826_ = v_fst_1885_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1936_; 
lean_dec(v_fst_1885_);
v___x_1936_ = lean_array_fget(v_fst_1932_, v___x_1786_);
lean_dec(v_fst_1932_);
v___y_1811_ = v___y_1862_;
v___y_1812_ = v___y_1863_;
v___y_1813_ = v___y_1864_;
v___y_1814_ = v___y_1869_;
v___y_1815_ = v___y_1873_;
v___y_1816_ = v_a_1880_;
v___y_1817_ = v___y_1870_;
v___y_1818_ = v_snd_1933_;
v___y_1819_ = v___y_1871_;
v___y_1820_ = v___x_1882_;
v___y_1821_ = v___y_1868_;
v___y_1822_ = v___y_1867_;
v___y_1823_ = v_snd_1931_;
v___y_1824_ = v___y_1872_;
v___y_1825_ = v___y_1874_;
v___y_1826_ = v___x_1936_;
goto v___jp_1810_;
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1888_);
lean_dec(v_fst_1885_);
lean_dec(v_a_1880_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_1937_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1892_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1892_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_a_1880_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_1946_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1883_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1883_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_1954_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1879_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1879_);
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
lean_dec(v_a_1876_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_1962_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1877_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1877_);
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
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_snd_1785_);
lean_dec(v_discharge_x3f_1784_);
lean_dec_ref(v_simprocs_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1778_);
lean_dec(v_snd_1775_);
v_a_1970_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1875_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1875_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2107_ = _args[0];
lean_object* v_snd_2108_ = _args[1];
lean_object* v___x_2109_ = _args[2];
lean_object* v___x_2110_ = _args[3];
lean_object* v___x_2111_ = _args[4];
lean_object* v_useReducible_2112_ = _args[5];
lean_object* v___x_2113_ = _args[6];
lean_object* v___x_2114_ = _args[7];
lean_object* v___x_2115_ = _args[8];
lean_object* v_simprocs_2116_ = _args[9];
lean_object* v_discharge_x3f_2117_ = _args[10];
lean_object* v_snd_2118_ = _args[11];
lean_object* v___x_2119_ = _args[12];
lean_object* v___f_2120_ = _args[13];
lean_object* v___y_2121_ = _args[14];
lean_object* v___y_2122_ = _args[15];
lean_object* v___y_2123_ = _args[16];
lean_object* v___y_2124_ = _args[17];
lean_object* v___y_2125_ = _args[18];
lean_object* v___y_2126_ = _args[19];
lean_object* v___y_2127_ = _args[20];
lean_object* v___y_2128_ = _args[21];
lean_object* v___y_2129_ = _args[22];
_start:
{
uint8_t v___x_95754__boxed_2130_; uint8_t v___x_95755__boxed_2131_; uint8_t v_useReducible_boxed_2132_; uint8_t v___x_95757__boxed_2133_; lean_object* v_res_2134_; 
v___x_95754__boxed_2130_ = lean_unbox(v___x_2109_);
v___x_95755__boxed_2131_ = lean_unbox(v___x_2110_);
v_useReducible_boxed_2132_ = lean_unbox(v_useReducible_2112_);
v___x_95757__boxed_2133_ = lean_unbox(v___x_2113_);
v_res_2134_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2107_, v_snd_2108_, v___x_95754__boxed_2130_, v___x_95755__boxed_2131_, v___x_2111_, v_useReducible_boxed_2132_, v___x_95757__boxed_2133_, v___x_2114_, v___x_2115_, v_simprocs_2116_, v_discharge_x3f_2117_, v_snd_2118_, v___x_2119_, v___f_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___x_2119_);
lean_dec(v___x_2114_);
return v_res_2134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2135_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_unsigned_to_nat(32u);
v___x_2139_ = lean_mk_empty_array_with_capacity(v___x_2138_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2145_ = l_Lean_MessageData_ofFormat(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v___x_2146_, lean_object* v_tk_2147_, lean_object* v___x_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_simprocs_2151_, uint8_t v___x_2152_, lean_object* v_usingArg_2153_, uint8_t v___x_2154_, lean_object* v___x_2155_, uint8_t v_useReducible_2156_, uint8_t v___x_2157_, lean_object* v___x_2158_, lean_object* v_usingTk_x3f_2159_, lean_object* v_discharge_x3f_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___y_2171_; 
if (lean_obj_tag(v_usingTk_x3f_2159_) == 0)
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_box(0);
v___y_2171_ = v___x_2276_;
goto v___jp_2170_;
}
else
{
lean_object* v_val_2277_; 
v_val_2277_ = lean_ctor_get(v_usingTk_x3f_2159_, 0);
lean_inc(v_val_2277_);
lean_dec_ref_known(v_usingTk_x3f_2159_, 1);
v___y_2171_ = v_val_2277_;
goto v___jp_2170_;
}
v___jp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2172_ = lean_mk_empty_array_with_capacity(v___x_2146_);
v___x_2173_ = lean_array_push(v___x_2172_, v_tk_2147_);
v___x_2174_ = lean_array_push(v___x_2173_, v___y_2171_);
v___x_2175_ = lean_box(2);
v___x_2176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2148_);
lean_ctor_set(v___x_2176_, 2, v___x_2174_);
v___x_2177_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2176_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2162_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = lean_mk_empty_array_with_capacity(v___x_2149_);
v___x_2182_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
lean_inc_n(v___x_2149_, 3);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2149_);
v___x_2184_ = lean_unsigned_to_nat(32u);
v___x_2185_ = lean_mk_empty_array_with_capacity(v___x_2184_);
v___x_2186_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
v___x_2187_ = ((size_t)5ULL);
v___x_2188_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2185_);
lean_ctor_set(v___x_2188_, 2, v___x_2149_);
lean_ctor_set(v___x_2188_, 3, v___x_2149_);
lean_ctor_set_usize(v___x_2188_, 4, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2182_);
lean_ctor_set(v___x_2189_, 1, v___x_2182_);
lean_ctor_set(v___x_2189_, 2, v___x_2182_);
lean_ctor_set(v___x_2189_, 3, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2183_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
lean_inc_ref(v___x_2190_);
lean_inc(v_discharge_x3f_2160_);
lean_inc_ref(v_simprocs_2151_);
lean_inc_ref(v___x_2150_);
v___x_2191_ = l_Lean_Meta_simpGoal(v_a_2180_, v___x_2150_, v_simprocs_2151_, v_discharge_x3f_2160_, v___x_2152_, v___x_2181_, v___x_2190_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v_fst_2193_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2191_, 1);
v_fst_2193_ = lean_ctor_get(v_a_2192_, 0);
if (lean_obj_tag(v_fst_2193_) == 1)
{
lean_object* v_val_2194_; lean_object* v_snd_2195_; lean_object* v_snd_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref_known(v___x_2190_, 2);
v_val_2194_ = lean_ctor_get(v_fst_2193_, 0);
lean_inc(v_val_2194_);
v_snd_2195_ = lean_ctor_get(v_a_2192_, 1);
lean_inc(v_snd_2195_);
lean_dec(v_a_2192_);
v_snd_2196_ = lean_ctor_get(v_val_2194_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_val_2194_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v_val_2194_, 0);
lean_dec(v_unused_2221_);
v___x_2198_ = v_val_2194_;
v_isShared_2199_ = v_isSharedCheck_2220_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_snd_2196_);
lean_dec(v_val_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2220_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2200_ = lean_box(0);
lean_inc(v_snd_2196_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set_tag(v___x_2198_, 1);
lean_ctor_set(v___x_2198_, 1, v___x_2200_);
lean_ctor_set(v___x_2198_, 0, v_snd_2196_);
v___x_2202_ = v___x_2198_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_snd_2196_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2202_, v___y_2162_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___y_2209_; lean_object* v___x_2210_; 
lean_dec_ref_known(v___x_2203_, 1);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2204_, 0, v_a_2178_);
v___x_2205_ = lean_box(v___x_2152_);
v___x_2206_ = lean_box(v___x_2154_);
v___x_2207_ = lean_box(v_useReducible_2156_);
v___x_2208_ = lean_box(v___x_2157_);
lean_inc(v_snd_2196_);
v___y_2209_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 23, 14);
lean_closure_set(v___y_2209_, 0, v_usingArg_2153_);
lean_closure_set(v___y_2209_, 1, v_snd_2196_);
lean_closure_set(v___y_2209_, 2, v___x_2205_);
lean_closure_set(v___y_2209_, 3, v___x_2206_);
lean_closure_set(v___y_2209_, 4, v___x_2155_);
lean_closure_set(v___y_2209_, 5, v___x_2207_);
lean_closure_set(v___y_2209_, 6, v___x_2208_);
lean_closure_set(v___y_2209_, 7, v___x_2158_);
lean_closure_set(v___y_2209_, 8, v___x_2150_);
lean_closure_set(v___y_2209_, 9, v_simprocs_2151_);
lean_closure_set(v___y_2209_, 10, v_discharge_x3f_2160_);
lean_closure_set(v___y_2209_, 11, v_snd_2195_);
lean_closure_set(v___y_2209_, 12, v___x_2149_);
lean_closure_set(v___y_2209_, 13, v___f_2204_);
v___x_2210_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_2196_, v___y_2209_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2210_;
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_snd_2196_);
lean_dec(v_snd_2195_);
lean_dec(v_a_2178_);
lean_dec(v_discharge_x3f_2160_);
lean_dec(v___x_2158_);
lean_dec_ref(v___x_2155_);
lean_dec(v_usingArg_2153_);
lean_dec_ref(v_simprocs_2151_);
lean_dec_ref(v___x_2150_);
lean_dec(v___x_2149_);
v_a_2211_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2203_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2203_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
else
{
lean_object* v___x_2222_; lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_a_2192_);
lean_dec(v_a_2178_);
lean_dec(v_discharge_x3f_2160_);
lean_dec(v___x_2158_);
lean_dec_ref(v___x_2155_);
lean_dec(v_usingArg_2153_);
lean_dec_ref(v_simprocs_2151_);
lean_dec_ref(v___x_2150_);
lean_dec(v___x_2149_);
v___x_2222_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2251_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2251_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2223_);
lean_dec(v_a_2223_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2229_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2190_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2190_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
lean_object* v_ref_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_del_object(v___x_2225_);
v_ref_2231_ = lean_ctor_get(v___y_2167_, 5);
v___x_2232_ = l_linter_unnecessarySimpa;
v___x_2233_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
v___x_2234_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2232_, v_ref_2231_, v___x_2233_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v___x_2234_, 0);
lean_dec(v_unused_2242_);
v___x_2236_ = v___x_2234_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_dec(v___x_2234_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2190_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2190_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref_known(v___x_2190_, 2);
v_a_2243_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2234_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2234_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref_known(v___x_2190_, 2);
lean_dec(v_a_2178_);
lean_dec(v_discharge_x3f_2160_);
lean_dec(v___x_2158_);
lean_dec_ref(v___x_2155_);
lean_dec(v_usingArg_2153_);
lean_dec_ref(v_simprocs_2151_);
lean_dec_ref(v___x_2150_);
lean_dec(v___x_2149_);
v_a_2252_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2191_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2191_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_a_2178_);
lean_dec(v_discharge_x3f_2160_);
lean_dec(v___x_2158_);
lean_dec_ref(v___x_2155_);
lean_dec(v_usingArg_2153_);
lean_dec_ref(v_simprocs_2151_);
lean_dec_ref(v___x_2150_);
lean_dec(v___x_2149_);
v_a_2260_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2179_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2179_);
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
lean_dec(v_discharge_x3f_2160_);
lean_dec(v___x_2158_);
lean_dec_ref(v___x_2155_);
lean_dec(v_usingArg_2153_);
lean_dec_ref(v_simprocs_2151_);
lean_dec_ref(v___x_2150_);
lean_dec(v___x_2149_);
v_a_2268_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2177_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2177_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v___x_2278_ = _args[0];
lean_object* v_tk_2279_ = _args[1];
lean_object* v___x_2280_ = _args[2];
lean_object* v___x_2281_ = _args[3];
lean_object* v___x_2282_ = _args[4];
lean_object* v_simprocs_2283_ = _args[5];
lean_object* v___x_2284_ = _args[6];
lean_object* v_usingArg_2285_ = _args[7];
lean_object* v___x_2286_ = _args[8];
lean_object* v___x_2287_ = _args[9];
lean_object* v_useReducible_2288_ = _args[10];
lean_object* v___x_2289_ = _args[11];
lean_object* v___x_2290_ = _args[12];
lean_object* v_usingTk_x3f_2291_ = _args[13];
lean_object* v_discharge_x3f_2292_ = _args[14];
lean_object* v___y_2293_ = _args[15];
lean_object* v___y_2294_ = _args[16];
lean_object* v___y_2295_ = _args[17];
lean_object* v___y_2296_ = _args[18];
lean_object* v___y_2297_ = _args[19];
lean_object* v___y_2298_ = _args[20];
lean_object* v___y_2299_ = _args[21];
lean_object* v___y_2300_ = _args[22];
lean_object* v___y_2301_ = _args[23];
_start:
{
uint8_t v___x_96478__boxed_2302_; uint8_t v___x_96479__boxed_2303_; uint8_t v_useReducible_boxed_2304_; uint8_t v___x_96481__boxed_2305_; lean_object* v_res_2306_; 
v___x_96478__boxed_2302_ = lean_unbox(v___x_2284_);
v___x_96479__boxed_2303_ = lean_unbox(v___x_2286_);
v_useReducible_boxed_2304_ = lean_unbox(v_useReducible_2288_);
v___x_96481__boxed_2305_ = lean_unbox(v___x_2289_);
v_res_2306_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2278_, v_tk_2279_, v___x_2280_, v___x_2281_, v___x_2282_, v_simprocs_2283_, v___x_96478__boxed_2302_, v_usingArg_2285_, v___x_96479__boxed_2303_, v___x_2287_, v_useReducible_boxed_2304_, v___x_96481__boxed_2305_, v___x_2290_, v_usingTk_x3f_2291_, v_discharge_x3f_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___x_2278_);
return v_res_2306_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2315_ = lean_unsigned_to_nat(38u);
v___x_2316_ = lean_unsigned_to_nat(126u);
v___x_2317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2318_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2319_ = l_mkPanicMessageWithDecl(v___x_2318_, v___x_2317_, v___x_2316_, v___x_2315_, v___x_2314_);
return v___x_2319_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Array_mkArray0(lean_box(0));
return v___x_2324_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2337_ = lean_unsigned_to_nat(15u);
v___x_2338_ = lean_unsigned_to_nat(127u);
v___x_2339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2341_ = l_mkPanicMessageWithDecl(v___x_2340_, v___x_2339_, v___x_2338_, v___x_2337_, v___x_2336_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2343_, lean_object* v___x_2344_, lean_object* v___x_2345_, lean_object* v___x_2346_, lean_object* v___x_2347_, uint8_t v___x_2348_, lean_object* v___x_2349_, lean_object* v___x_2350_, uint8_t v_useReducible_2351_, lean_object* v___f_2352_, lean_object* v___x_2353_, lean_object* v___x_2354_, lean_object* v___x_2355_, lean_object* v___x_2356_, lean_object* v___x_2357_, lean_object* v___x_2358_, lean_object* v_usingArg_2359_, lean_object* v___x_2360_, uint8_t v___x_2361_, lean_object* v_usingTk_x3f_2362_, lean_object* v_squeeze_2363_, lean_object* v_unfold_2364_, lean_object* v_args_2365_, lean_object* v_only_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___y_2378_; lean_object* v___y_2382_; lean_object* v_stx_2383_; lean_object* v___y_2384_; lean_object* v_ref_2385_; lean_object* v___y_2386_; lean_object* v___y_2405_; lean_object* v_stx_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v_options_2431_; lean_object* v_ref_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; uint8_t v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v_args_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2882_; uint8_t v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v_only_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2976_; uint8_t v___y_2977_; lean_object* v___y_2978_; uint8_t v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; uint8_t v___y_2992_; lean_object* v___y_2994_; uint8_t v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3066_; 
v_options_2431_ = lean_ctor_get(v___y_2374_, 2);
v_ref_2432_ = lean_ctor_get(v___y_2374_, 5);
v___x_2433_ = 0;
v___x_2434_ = l_Lean_SourceInfo_fromRef(v_ref_2432_, v___x_2433_);
v___x_2435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7));
lean_inc_ref(v___x_2346_);
lean_inc_ref(v___x_2345_);
lean_inc_ref(v___x_2344_);
v___x_2436_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2435_);
lean_inc(v___x_2434_);
v___x_2437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2434_);
lean_ctor_set(v___x_2437_, 1, v___x_2435_);
v___x_2438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_2439_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_2367_) == 0)
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_3066_ = v___x_3075_;
goto v___jp_3065_;
}
else
{
lean_object* v_val_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_val_3076_ = lean_ctor_get(v___y_2367_, 0);
lean_inc(v_val_3076_);
lean_dec_ref_known(v___y_2367_, 1);
v___x_3077_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___x_3078_ = lean_array_push(v___x_3077_, v_val_3076_);
v___y_3066_ = v___x_3078_;
goto v___jp_3065_;
}
v___jp_2377_:
{
lean_object* v_diag_2379_; lean_object* v___x_2380_; 
v_diag_2379_ = lean_ctor_get(v___y_2378_, 1);
lean_inc_ref(v_diag_2379_);
lean_dec_ref(v___y_2378_);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v_diag_2379_);
return v___x_2380_;
}
v___jp_2381_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1));
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v_stx_2383_);
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2388_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
lean_ctor_set(v___x_2390_, 2, v___x_2389_);
lean_ctor_set(v___x_2390_, 3, v___x_2389_);
lean_ctor_set(v___x_2390_, 4, v___x_2389_);
lean_ctor_set(v___x_2390_, 5, v___x_2389_);
v___x_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2391_, 0, v_ref_2385_);
v___x_2392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2));
v___x_2393_ = 4;
v___x_2394_ = l_Lean_MessageData_nil;
v___x_2395_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2343_, v___x_2390_, v___x_2391_, v___x_2392_, v___x_2389_, v___x_2393_, v___x_2394_, v___y_2384_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2384_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_dec_ref_known(v___x_2395_, 1);
v___y_2378_ = v___y_2382_;
goto v___jp_2377_;
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec_ref(v___y_2382_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
v___jp_2404_:
{
lean_object* v_ref_2409_; 
v_ref_2409_ = lean_ctor_get(v___y_2407_, 5);
lean_inc(v_ref_2409_);
v___y_2382_ = v___y_2405_;
v_stx_2383_ = v_stx_2406_;
v___y_2384_ = v___y_2407_;
v_ref_2385_ = v_ref_2409_;
v___y_2386_ = v___y_2408_;
goto v___jp_2381_;
}
v___jp_2410_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
v___x_2421_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2420_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___y_2405_ = v___y_2411_;
v_stx_2406_ = v_a_2422_;
v___y_2407_ = v___y_2418_;
v___y_2408_ = v___y_2419_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___y_2411_);
lean_dec(v_tk_2343_);
v_a_2423_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2421_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2421_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
v___jp_2440_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = l_Array_append___redArg(v___x_2439_, v___y_2451_);
lean_dec_ref(v___y_2451_);
lean_inc_n(v___y_2442_, 2);
v___x_2453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2453_, 0, v___y_2442_);
lean_ctor_set(v___x_2453_, 1, v___x_2438_);
lean_ctor_set(v___x_2453_, 2, v___x_2452_);
v___x_2454_ = l_Lean_Syntax_node5(v___y_2442_, v___x_2349_, v___y_2448_, v___y_2447_, v___y_2446_, v___y_2444_, v___x_2453_);
v___x_2455_ = l_Lean_Syntax_node2(v___y_2442_, v___y_2450_, v___y_2449_, v___x_2454_);
v___y_2405_ = v___y_2443_;
v_stx_2406_ = v___x_2455_;
v___y_2407_ = v___y_2445_;
v___y_2408_ = v___y_2441_;
goto v___jp_2404_;
}
v___jp_2456_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = l_Array_append___redArg(v___x_2439_, v___y_2467_);
lean_dec_ref(v___y_2467_);
lean_inc(v___y_2458_);
v___x_2469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___y_2458_);
lean_ctor_set(v___x_2469_, 1, v___x_2438_);
lean_ctor_set(v___x_2469_, 2, v___x_2468_);
if (lean_obj_tag(v___y_2461_) == 1)
{
lean_object* v_val_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v___x_2347_);
v_val_2470_ = lean_ctor_get(v___y_2461_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v___y_2461_, 1);
v___x_2471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2458_);
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___y_2458_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = l_Array_mkArray2___redArg(v___x_2472_, v_val_2470_);
v___y_2441_ = v___y_2457_;
v___y_2442_ = v___y_2458_;
v___y_2443_ = v___y_2459_;
v___y_2444_ = v___x_2469_;
v___y_2445_ = v___y_2460_;
v___y_2446_ = v___y_2462_;
v___y_2447_ = v___y_2464_;
v___y_2448_ = v___y_2463_;
v___y_2449_ = v___y_2465_;
v___y_2450_ = v___y_2466_;
v___y_2451_ = v___x_2473_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2474_; 
lean_dec(v___y_2461_);
v___x_2474_ = lean_mk_empty_array_with_capacity(v___x_2347_);
lean_dec(v___x_2347_);
v___y_2441_ = v___y_2457_;
v___y_2442_ = v___y_2458_;
v___y_2443_ = v___y_2459_;
v___y_2444_ = v___x_2469_;
v___y_2445_ = v___y_2460_;
v___y_2446_ = v___y_2462_;
v___y_2447_ = v___y_2464_;
v___y_2448_ = v___y_2463_;
v___y_2449_ = v___y_2465_;
v___y_2450_ = v___y_2466_;
v___y_2451_ = v___x_2474_;
goto v___jp_2440_;
}
}
v___jp_2475_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = l_Array_append___redArg(v___x_2439_, v___y_2486_);
lean_dec_ref(v___y_2486_);
lean_inc(v___y_2478_);
v___x_2488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2488_, 0, v___y_2478_);
lean_ctor_set(v___x_2488_, 1, v___x_2438_);
lean_ctor_set(v___x_2488_, 2, v___x_2487_);
if (lean_obj_tag(v___y_2476_) == 1)
{
lean_object* v_val_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_val_2489_ = lean_ctor_get(v___y_2476_, 0);
lean_inc(v_val_2489_);
lean_dec_ref_known(v___y_2476_, 1);
v___x_2490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2491_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2490_);
v___x_2492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2478_, 4);
v___x_2493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___y_2478_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = l_Array_append___redArg(v___x_2439_, v_val_2489_);
lean_dec(v_val_2489_);
v___x_2495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2495_, 0, v___y_2478_);
lean_ctor_set(v___x_2495_, 1, v___x_2438_);
lean_ctor_set(v___x_2495_, 2, v___x_2494_);
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___y_2478_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Lean_Syntax_node3(v___y_2478_, v___x_2491_, v___x_2493_, v___x_2495_, v___x_2497_);
v___x_2499_ = l_Array_mkArray1___redArg(v___x_2498_);
v___y_2457_ = v___y_2477_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2480_;
v___y_2461_ = v___y_2481_;
v___y_2462_ = v___x_2488_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2482_;
v___y_2465_ = v___y_2484_;
v___y_2466_ = v___y_2485_;
v___y_2467_ = v___x_2499_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2500_; 
lean_dec(v___y_2476_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2500_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2457_ = v___y_2477_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___y_2480_;
v___y_2461_ = v___y_2481_;
v___y_2462_ = v___x_2488_;
v___y_2463_ = v___y_2483_;
v___y_2464_ = v___y_2482_;
v___y_2465_ = v___y_2484_;
v___y_2466_ = v___y_2485_;
v___y_2467_ = v___x_2500_;
goto v___jp_2456_;
}
}
v___jp_2501_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = l_Array_append___redArg(v___x_2439_, v___y_2512_);
lean_dec_ref(v___y_2512_);
lean_inc(v___y_2504_);
v___x_2514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2504_);
lean_ctor_set(v___x_2514_, 1, v___x_2438_);
lean_ctor_set(v___x_2514_, 2, v___x_2513_);
if (lean_obj_tag(v___y_2509_) == 1)
{
lean_object* v_val_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_val_2515_ = lean_ctor_get(v___y_2509_, 0);
lean_inc(v_val_2515_);
lean_dec_ref_known(v___y_2509_, 1);
v___x_2516_ = l_Lean_SourceInfo_fromRef(v_val_2515_, v___x_2348_);
lean_dec(v_val_2515_);
v___x_2517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Array_mkArray1___redArg(v___x_2518_);
v___y_2476_ = v___y_2503_;
v___y_2477_ = v___y_2502_;
v___y_2478_ = v___y_2504_;
v___y_2479_ = v___y_2505_;
v___y_2480_ = v___y_2506_;
v___y_2481_ = v___y_2507_;
v___y_2482_ = v___x_2514_;
v___y_2483_ = v___y_2508_;
v___y_2484_ = v___y_2510_;
v___y_2485_ = v___y_2511_;
v___y_2486_ = v___x_2519_;
goto v___jp_2475_;
}
else
{
lean_object* v___x_2520_; 
lean_dec(v___y_2509_);
v___x_2520_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2476_ = v___y_2503_;
v___y_2477_ = v___y_2502_;
v___y_2478_ = v___y_2504_;
v___y_2479_ = v___y_2505_;
v___y_2480_ = v___y_2506_;
v___y_2481_ = v___y_2507_;
v___y_2482_ = v___x_2514_;
v___y_2483_ = v___y_2508_;
v___y_2484_ = v___y_2510_;
v___y_2485_ = v___y_2511_;
v___y_2486_ = v___x_2520_;
goto v___jp_2475_;
}
}
v___jp_2521_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2536_ = l_Array_append___redArg(v___x_2439_, v___y_2535_);
lean_dec_ref(v___y_2535_);
lean_inc_n(v___y_2533_, 3);
v___x_2537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2537_, 0, v___y_2533_);
lean_ctor_set(v___x_2537_, 1, v___x_2438_);
lean_ctor_set(v___x_2537_, 2, v___x_2536_);
v___x_2538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___y_2533_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = l_Lean_Syntax_node6(v___y_2533_, v___y_2527_, v___y_2532_, v___y_2528_, v___y_2529_, v___x_2537_, v___x_2539_, v___y_2530_);
v___x_2541_ = l_Lean_Syntax_node4(v___y_2533_, v___y_2531_, v___y_2526_, v___y_2523_, v___y_2534_, v___x_2540_);
v___y_2405_ = v___y_2524_;
v_stx_2406_ = v___x_2541_;
v___y_2407_ = v___y_2525_;
v___y_2408_ = v___y_2522_;
goto v___jp_2404_;
}
v___jp_2542_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = l_Array_append___redArg(v___x_2439_, v___y_2556_);
lean_dec_ref(v___y_2556_);
lean_inc(v___y_2554_);
v___x_2558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2554_);
lean_ctor_set(v___x_2558_, 1, v___x_2438_);
lean_ctor_set(v___x_2558_, 2, v___x_2557_);
if (lean_obj_tag(v___y_2548_) == 1)
{
lean_object* v_val_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec(v___x_2347_);
v_val_2559_ = lean_ctor_get(v___y_2548_, 0);
lean_inc(v_val_2559_);
lean_dec_ref_known(v___y_2548_, 1);
v___x_2560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2561_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2560_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2554_, 4);
v___x_2563_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2554_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Array_append___redArg(v___x_2439_, v_val_2559_);
lean_dec(v_val_2559_);
v___x_2565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2565_, 0, v___y_2554_);
lean_ctor_set(v___x_2565_, 1, v___x_2438_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
v___x_2566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___y_2554_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_Syntax_node3(v___y_2554_, v___x_2561_, v___x_2563_, v___x_2565_, v___x_2567_);
v___x_2569_ = l_Array_mkArray1___redArg(v___x_2568_);
v___y_2522_ = v___y_2543_;
v___y_2523_ = v___y_2544_;
v___y_2524_ = v___y_2545_;
v___y_2525_ = v___y_2546_;
v___y_2526_ = v___y_2547_;
v___y_2527_ = v___y_2549_;
v___y_2528_ = v___y_2550_;
v___y_2529_ = v___x_2558_;
v___y_2530_ = v___y_2551_;
v___y_2531_ = v___y_2552_;
v___y_2532_ = v___y_2553_;
v___y_2533_ = v___y_2554_;
v___y_2534_ = v___y_2555_;
v___y_2535_ = v___x_2569_;
goto v___jp_2521_;
}
else
{
lean_object* v___x_2570_; 
lean_dec(v___y_2548_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2570_ = lean_mk_empty_array_with_capacity(v___x_2347_);
lean_dec(v___x_2347_);
v___y_2522_ = v___y_2543_;
v___y_2523_ = v___y_2544_;
v___y_2524_ = v___y_2545_;
v___y_2525_ = v___y_2546_;
v___y_2526_ = v___y_2547_;
v___y_2527_ = v___y_2549_;
v___y_2528_ = v___y_2550_;
v___y_2529_ = v___x_2558_;
v___y_2530_ = v___y_2551_;
v___y_2531_ = v___y_2552_;
v___y_2532_ = v___y_2553_;
v___y_2533_ = v___y_2554_;
v___y_2534_ = v___y_2555_;
v___y_2535_ = v___x_2570_;
goto v___jp_2521_;
}
}
v___jp_2571_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = l_Array_append___redArg(v___x_2439_, v___y_2585_);
lean_dec_ref(v___y_2585_);
lean_inc(v___y_2582_);
v___x_2587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2587_, 0, v___y_2582_);
lean_ctor_set(v___x_2587_, 1, v___x_2438_);
lean_ctor_set(v___x_2587_, 2, v___x_2586_);
if (lean_obj_tag(v___y_2584_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_val_2588_ = lean_ctor_get(v___y_2584_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___y_2584_, 1);
v___x_2589_ = l_Lean_SourceInfo_fromRef(v_val_2588_, v___x_2348_);
lean_dec(v_val_2588_);
v___x_2590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = l_Array_mkArray1___redArg(v___x_2591_);
v___y_2543_ = v___y_2572_;
v___y_2544_ = v___y_2573_;
v___y_2545_ = v___y_2574_;
v___y_2546_ = v___y_2575_;
v___y_2547_ = v___y_2576_;
v___y_2548_ = v___y_2577_;
v___y_2549_ = v___y_2578_;
v___y_2550_ = v___x_2587_;
v___y_2551_ = v___y_2579_;
v___y_2552_ = v___y_2580_;
v___y_2553_ = v___y_2581_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___x_2592_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2593_; 
lean_dec(v___y_2584_);
v___x_2593_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2543_ = v___y_2572_;
v___y_2544_ = v___y_2573_;
v___y_2545_ = v___y_2574_;
v___y_2546_ = v___y_2575_;
v___y_2547_ = v___y_2576_;
v___y_2548_ = v___y_2577_;
v___y_2549_ = v___y_2578_;
v___y_2550_ = v___x_2587_;
v___y_2551_ = v___y_2579_;
v___y_2552_ = v___y_2580_;
v___y_2553_ = v___y_2581_;
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___x_2593_;
goto v___jp_2542_;
}
}
v___jp_2594_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2606_ = l_Array_append___redArg(v___x_2439_, v___y_2605_);
lean_dec_ref(v___y_2605_);
lean_inc_n(v___y_2601_, 2);
v___x_2607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2607_, 0, v___y_2601_);
lean_ctor_set(v___x_2607_, 1, v___x_2438_);
lean_ctor_set(v___x_2607_, 2, v___x_2606_);
v___x_2608_ = l_Lean_Syntax_node5(v___y_2601_, v___x_2349_, v___y_2603_, v___y_2602_, v___y_2596_, v___y_2604_, v___x_2607_);
lean_inc(v___y_2597_);
v___x_2609_ = l_Lean_Syntax_node4(v___y_2601_, v___x_2350_, v___y_2600_, v___y_2597_, v___y_2597_, v___x_2608_);
v___y_2405_ = v___y_2598_;
v_stx_2406_ = v___x_2609_;
v___y_2407_ = v___y_2599_;
v___y_2408_ = v___y_2595_;
goto v___jp_2404_;
}
v___jp_2610_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = l_Array_append___redArg(v___x_2439_, v___y_2621_);
lean_dec_ref(v___y_2621_);
lean_inc(v___y_2618_);
v___x_2623_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2623_, 0, v___y_2618_);
lean_ctor_set(v___x_2623_, 1, v___x_2438_);
lean_ctor_set(v___x_2623_, 2, v___x_2622_);
if (lean_obj_tag(v___y_2616_) == 1)
{
lean_object* v_val_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec(v___x_2347_);
v_val_2624_ = lean_ctor_get(v___y_2616_, 0);
lean_inc(v_val_2624_);
lean_dec_ref_known(v___y_2616_, 1);
v___x_2625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2618_);
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___y_2618_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = l_Array_mkArray2___redArg(v___x_2626_, v_val_2624_);
v___y_2595_ = v___y_2611_;
v___y_2596_ = v___y_2612_;
v___y_2597_ = v___y_2613_;
v___y_2598_ = v___y_2614_;
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___y_2617_;
v___y_2601_ = v___y_2618_;
v___y_2602_ = v___y_2620_;
v___y_2603_ = v___y_2619_;
v___y_2604_ = v___x_2623_;
v___y_2605_ = v___x_2627_;
goto v___jp_2594_;
}
else
{
lean_object* v___x_2628_; 
lean_dec(v___y_2616_);
v___x_2628_ = lean_mk_empty_array_with_capacity(v___x_2347_);
lean_dec(v___x_2347_);
v___y_2595_ = v___y_2611_;
v___y_2596_ = v___y_2612_;
v___y_2597_ = v___y_2613_;
v___y_2598_ = v___y_2614_;
v___y_2599_ = v___y_2615_;
v___y_2600_ = v___y_2617_;
v___y_2601_ = v___y_2618_;
v___y_2602_ = v___y_2620_;
v___y_2603_ = v___y_2619_;
v___y_2604_ = v___x_2623_;
v___y_2605_ = v___x_2628_;
goto v___jp_2594_;
}
}
v___jp_2629_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = l_Array_append___redArg(v___x_2439_, v___y_2640_);
lean_dec_ref(v___y_2640_);
lean_inc(v___y_2637_);
v___x_2642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2642_, 0, v___y_2637_);
lean_ctor_set(v___x_2642_, 1, v___x_2438_);
lean_ctor_set(v___x_2642_, 2, v___x_2641_);
if (lean_obj_tag(v___y_2630_) == 1)
{
lean_object* v_val_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_val_2643_ = lean_ctor_get(v___y_2630_, 0);
lean_inc(v_val_2643_);
lean_dec_ref_known(v___y_2630_, 1);
v___x_2644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2645_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2644_);
v___x_2646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2637_, 4);
v___x_2647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___y_2637_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Array_append___redArg(v___x_2439_, v_val_2643_);
lean_dec(v_val_2643_);
v___x_2649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2649_, 0, v___y_2637_);
lean_ctor_set(v___x_2649_, 1, v___x_2438_);
lean_ctor_set(v___x_2649_, 2, v___x_2648_);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___y_2637_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_Syntax_node3(v___y_2637_, v___x_2645_, v___x_2647_, v___x_2649_, v___x_2651_);
v___x_2653_ = l_Array_mkArray1___redArg(v___x_2652_);
v___y_2611_ = v___y_2631_;
v___y_2612_ = v___x_2642_;
v___y_2613_ = v___y_2632_;
v___y_2614_ = v___y_2633_;
v___y_2615_ = v___y_2634_;
v___y_2616_ = v___y_2636_;
v___y_2617_ = v___y_2635_;
v___y_2618_ = v___y_2637_;
v___y_2619_ = v___y_2639_;
v___y_2620_ = v___y_2638_;
v___y_2621_ = v___x_2653_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2654_; 
lean_dec(v___y_2630_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2654_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2611_ = v___y_2631_;
v___y_2612_ = v___x_2642_;
v___y_2613_ = v___y_2632_;
v___y_2614_ = v___y_2633_;
v___y_2615_ = v___y_2634_;
v___y_2616_ = v___y_2636_;
v___y_2617_ = v___y_2635_;
v___y_2618_ = v___y_2637_;
v___y_2619_ = v___y_2639_;
v___y_2620_ = v___y_2638_;
v___y_2621_ = v___x_2654_;
goto v___jp_2610_;
}
}
v___jp_2655_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = l_Array_append___redArg(v___x_2439_, v___y_2666_);
lean_dec_ref(v___y_2666_);
lean_inc(v___y_2663_);
v___x_2668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2668_, 0, v___y_2663_);
lean_ctor_set(v___x_2668_, 1, v___x_2438_);
lean_ctor_set(v___x_2668_, 2, v___x_2667_);
if (lean_obj_tag(v___y_2665_) == 1)
{
lean_object* v_val_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_val_2669_ = lean_ctor_get(v___y_2665_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v___y_2665_, 1);
v___x_2670_ = l_Lean_SourceInfo_fromRef(v_val_2669_, v___x_2348_);
lean_dec(v_val_2669_);
v___x_2671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Array_mkArray1___redArg(v___x_2672_);
v___y_2630_ = v___y_2657_;
v___y_2631_ = v___y_2656_;
v___y_2632_ = v___y_2658_;
v___y_2633_ = v___y_2659_;
v___y_2634_ = v___y_2660_;
v___y_2635_ = v___y_2662_;
v___y_2636_ = v___y_2661_;
v___y_2637_ = v___y_2663_;
v___y_2638_ = v___x_2668_;
v___y_2639_ = v___y_2664_;
v___y_2640_ = v___x_2673_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2674_; 
lean_dec(v___y_2665_);
v___x_2674_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2630_ = v___y_2657_;
v___y_2631_ = v___y_2656_;
v___y_2632_ = v___y_2658_;
v___y_2633_ = v___y_2659_;
v___y_2634_ = v___y_2660_;
v___y_2635_ = v___y_2662_;
v___y_2636_ = v___y_2661_;
v___y_2637_ = v___y_2663_;
v___y_2638_ = v___x_2668_;
v___y_2639_ = v___y_2664_;
v___y_2640_ = v___x_2674_;
goto v___jp_2629_;
}
}
v___jp_2675_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2689_ = l_Array_append___redArg(v___x_2439_, v___y_2688_);
lean_dec_ref(v___y_2688_);
lean_inc_n(v___y_2686_, 3);
v___x_2690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2690_, 0, v___y_2686_);
lean_ctor_set(v___x_2690_, 1, v___x_2438_);
lean_ctor_set(v___x_2690_, 2, v___x_2689_);
v___x_2691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___y_2686_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_Syntax_node6(v___y_2686_, v___y_2681_, v___y_2685_, v___y_2683_, v___y_2684_, v___x_2690_, v___x_2692_, v___y_2687_);
lean_inc(v___y_2679_);
v___x_2694_ = l_Lean_Syntax_node4(v___y_2686_, v___y_2680_, v___y_2682_, v___y_2679_, v___y_2679_, v___x_2693_);
v___y_2405_ = v___y_2677_;
v_stx_2406_ = v___x_2694_;
v___y_2407_ = v___y_2678_;
v___y_2408_ = v___y_2676_;
goto v___jp_2404_;
}
v___jp_2695_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = l_Array_append___redArg(v___x_2439_, v___y_2708_);
lean_dec_ref(v___y_2708_);
lean_inc(v___y_2706_);
v___x_2710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2710_, 0, v___y_2706_);
lean_ctor_set(v___x_2710_, 1, v___x_2438_);
lean_ctor_set(v___x_2710_, 2, v___x_2709_);
if (lean_obj_tag(v___y_2701_) == 1)
{
lean_object* v_val_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_dec(v___x_2347_);
v_val_2711_ = lean_ctor_get(v___y_2701_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v___y_2701_, 1);
v___x_2712_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2713_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2712_);
v___x_2714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2706_, 4);
v___x_2715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___y_2706_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = l_Array_append___redArg(v___x_2439_, v_val_2711_);
lean_dec(v_val_2711_);
v___x_2717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___y_2706_);
lean_ctor_set(v___x_2717_, 1, v___x_2438_);
lean_ctor_set(v___x_2717_, 2, v___x_2716_);
v___x_2718_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___y_2706_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = l_Lean_Syntax_node3(v___y_2706_, v___x_2713_, v___x_2715_, v___x_2717_, v___x_2719_);
v___x_2721_ = l_Array_mkArray1___redArg(v___x_2720_);
v___y_2676_ = v___y_2696_;
v___y_2677_ = v___y_2697_;
v___y_2678_ = v___y_2698_;
v___y_2679_ = v___y_2699_;
v___y_2680_ = v___y_2700_;
v___y_2681_ = v___y_2702_;
v___y_2682_ = v___y_2703_;
v___y_2683_ = v___y_2704_;
v___y_2684_ = v___x_2710_;
v___y_2685_ = v___y_2705_;
v___y_2686_ = v___y_2706_;
v___y_2687_ = v___y_2707_;
v___y_2688_ = v___x_2721_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2722_; 
lean_dec(v___y_2701_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2722_ = lean_mk_empty_array_with_capacity(v___x_2347_);
lean_dec(v___x_2347_);
v___y_2676_ = v___y_2696_;
v___y_2677_ = v___y_2697_;
v___y_2678_ = v___y_2698_;
v___y_2679_ = v___y_2699_;
v___y_2680_ = v___y_2700_;
v___y_2681_ = v___y_2702_;
v___y_2682_ = v___y_2703_;
v___y_2683_ = v___y_2704_;
v___y_2684_ = v___x_2710_;
v___y_2685_ = v___y_2705_;
v___y_2686_ = v___y_2706_;
v___y_2687_ = v___y_2707_;
v___y_2688_ = v___x_2722_;
goto v___jp_2675_;
}
}
v___jp_2723_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = l_Array_append___redArg(v___x_2439_, v___y_2736_);
lean_dec_ref(v___y_2736_);
lean_inc(v___y_2733_);
v___x_2738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2738_, 0, v___y_2733_);
lean_ctor_set(v___x_2738_, 1, v___x_2438_);
lean_ctor_set(v___x_2738_, 2, v___x_2737_);
if (lean_obj_tag(v___y_2735_) == 1)
{
lean_object* v_val_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v_val_2739_ = lean_ctor_get(v___y_2735_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v___y_2735_, 1);
v___x_2740_ = l_Lean_SourceInfo_fromRef(v_val_2739_, v___x_2348_);
lean_dec(v_val_2739_);
v___x_2741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = l_Array_mkArray1___redArg(v___x_2742_);
v___y_2696_ = v___y_2724_;
v___y_2697_ = v___y_2725_;
v___y_2698_ = v___y_2726_;
v___y_2699_ = v___y_2727_;
v___y_2700_ = v___y_2728_;
v___y_2701_ = v___y_2729_;
v___y_2702_ = v___y_2730_;
v___y_2703_ = v___y_2731_;
v___y_2704_ = v___x_2738_;
v___y_2705_ = v___y_2732_;
v___y_2706_ = v___y_2733_;
v___y_2707_ = v___y_2734_;
v___y_2708_ = v___x_2743_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2744_; 
lean_dec(v___y_2735_);
v___x_2744_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2696_ = v___y_2724_;
v___y_2697_ = v___y_2725_;
v___y_2698_ = v___y_2726_;
v___y_2699_ = v___y_2727_;
v___y_2700_ = v___y_2728_;
v___y_2701_ = v___y_2729_;
v___y_2702_ = v___y_2730_;
v___y_2703_ = v___y_2731_;
v___y_2704_ = v___x_2738_;
v___y_2705_ = v___y_2732_;
v___y_2706_ = v___y_2733_;
v___y_2707_ = v___y_2734_;
v___y_2708_ = v___x_2744_;
goto v___jp_2695_;
}
}
v___jp_2745_:
{
if (v___y_2756_ == 0)
{
if (v_useReducible_2351_ == 0)
{
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
if (lean_obj_tag(v___y_2749_) == 0)
{
lean_dec(v___y_2760_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2754_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___y_2411_ = v___y_2747_;
v___y_2412_ = v___y_2752_;
v___y_2413_ = v___y_2755_;
v___y_2414_ = v___y_2750_;
v___y_2415_ = v___y_2759_;
v___y_2416_ = v___y_2753_;
v___y_2417_ = v___y_2751_;
v___y_2418_ = v___y_2748_;
v___y_2419_ = v___y_2746_;
goto v___jp_2410_;
}
else
{
lean_object* v_val_2761_; lean_object* v___x_2762_; 
v_val_2761_ = lean_ctor_get(v___y_2749_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v___y_2749_, 1);
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2748_);
v___x_2762_ = lean_apply_9(v___f_2352_, v___y_2752_, v___y_2755_, v___y_2750_, v___y_2759_, v___y_2753_, v___y_2751_, v___y_2748_, v___y_2746_, lean_box(0));
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc_n(v_a_2763_, 3);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2346_, 2);
lean_inc_ref_n(v___x_2345_, 2);
lean_inc_ref_n(v___x_2344_, 2);
v___x_2765_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2764_);
v___x_2766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_a_2763_);
lean_ctor_set(v___x_2766_, 1, v___x_2353_);
v___x_2767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2767_, 0, v_a_2763_);
lean_ctor_set(v___x_2767_, 1, v___x_2438_);
lean_ctor_set(v___x_2767_, 2, v___x_2439_);
v___x_2768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2769_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2768_);
if (lean_obj_tag(v___y_2760_) == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2724_ = v___y_2746_;
v___y_2725_ = v___y_2747_;
v___y_2726_ = v___y_2748_;
v___y_2727_ = v___x_2767_;
v___y_2728_ = v___x_2765_;
v___y_2729_ = v___y_2754_;
v___y_2730_ = v___x_2769_;
v___y_2731_ = v___x_2766_;
v___y_2732_ = v___y_2757_;
v___y_2733_ = v_a_2763_;
v___y_2734_ = v_val_2761_;
v___y_2735_ = v___y_2758_;
v___y_2736_ = v___x_2770_;
goto v___jp_2723_;
}
else
{
lean_object* v_val_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_val_2771_ = lean_ctor_get(v___y_2760_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v___y_2760_, 1);
v___x_2772_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___x_2773_ = lean_array_push(v___x_2772_, v_val_2771_);
v___y_2724_ = v___y_2746_;
v___y_2725_ = v___y_2747_;
v___y_2726_ = v___y_2748_;
v___y_2727_ = v___x_2767_;
v___y_2728_ = v___x_2765_;
v___y_2729_ = v___y_2754_;
v___y_2730_ = v___x_2769_;
v___y_2731_ = v___x_2766_;
v___y_2732_ = v___y_2757_;
v___y_2733_ = v_a_2763_;
v___y_2734_ = v_val_2761_;
v___y_2735_ = v___y_2758_;
v___y_2736_ = v___x_2773_;
goto v___jp_2723_;
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_val_2761_);
lean_dec(v___y_2760_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___x_2353_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v_a_2774_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2762_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2762_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
else
{
lean_object* v___x_2782_; 
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2748_);
v___x_2782_ = lean_apply_9(v___f_2352_, v___y_2752_, v___y_2755_, v___y_2750_, v___y_2759_, v___y_2753_, v___y_2751_, v___y_2748_, v___y_2746_, lean_box(0));
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc_n(v_a_2783_, 3);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2784_, 0, v_a_2783_);
lean_ctor_set(v___x_2784_, 1, v___x_2353_);
v___x_2785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2785_, 0, v_a_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2438_);
lean_ctor_set(v___x_2785_, 2, v___x_2439_);
if (lean_obj_tag(v___y_2760_) == 0)
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2656_ = v___y_2746_;
v___y_2657_ = v___y_2754_;
v___y_2658_ = v___x_2785_;
v___y_2659_ = v___y_2747_;
v___y_2660_ = v___y_2748_;
v___y_2661_ = v___y_2749_;
v___y_2662_ = v___x_2784_;
v___y_2663_ = v_a_2783_;
v___y_2664_ = v___y_2757_;
v___y_2665_ = v___y_2758_;
v___y_2666_ = v___x_2786_;
goto v___jp_2655_;
}
else
{
lean_object* v_val_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_val_2787_ = lean_ctor_get(v___y_2760_, 0);
lean_inc(v_val_2787_);
lean_dec_ref_known(v___y_2760_, 1);
v___x_2788_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___x_2789_ = lean_array_push(v___x_2788_, v_val_2787_);
v___y_2656_ = v___y_2746_;
v___y_2657_ = v___y_2754_;
v___y_2658_ = v___x_2785_;
v___y_2659_ = v___y_2747_;
v___y_2660_ = v___y_2748_;
v___y_2661_ = v___y_2749_;
v___y_2662_ = v___x_2784_;
v___y_2663_ = v_a_2783_;
v___y_2664_ = v___y_2757_;
v___y_2665_ = v___y_2758_;
v___y_2666_ = v___x_2789_;
goto v___jp_2655_;
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec(v___y_2760_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2754_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___x_2353_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v_a_2790_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2782_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2782_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
else
{
lean_dec(v___x_2350_);
if (v_useReducible_2351_ == 0)
{
lean_dec(v___x_2349_);
if (lean_obj_tag(v___y_2749_) == 0)
{
lean_dec(v___y_2760_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2754_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___y_2411_ = v___y_2747_;
v___y_2412_ = v___y_2752_;
v___y_2413_ = v___y_2755_;
v___y_2414_ = v___y_2750_;
v___y_2415_ = v___y_2759_;
v___y_2416_ = v___y_2753_;
v___y_2417_ = v___y_2751_;
v___y_2418_ = v___y_2748_;
v___y_2419_ = v___y_2746_;
goto v___jp_2410_;
}
else
{
lean_object* v_val_2798_; lean_object* v___x_2799_; 
v_val_2798_ = lean_ctor_get(v___y_2749_, 0);
lean_inc(v_val_2798_);
lean_dec_ref_known(v___y_2749_, 1);
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2748_);
v___x_2799_ = lean_apply_9(v___f_2352_, v___y_2752_, v___y_2755_, v___y_2750_, v___y_2759_, v___y_2753_, v___y_2751_, v___y_2748_, v___y_2746_, lean_box(0));
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc_n(v_a_2800_, 5);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2346_, 2);
lean_inc_ref_n(v___x_2345_, 2);
lean_inc_ref_n(v___x_2344_, 2);
v___x_2802_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2803_, 0, v_a_2800_);
lean_ctor_set(v___x_2803_, 1, v___x_2353_);
v___x_2804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2804_, 0, v_a_2800_);
lean_ctor_set(v___x_2804_, 1, v___x_2438_);
lean_ctor_set(v___x_2804_, 2, v___x_2439_);
v___x_2805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_2806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_a_2800_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = l_Lean_Syntax_node1(v_a_2800_, v___x_2438_, v___x_2806_);
v___x_2808_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2809_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2808_);
if (lean_obj_tag(v___y_2760_) == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2572_ = v___y_2746_;
v___y_2573_ = v___x_2804_;
v___y_2574_ = v___y_2747_;
v___y_2575_ = v___y_2748_;
v___y_2576_ = v___x_2803_;
v___y_2577_ = v___y_2754_;
v___y_2578_ = v___x_2809_;
v___y_2579_ = v_val_2798_;
v___y_2580_ = v___x_2802_;
v___y_2581_ = v___y_2757_;
v___y_2582_ = v_a_2800_;
v___y_2583_ = v___x_2807_;
v___y_2584_ = v___y_2758_;
v___y_2585_ = v___x_2810_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_val_2811_ = lean_ctor_get(v___y_2760_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v___y_2760_, 1);
v___x_2812_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___x_2813_ = lean_array_push(v___x_2812_, v_val_2811_);
v___y_2572_ = v___y_2746_;
v___y_2573_ = v___x_2804_;
v___y_2574_ = v___y_2747_;
v___y_2575_ = v___y_2748_;
v___y_2576_ = v___x_2803_;
v___y_2577_ = v___y_2754_;
v___y_2578_ = v___x_2809_;
v___y_2579_ = v_val_2798_;
v___y_2580_ = v___x_2802_;
v___y_2581_ = v___y_2757_;
v___y_2582_ = v_a_2800_;
v___y_2583_ = v___x_2807_;
v___y_2584_ = v___y_2758_;
v___y_2585_ = v___x_2813_;
goto v___jp_2571_;
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_val_2798_);
lean_dec(v___y_2760_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___x_2353_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v_a_2814_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2799_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2799_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
else
{
lean_object* v___x_2822_; 
lean_dec_ref(v___x_2353_);
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2748_);
v___x_2822_ = lean_apply_9(v___f_2352_, v___y_2752_, v___y_2755_, v___y_2750_, v___y_2759_, v___y_2753_, v___y_2751_, v___y_2748_, v___y_2746_, lean_box(0));
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc_n(v_a_2823_, 2);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20));
lean_inc_ref(v___x_2346_);
lean_inc_ref(v___x_2345_);
lean_inc_ref(v___x_2344_);
v___x_2825_ = l_Lean_Name_mkStr4(v___x_2344_, v___x_2345_, v___x_2346_, v___x_2824_);
v___x_2826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21));
v___x_2827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_a_2823_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
if (lean_obj_tag(v___y_2760_) == 0)
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_2502_ = v___y_2746_;
v___y_2503_ = v___y_2754_;
v___y_2504_ = v_a_2823_;
v___y_2505_ = v___y_2747_;
v___y_2506_ = v___y_2748_;
v___y_2507_ = v___y_2749_;
v___y_2508_ = v___y_2757_;
v___y_2509_ = v___y_2758_;
v___y_2510_ = v___x_2827_;
v___y_2511_ = v___x_2825_;
v___y_2512_ = v___x_2828_;
goto v___jp_2501_;
}
else
{
lean_object* v_val_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_val_2829_ = lean_ctor_get(v___y_2760_, 0);
lean_inc(v_val_2829_);
lean_dec_ref_known(v___y_2760_, 1);
v___x_2830_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___x_2831_ = lean_array_push(v___x_2830_, v_val_2829_);
v___y_2502_ = v___y_2746_;
v___y_2503_ = v___y_2754_;
v___y_2504_ = v_a_2823_;
v___y_2505_ = v___y_2747_;
v___y_2506_ = v___y_2748_;
v___y_2507_ = v___y_2749_;
v___y_2508_ = v___y_2757_;
v___y_2509_ = v___y_2758_;
v___y_2510_ = v___x_2827_;
v___y_2511_ = v___x_2825_;
v___y_2512_ = v___x_2831_;
goto v___jp_2501_;
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v___y_2760_);
lean_dec(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec(v___y_2754_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v_a_2832_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2822_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2822_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
}
v___jp_2840_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = lean_unsigned_to_nat(5u);
v___x_2858_ = l_Lean_Syntax_getArg(v___y_2844_, v___x_2857_);
lean_dec(v___y_2844_);
v___x_2859_ = l_Lean_Syntax_matchesNull(v___x_2858_, v___x_2347_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec(v_args_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2843_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2860_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2861_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2860_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___y_2405_ = v___y_2842_;
v_stx_2406_ = v_a_2862_;
v___y_2407_ = v___y_2855_;
v___y_2408_ = v___y_2856_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec_ref(v___y_2842_);
lean_dec(v_tk_2343_);
v_a_2863_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2861_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_Syntax_getOptional_x3f(v___y_2847_);
lean_dec(v___y_2847_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_box(0);
v___y_2746_ = v___y_2856_;
v___y_2747_ = v___y_2842_;
v___y_2748_ = v___y_2855_;
v___y_2749_ = v___y_2843_;
v___y_2750_ = v___y_2851_;
v___y_2751_ = v___y_2854_;
v___y_2752_ = v___y_2849_;
v___y_2753_ = v___y_2853_;
v___y_2754_ = v_args_2848_;
v___y_2755_ = v___y_2850_;
v___y_2756_ = v___y_2841_;
v___y_2757_ = v___y_2845_;
v___y_2758_ = v___y_2846_;
v___y_2759_ = v___y_2852_;
v___y_2760_ = v___x_2872_;
goto v___jp_2745_;
}
else
{
lean_object* v_val_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
v_val_2873_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2871_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_val_2873_);
lean_dec(v___x_2871_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_val_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
v___y_2746_ = v___y_2856_;
v___y_2747_ = v___y_2842_;
v___y_2748_ = v___y_2855_;
v___y_2749_ = v___y_2843_;
v___y_2750_ = v___y_2851_;
v___y_2751_ = v___y_2854_;
v___y_2752_ = v___y_2849_;
v___y_2753_ = v___y_2853_;
v___y_2754_ = v_args_2848_;
v___y_2755_ = v___y_2850_;
v___y_2756_ = v___y_2841_;
v___y_2757_ = v___y_2845_;
v___y_2758_ = v___y_2846_;
v___y_2759_ = v___y_2852_;
v___y_2760_ = v___x_2878_;
goto v___jp_2745_;
}
}
}
}
}
v___jp_2881_:
{
lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = l_Lean_Syntax_getArg(v___y_2885_, v___x_2354_);
v___x_2898_ = l_Lean_Syntax_isNone(v___x_2897_);
if (v___x_2898_ == 0)
{
uint8_t v___x_2899_; 
lean_inc(v___x_2897_);
v___x_2899_ = l_Lean_Syntax_matchesNull(v___x_2897_, v___x_2355_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec(v___x_2897_);
lean_dec(v_only_2888_);
lean_dec(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2900_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2901_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2900_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___y_2405_ = v___y_2882_;
v_stx_2406_ = v_a_2902_;
v___y_2407_ = v___y_2895_;
v___y_2408_ = v___y_2896_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec_ref(v___y_2882_);
lean_dec(v_tk_2343_);
v_a_2903_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2901_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2901_);
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
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = l_Lean_Syntax_getArg(v___x_2897_, v___x_2356_);
lean_dec(v___x_2356_);
lean_dec(v___x_2897_);
v___x_2912_ = l_Lean_Syntax_getArgs(v___x_2911_);
lean_dec(v___x_2911_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
v___y_2841_ = v___y_2883_;
v___y_2842_ = v___y_2882_;
v___y_2843_ = v___y_2884_;
v___y_2844_ = v___y_2885_;
v___y_2845_ = v___y_2886_;
v___y_2846_ = v_only_2888_;
v___y_2847_ = v___y_2887_;
v_args_2848_ = v___x_2913_;
v___y_2849_ = v___y_2889_;
v___y_2850_ = v___y_2890_;
v___y_2851_ = v___y_2891_;
v___y_2852_ = v___y_2892_;
v___y_2853_ = v___y_2893_;
v___y_2854_ = v___y_2894_;
v___y_2855_ = v___y_2895_;
v___y_2856_ = v___y_2896_;
goto v___jp_2840_;
}
}
else
{
lean_object* v___x_2914_; 
lean_dec(v___x_2897_);
lean_dec(v___x_2356_);
v___x_2914_ = lean_box(0);
v___y_2841_ = v___y_2883_;
v___y_2842_ = v___y_2882_;
v___y_2843_ = v___y_2884_;
v___y_2844_ = v___y_2885_;
v___y_2845_ = v___y_2886_;
v___y_2846_ = v_only_2888_;
v___y_2847_ = v___y_2887_;
v_args_2848_ = v___x_2914_;
v___y_2849_ = v___y_2889_;
v___y_2850_ = v___y_2890_;
v___y_2851_ = v___y_2891_;
v___y_2852_ = v___y_2892_;
v___y_2853_ = v___y_2893_;
v___y_2854_ = v___y_2894_;
v___y_2855_ = v___y_2895_;
v___y_2856_ = v___y_2896_;
goto v___jp_2840_;
}
}
v___jp_2915_:
{
lean_object* v_usedTheorems_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_usedTheorems_2920_ = lean_ctor_get(v___y_2917_, 0);
v___x_2921_ = l_Lean_Syntax_unsetTrailing(v___y_2918_);
v___x_2922_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2921_, v_usedTheorems_2920_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; uint8_t v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc_n(v_a_2923_, 2);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_Syntax_isOfKind(v_a_2923_, v___x_2436_);
lean_dec(v___x_2436_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_inc(v_ref_2432_);
lean_dec(v_a_2923_);
lean_dec(v___y_2919_);
lean_dec(v___x_2358_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2926_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2925_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___y_2382_ = v___y_2917_;
v_stx_2383_ = v_a_2927_;
v___y_2384_ = v___y_2374_;
v_ref_2385_ = v_ref_2432_;
v___y_2386_ = v___y_2375_;
goto v___jp_2381_;
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec_ref(v___y_2917_);
lean_dec(v_ref_2432_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v_tk_2343_);
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
lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = l_Lean_Syntax_getArg(v_a_2923_, v___x_2356_);
lean_inc(v___x_2936_);
v___x_2937_ = l_Lean_Syntax_isOfKind(v___x_2936_, v___x_2357_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_inc(v_ref_2432_);
lean_dec(v___x_2936_);
lean_dec(v_a_2923_);
lean_dec(v___y_2919_);
lean_dec(v___x_2358_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2938_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2939_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2938_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___y_2382_ = v___y_2917_;
v_stx_2383_ = v_a_2940_;
v___y_2384_ = v___y_2374_;
v_ref_2385_ = v_ref_2432_;
v___y_2386_ = v___y_2375_;
goto v___jp_2381_;
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v___y_2917_);
lean_dec(v_ref_2432_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v_tk_2343_);
v_a_2941_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2939_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2939_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2949_ = l_Lean_Syntax_getArg(v_a_2923_, v___x_2358_);
lean_dec(v___x_2358_);
v___x_2950_ = l_Lean_Syntax_getArg(v_a_2923_, v___x_2355_);
v___x_2951_ = l_Lean_Syntax_isNone(v___x_2950_);
if (v___x_2951_ == 0)
{
uint8_t v___x_2952_; 
lean_inc(v___x_2950_);
v___x_2952_ = l_Lean_Syntax_matchesNull(v___x_2950_, v___x_2356_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_inc(v_ref_2432_);
lean_dec(v___x_2950_);
lean_dec(v___x_2949_);
lean_dec(v___x_2936_);
lean_dec(v_a_2923_);
lean_dec(v___y_2919_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
v___x_2953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2954_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2953_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v___y_2382_ = v___y_2917_;
v_stx_2383_ = v_a_2955_;
v___y_2384_ = v___y_2374_;
v_ref_2385_ = v_ref_2432_;
v___y_2386_ = v___y_2375_;
goto v___jp_2381_;
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref(v___y_2917_);
lean_dec(v_ref_2432_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v_tk_2343_);
v_a_2956_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2954_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = l_Lean_Syntax_getArg(v___x_2950_, v___x_2347_);
lean_dec(v___x_2950_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
v___y_2882_ = v___y_2917_;
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___y_2919_;
v___y_2885_ = v_a_2923_;
v___y_2886_ = v___x_2936_;
v___y_2887_ = v___x_2949_;
v_only_2888_ = v___x_2965_;
v___y_2889_ = v___y_2368_;
v___y_2890_ = v___y_2369_;
v___y_2891_ = v___y_2370_;
v___y_2892_ = v___y_2371_;
v___y_2893_ = v___y_2372_;
v___y_2894_ = v___y_2373_;
v___y_2895_ = v___y_2374_;
v___y_2896_ = v___y_2375_;
goto v___jp_2881_;
}
}
else
{
lean_object* v___x_2966_; 
lean_dec(v___x_2950_);
v___x_2966_ = lean_box(0);
v___y_2882_ = v___y_2917_;
v___y_2883_ = v___y_2916_;
v___y_2884_ = v___y_2919_;
v___y_2885_ = v_a_2923_;
v___y_2886_ = v___x_2936_;
v___y_2887_ = v___x_2949_;
v_only_2888_ = v___x_2966_;
v___y_2889_ = v___y_2368_;
v___y_2890_ = v___y_2369_;
v___y_2891_ = v___y_2370_;
v___y_2892_ = v___y_2371_;
v___y_2893_ = v___y_2372_;
v___y_2894_ = v___y_2373_;
v___y_2895_ = v___y_2374_;
v___y_2896_ = v___y_2375_;
goto v___jp_2881_;
}
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2917_);
lean_dec(v___x_2436_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___x_2358_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v_a_2967_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2922_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2922_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
v___jp_2975_:
{
if (lean_obj_tag(v_usingArg_2359_) == 0)
{
v___y_2916_ = v___y_2977_;
v___y_2917_ = v___y_2976_;
v___y_2918_ = v___y_2978_;
v___y_2919_ = v_usingArg_2359_;
goto v___jp_2915_;
}
else
{
lean_object* v_val_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2987_; 
v_val_2979_ = lean_ctor_get(v_usingArg_2359_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_usingArg_2359_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2981_ = v_usingArg_2359_;
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_val_2979_);
lean_dec(v_usingArg_2359_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = l_Lean_Syntax_unsetTrailing(v_val_2979_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
v___y_2916_ = v___y_2977_;
v___y_2917_ = v___y_2976_;
v___y_2918_ = v___y_2978_;
v___y_2919_ = v___x_2985_;
goto v___jp_2915_;
}
}
}
}
v___jp_2988_:
{
if (v___y_2992_ == 0)
{
lean_dec(v___y_2991_);
lean_dec(v___x_2436_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v_usingArg_2359_);
lean_dec(v___x_2358_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v___y_2378_ = v___y_2990_;
goto v___jp_2377_;
}
else
{
v___y_2976_ = v___y_2990_;
v___y_2977_ = v___y_2989_;
v___y_2978_ = v___y_2991_;
goto v___jp_2975_;
}
}
v___jp_2993_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; 
v___x_2999_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_2998_, v___x_2433_);
v___x_3000_ = lean_box(v___x_2348_);
v___x_3001_ = lean_box(v___x_2433_);
v___x_3002_ = lean_box(v_useReducible_2351_);
v___x_3003_ = lean_box(v___x_2361_);
lean_inc(v___x_2356_);
lean_inc_ref(v___x_2353_);
lean_inc(v_usingArg_2359_);
lean_inc(v___x_2347_);
lean_inc(v_tk_2343_);
lean_inc(v___x_2358_);
v___f_3004_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 24, 14);
lean_closure_set(v___f_3004_, 0, v___x_2358_);
lean_closure_set(v___f_3004_, 1, v_tk_2343_);
lean_closure_set(v___f_3004_, 2, v___x_2438_);
lean_closure_set(v___f_3004_, 3, v___x_2347_);
lean_closure_set(v___f_3004_, 4, v___x_2999_);
lean_closure_set(v___f_3004_, 5, v___y_2994_);
lean_closure_set(v___f_3004_, 6, v___x_3000_);
lean_closure_set(v___f_3004_, 7, v_usingArg_2359_);
lean_closure_set(v___f_3004_, 8, v___x_3001_);
lean_closure_set(v___f_3004_, 9, v___x_2353_);
lean_closure_set(v___f_3004_, 10, v___x_3002_);
lean_closure_set(v___f_3004_, 11, v___x_3003_);
lean_closure_set(v___f_3004_, 12, v___x_2356_);
lean_closure_set(v___f_3004_, 13, v_usingTk_x3f_2362_);
v___x_3005_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_2997_, v___f_3004_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2997_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3008_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_2431_, v___x_3007_);
if (v___x_3008_ == 0)
{
if (lean_obj_tag(v_squeeze_2363_) == 0)
{
v___y_2989_ = v___y_2995_;
v___y_2990_ = v_a_3006_;
v___y_2991_ = v___y_2996_;
v___y_2992_ = v___x_3008_;
goto v___jp_2988_;
}
else
{
v___y_2989_ = v___y_2995_;
v___y_2990_ = v_a_3006_;
v___y_2991_ = v___y_2996_;
v___y_2992_ = v___x_2361_;
goto v___jp_2988_;
}
}
else
{
v___y_2976_ = v_a_3006_;
v___y_2977_ = v___y_2995_;
v___y_2978_ = v___y_2996_;
goto v___jp_2975_;
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v___y_2996_);
lean_dec(v___x_2436_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v_usingArg_2359_);
lean_dec(v___x_2358_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v_a_3009_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3005_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3005_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
v___jp_3017_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3021_ = l_Array_append___redArg(v___x_2439_, v___y_3020_);
lean_dec_ref(v___y_3020_);
lean_inc_n(v___x_2434_, 2);
v___x_3022_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3022_, 0, v___x_2434_);
lean_ctor_set(v___x_3022_, 1, v___x_2438_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3023_, 0, v___x_2434_);
lean_ctor_set(v___x_3023_, 1, v___x_2438_);
lean_ctor_set(v___x_3023_, 2, v___x_2439_);
lean_inc(v___x_2436_);
v___x_3024_ = l_Lean_Syntax_node6(v___x_2434_, v___x_2436_, v___x_2437_, v___x_2360_, v___y_3019_, v___y_3018_, v___x_3022_, v___x_3023_);
v___x_3025_ = 0;
v___x_3026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23));
v___x_3027_ = lean_box(v___x_2433_);
v___x_3028_ = lean_box(v___x_3025_);
v___x_3029_ = lean_box(v___x_2433_);
lean_inc(v___x_3024_);
v___x_3030_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3030_, 0, v___x_3024_);
lean_closure_set(v___x_3030_, 1, v___x_3027_);
lean_closure_set(v___x_3030_, 2, v___x_3028_);
lean_closure_set(v___x_3030_, 3, v___x_3029_);
lean_closure_set(v___x_3030_, 4, v___x_3026_);
v___x_3031_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3030_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
if (lean_obj_tag(v_unfold_2364_) == 0)
{
lean_object* v_ctx_3033_; lean_object* v_simprocs_3034_; lean_object* v_dischargeWrapper_3035_; 
v_ctx_3033_ = lean_ctor_get(v_a_3032_, 0);
lean_inc_ref(v_ctx_3033_);
v_simprocs_3034_ = lean_ctor_get(v_a_3032_, 1);
lean_inc_ref(v_simprocs_3034_);
v_dischargeWrapper_3035_ = lean_ctor_get(v_a_3032_, 2);
lean_inc(v_dischargeWrapper_3035_);
lean_dec(v_a_3032_);
v___y_2994_ = v_simprocs_3034_;
v___y_2995_ = v___x_2433_;
v___y_2996_ = v___x_3024_;
v___y_2997_ = v_dischargeWrapper_3035_;
v___y_2998_ = v_ctx_3033_;
goto v___jp_2993_;
}
else
{
if (v___x_2361_ == 0)
{
lean_object* v_ctx_3036_; lean_object* v_simprocs_3037_; lean_object* v_dischargeWrapper_3038_; 
v_ctx_3036_ = lean_ctor_get(v_a_3032_, 0);
lean_inc_ref(v_ctx_3036_);
v_simprocs_3037_ = lean_ctor_get(v_a_3032_, 1);
lean_inc_ref(v_simprocs_3037_);
v_dischargeWrapper_3038_ = lean_ctor_get(v_a_3032_, 2);
lean_inc(v_dischargeWrapper_3038_);
lean_dec(v_a_3032_);
v___y_2994_ = v_simprocs_3037_;
v___y_2995_ = v___x_2361_;
v___y_2996_ = v___x_3024_;
v___y_2997_ = v_dischargeWrapper_3038_;
v___y_2998_ = v_ctx_3036_;
goto v___jp_2993_;
}
else
{
lean_object* v_ctx_3039_; lean_object* v_simprocs_3040_; lean_object* v_dischargeWrapper_3041_; lean_object* v___x_3042_; 
v_ctx_3039_ = lean_ctor_get(v_a_3032_, 0);
lean_inc_ref(v_ctx_3039_);
v_simprocs_3040_ = lean_ctor_get(v_a_3032_, 1);
lean_inc_ref(v_simprocs_3040_);
v_dischargeWrapper_3041_ = lean_ctor_get(v_a_3032_, 2);
lean_inc(v_dischargeWrapper_3041_);
lean_dec(v_a_3032_);
v___x_3042_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3039_);
v___y_2994_ = v_simprocs_3040_;
v___y_2995_ = v___x_2361_;
v___y_2996_ = v___x_3024_;
v___y_2997_ = v_dischargeWrapper_3041_;
v___y_2998_ = v___x_3042_;
goto v___jp_2993_;
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v___x_3024_);
lean_dec(v___x_2436_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v_usingTk_x3f_2362_);
lean_dec(v_usingArg_2359_);
lean_dec(v___x_2358_);
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2353_);
lean_dec_ref(v___f_2352_);
lean_dec(v___x_2350_);
lean_dec(v___x_2349_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___x_2344_);
lean_dec(v_tk_2343_);
v_a_3043_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3031_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3031_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
v___jp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = l_Array_append___redArg(v___x_2439_, v___y_3053_);
lean_dec_ref(v___y_3053_);
lean_inc(v___x_2434_);
v___x_3055_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3055_, 0, v___x_2434_);
lean_ctor_set(v___x_3055_, 1, v___x_2438_);
lean_ctor_set(v___x_3055_, 2, v___x_3054_);
if (lean_obj_tag(v_args_2365_) == 1)
{
lean_object* v_val_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_val_3056_ = lean_ctor_get(v_args_2365_, 0);
v___x_3057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___x_2434_, 3);
v___x_3058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_2434_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = l_Array_append___redArg(v___x_2439_, v_val_3056_);
v___x_3060_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3060_, 0, v___x_2434_);
lean_ctor_set(v___x_3060_, 1, v___x_2438_);
lean_ctor_set(v___x_3060_, 2, v___x_3059_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_2434_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = l_Array_mkArray3___redArg(v___x_3058_, v___x_3060_, v___x_3062_);
v___y_3018_ = v___x_3055_;
v___y_3019_ = v___y_3052_;
v___y_3020_ = v___x_3063_;
goto v___jp_3017_;
}
else
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_3018_ = v___x_3055_;
v___y_3019_ = v___y_3052_;
v___y_3020_ = v___x_3064_;
goto v___jp_3017_;
}
}
v___jp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = l_Array_append___redArg(v___x_2439_, v___y_3066_);
lean_dec_ref(v___y_3066_);
lean_inc(v___x_2434_);
v___x_3068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3068_, 0, v___x_2434_);
lean_ctor_set(v___x_3068_, 1, v___x_2438_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
if (lean_obj_tag(v_only_2366_) == 1)
{
lean_object* v_val_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_val_3069_ = lean_ctor_get(v_only_2366_, 0);
v___x_3070_ = l_Lean_SourceInfo_fromRef(v_val_3069_, v___x_2348_);
v___x_3071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = l_Array_mkArray1___redArg(v___x_3072_);
v___y_3052_ = v___x_3068_;
v___y_3053_ = v___x_3073_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___y_3052_ = v___x_3068_;
v___y_3053_ = v___x_3074_;
goto v___jp_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v_tk_3079_ = _args[0];
lean_object* v___x_3080_ = _args[1];
lean_object* v___x_3081_ = _args[2];
lean_object* v___x_3082_ = _args[3];
lean_object* v___x_3083_ = _args[4];
lean_object* v___x_3084_ = _args[5];
lean_object* v___x_3085_ = _args[6];
lean_object* v___x_3086_ = _args[7];
lean_object* v_useReducible_3087_ = _args[8];
lean_object* v___f_3088_ = _args[9];
lean_object* v___x_3089_ = _args[10];
lean_object* v___x_3090_ = _args[11];
lean_object* v___x_3091_ = _args[12];
lean_object* v___x_3092_ = _args[13];
lean_object* v___x_3093_ = _args[14];
lean_object* v___x_3094_ = _args[15];
lean_object* v_usingArg_3095_ = _args[16];
lean_object* v___x_3096_ = _args[17];
lean_object* v___x_3097_ = _args[18];
lean_object* v_usingTk_x3f_3098_ = _args[19];
lean_object* v_squeeze_3099_ = _args[20];
lean_object* v_unfold_3100_ = _args[21];
lean_object* v_args_3101_ = _args[22];
lean_object* v_only_3102_ = _args[23];
lean_object* v___y_3103_ = _args[24];
lean_object* v___y_3104_ = _args[25];
lean_object* v___y_3105_ = _args[26];
lean_object* v___y_3106_ = _args[27];
lean_object* v___y_3107_ = _args[28];
lean_object* v___y_3108_ = _args[29];
lean_object* v___y_3109_ = _args[30];
lean_object* v___y_3110_ = _args[31];
lean_object* v___y_3111_ = _args[32];
lean_object* v___y_3112_ = _args[33];
_start:
{
uint8_t v___x_96894__boxed_3113_; uint8_t v_useReducible_boxed_3114_; uint8_t v___x_96905__boxed_3115_; lean_object* v_res_3116_; 
v___x_96894__boxed_3113_ = lean_unbox(v___x_3084_);
v_useReducible_boxed_3114_ = lean_unbox(v_useReducible_3087_);
v___x_96905__boxed_3115_ = lean_unbox(v___x_3097_);
v_res_3116_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3079_, v___x_3080_, v___x_3081_, v___x_3082_, v___x_3083_, v___x_96894__boxed_3113_, v___x_3085_, v___x_3086_, v_useReducible_boxed_3114_, v___f_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v___x_3094_, v_usingArg_3095_, v___x_3096_, v___x_96905__boxed_3115_, v_usingTk_x3f_3098_, v_squeeze_3099_, v_unfold_3100_, v_args_3101_, v_only_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v_only_3102_);
lean_dec(v_args_3101_);
lean_dec(v_unfold_3100_);
lean_dec(v_squeeze_3099_);
lean_dec(v___x_3093_);
lean_dec(v___x_3091_);
lean_dec(v___x_3090_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3143_, lean_object* v_stx_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3156_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_3157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
lean_inc(v_stx_3144_);
v___x_3159_ = l_Lean_Syntax_isOfKind(v_stx_3144_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; 
lean_dec(v_stx_3144_);
v___x_3160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3160_;
}
else
{
lean_object* v___f_3161_; lean_object* v___x_3162_; lean_object* v_tk_3163_; lean_object* v___x_3164_; uint8_t v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v_usingTk_x3f_3215_; lean_object* v_usingArg_3216_; uint8_t v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v_args_3248_; uint8_t v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v_only_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_unfold_3304_; lean_object* v_squeeze_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___f_3161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3162_ = lean_unsigned_to_nat(0u);
v_tk_3163_ = l_Lean_Syntax_getArg(v_stx_3144_, v___x_3162_);
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3340_ = l_Lean_Syntax_getArg(v_stx_3144_, v___x_3164_);
v___x_3341_ = l_Lean_Syntax_isNone(v___x_3340_);
if (v___x_3341_ == 0)
{
uint8_t v___x_3342_; 
lean_inc(v___x_3340_);
v___x_3342_ = l_Lean_Syntax_matchesNull(v___x_3340_, v___x_3164_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; 
lean_dec(v___x_3340_);
lean_dec(v_tk_3163_);
lean_dec(v_stx_3144_);
v___x_3343_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3343_;
}
else
{
lean_object* v_squeeze_3344_; lean_object* v___x_3345_; 
v_squeeze_3344_ = l_Lean_Syntax_getArg(v___x_3340_, v___x_3162_);
lean_dec(v___x_3340_);
v___x_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3345_, 0, v_squeeze_3344_);
v_squeeze_3323_ = v___x_3345_;
v___y_3324_ = v_a_3145_;
v___y_3325_ = v_a_3146_;
v___y_3326_ = v_a_3147_;
v___y_3327_ = v_a_3148_;
v___y_3328_ = v_a_3149_;
v___y_3329_ = v_a_3150_;
v___y_3330_ = v_a_3151_;
v___y_3331_ = v_a_3152_;
goto v___jp_3322_;
}
}
else
{
lean_object* v___x_3346_; 
lean_dec(v___x_3340_);
v___x_3346_ = lean_box(0);
v_squeeze_3323_ = v___x_3346_;
v___y_3324_ = v_a_3145_;
v___y_3325_ = v_a_3146_;
v___y_3326_ = v_a_3147_;
v___y_3327_ = v_a_3148_;
v___y_3328_ = v_a_3149_;
v___y_3329_ = v_a_3150_;
v___y_3330_ = v_a_3151_;
v___y_3331_ = v_a_3152_;
goto v___jp_3322_;
}
v___jp_3165_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3188_ = lean_box(v___x_3159_);
v___x_3189_ = lean_box(v_useReducible_3143_);
v___x_3190_ = lean_box(v___y_3166_);
lean_inc(v___y_3170_);
lean_inc(v___y_3167_);
v___f_3191_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3191_, 0, v_tk_3163_);
lean_closure_set(v___f_3191_, 1, v___x_3154_);
lean_closure_set(v___f_3191_, 2, v___x_3155_);
lean_closure_set(v___f_3191_, 3, v___x_3156_);
lean_closure_set(v___f_3191_, 4, v___x_3162_);
lean_closure_set(v___f_3191_, 5, v___x_3188_);
lean_closure_set(v___f_3191_, 6, v___y_3167_);
lean_closure_set(v___f_3191_, 7, v___x_3158_);
lean_closure_set(v___f_3191_, 8, v___x_3189_);
lean_closure_set(v___f_3191_, 9, v___f_3161_);
lean_closure_set(v___f_3191_, 10, v___x_3157_);
lean_closure_set(v___f_3191_, 11, v___y_3181_);
lean_closure_set(v___f_3191_, 12, v___y_3182_);
lean_closure_set(v___f_3191_, 13, v___x_3164_);
lean_closure_set(v___f_3191_, 14, v___y_3170_);
lean_closure_set(v___f_3191_, 15, v___y_3172_);
lean_closure_set(v___f_3191_, 16, v___y_3179_);
lean_closure_set(v___f_3191_, 17, v___y_3183_);
lean_closure_set(v___f_3191_, 18, v___x_3190_);
lean_closure_set(v___f_3191_, 19, v___y_3171_);
lean_closure_set(v___f_3191_, 20, v___y_3180_);
lean_closure_set(v___f_3191_, 21, v___y_3184_);
lean_closure_set(v___f_3191_, 22, v___y_3174_);
lean_closure_set(v___f_3191_, 23, v___y_3173_);
lean_closure_set(v___f_3191_, 24, v___y_3187_);
v___x_3192_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3192_, 0, v___f_3191_);
v___x_3193_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3192_, v___y_3177_, v___y_3168_, v___y_3185_, v___y_3176_, v___y_3178_, v___y_3186_, v___y_3175_, v___y_3169_);
return v___x_3193_;
}
v___jp_3194_:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Syntax_getOptional_x3f(v___y_3200_);
lean_dec(v___y_3200_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_box(0);
v___y_3166_ = v___y_3195_;
v___y_3167_ = v___y_3196_;
v___y_3168_ = v___y_3197_;
v___y_3169_ = v___y_3198_;
v___y_3170_ = v___y_3199_;
v___y_3171_ = v_usingTk_x3f_3215_;
v___y_3172_ = v___y_3201_;
v___y_3173_ = v___y_3202_;
v___y_3174_ = v___y_3203_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v___y_3205_;
v___y_3177_ = v___y_3206_;
v___y_3178_ = v___y_3207_;
v___y_3179_ = v_usingArg_3216_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v___y_3210_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3212_;
v___y_3185_ = v___y_3213_;
v___y_3186_ = v___y_3214_;
v___y_3187_ = v___x_3218_;
goto v___jp_3165_;
}
else
{
lean_object* v_val_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
v_val_3219_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3217_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_val_3219_);
lean_dec(v___x_3217_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_val_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
v___y_3166_ = v___y_3195_;
v___y_3167_ = v___y_3196_;
v___y_3168_ = v___y_3197_;
v___y_3169_ = v___y_3198_;
v___y_3170_ = v___y_3199_;
v___y_3171_ = v_usingTk_x3f_3215_;
v___y_3172_ = v___y_3201_;
v___y_3173_ = v___y_3202_;
v___y_3174_ = v___y_3203_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v___y_3205_;
v___y_3177_ = v___y_3206_;
v___y_3178_ = v___y_3207_;
v___y_3179_ = v_usingArg_3216_;
v___y_3180_ = v___y_3208_;
v___y_3181_ = v___y_3211_;
v___y_3182_ = v___y_3210_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3212_;
v___y_3185_ = v___y_3213_;
v___y_3186_ = v___y_3214_;
v___y_3187_ = v___x_3224_;
goto v___jp_3165_;
}
}
}
}
v___jp_3227_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3249_ = lean_unsigned_to_nat(4u);
v___x_3250_ = l_Lean_Syntax_getArg(v___y_3247_, v___x_3249_);
lean_dec(v___y_3247_);
v___x_3251_ = l_Lean_Syntax_isNone(v___x_3250_);
if (v___x_3251_ == 0)
{
uint8_t v___x_3252_; 
lean_inc(v___x_3250_);
v___x_3252_ = l_Lean_Syntax_matchesNull(v___x_3250_, v___y_3236_);
lean_dec(v___y_3236_);
if (v___x_3252_ == 0)
{
lean_object* v___x_3253_; 
lean_dec(v___x_3250_);
lean_dec(v_args_3248_);
lean_dec(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec(v_tk_3163_);
v___x_3253_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3253_;
}
else
{
lean_object* v_usingTk_x3f_3254_; lean_object* v_usingArg_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_usingTk_x3f_3254_ = l_Lean_Syntax_getArg(v___x_3250_, v___x_3162_);
v_usingArg_3255_ = l_Lean_Syntax_getArg(v___x_3250_, v___x_3164_);
lean_dec(v___x_3250_);
v___x_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3256_, 0, v_usingTk_x3f_3254_);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_usingArg_3255_);
v___y_3195_ = v___y_3228_;
v___y_3196_ = v___y_3229_;
v___y_3197_ = v___y_3230_;
v___y_3198_ = v___y_3231_;
v___y_3199_ = v___y_3232_;
v___y_3200_ = v___y_3233_;
v___y_3201_ = v___y_3234_;
v___y_3202_ = v___y_3235_;
v___y_3203_ = v_args_3248_;
v___y_3204_ = v___y_3237_;
v___y_3205_ = v___y_3238_;
v___y_3206_ = v___y_3239_;
v___y_3207_ = v___y_3240_;
v___y_3208_ = v___y_3241_;
v___y_3209_ = v___y_3243_;
v___y_3210_ = v___y_3242_;
v___y_3211_ = v___x_3249_;
v___y_3212_ = v___y_3244_;
v___y_3213_ = v___y_3245_;
v___y_3214_ = v___y_3246_;
v_usingTk_x3f_3215_ = v___x_3256_;
v_usingArg_3216_ = v___x_3257_;
goto v___jp_3194_;
}
}
else
{
lean_object* v___x_3258_; 
lean_dec(v___x_3250_);
lean_dec(v___y_3236_);
v___x_3258_ = lean_box(0);
v___y_3195_ = v___y_3228_;
v___y_3196_ = v___y_3229_;
v___y_3197_ = v___y_3230_;
v___y_3198_ = v___y_3231_;
v___y_3199_ = v___y_3232_;
v___y_3200_ = v___y_3233_;
v___y_3201_ = v___y_3234_;
v___y_3202_ = v___y_3235_;
v___y_3203_ = v_args_3248_;
v___y_3204_ = v___y_3237_;
v___y_3205_ = v___y_3238_;
v___y_3206_ = v___y_3239_;
v___y_3207_ = v___y_3240_;
v___y_3208_ = v___y_3241_;
v___y_3209_ = v___y_3243_;
v___y_3210_ = v___y_3242_;
v___y_3211_ = v___x_3249_;
v___y_3212_ = v___y_3244_;
v___y_3213_ = v___y_3245_;
v___y_3214_ = v___y_3246_;
v_usingTk_x3f_3215_ = v___x_3258_;
v_usingArg_3216_ = v___x_3258_;
goto v___jp_3194_;
}
}
v___jp_3259_:
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = l_Lean_Syntax_getArg(v___y_3270_, v___y_3269_);
lean_dec(v___y_3269_);
v___x_3282_ = l_Lean_Syntax_isNone(v___x_3281_);
if (v___x_3282_ == 0)
{
uint8_t v___x_3283_; 
lean_inc(v___x_3281_);
v___x_3283_ = l_Lean_Syntax_matchesNull(v___x_3281_, v___x_3164_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; 
lean_dec(v___x_3281_);
lean_dec(v_only_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec(v_tk_3163_);
v___x_3284_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3284_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = l_Lean_Syntax_getArg(v___x_3281_, v___x_3162_);
lean_dec(v___x_3281_);
v___x_3286_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
lean_inc(v___x_3285_);
v___x_3287_ = l_Lean_Syntax_isOfKind(v___x_3285_, v___x_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_dec(v___x_3285_);
lean_dec(v_only_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec(v_tk_3163_);
v___x_3288_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3288_;
}
else
{
lean_object* v___x_3289_; lean_object* v_args_3290_; lean_object* v___x_3291_; 
v___x_3289_ = l_Lean_Syntax_getArg(v___x_3285_, v___x_3164_);
lean_dec(v___x_3285_);
v_args_3290_ = l_Lean_Syntax_getArgs(v___x_3289_);
lean_dec(v___x_3289_);
v___x_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3291_, 0, v_args_3290_);
v___y_3228_ = v___y_3260_;
v___y_3229_ = v___y_3261_;
v___y_3230_ = v___y_3274_;
v___y_3231_ = v___y_3280_;
v___y_3232_ = v___y_3266_;
v___y_3233_ = v___y_3268_;
v___y_3234_ = v___y_3267_;
v___y_3235_ = v_only_3272_;
v___y_3236_ = v___y_3271_;
v___y_3237_ = v___y_3279_;
v___y_3238_ = v___y_3276_;
v___y_3239_ = v___y_3273_;
v___y_3240_ = v___y_3277_;
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3264_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___y_3265_;
v___y_3245_ = v___y_3275_;
v___y_3246_ = v___y_3278_;
v___y_3247_ = v___y_3270_;
v_args_3248_ = v___x_3291_;
goto v___jp_3227_;
}
}
}
else
{
lean_object* v___x_3292_; 
lean_dec(v___x_3281_);
v___x_3292_ = lean_box(0);
v___y_3228_ = v___y_3260_;
v___y_3229_ = v___y_3261_;
v___y_3230_ = v___y_3274_;
v___y_3231_ = v___y_3280_;
v___y_3232_ = v___y_3266_;
v___y_3233_ = v___y_3268_;
v___y_3234_ = v___y_3267_;
v___y_3235_ = v_only_3272_;
v___y_3236_ = v___y_3271_;
v___y_3237_ = v___y_3279_;
v___y_3238_ = v___y_3276_;
v___y_3239_ = v___y_3273_;
v___y_3240_ = v___y_3277_;
v___y_3241_ = v___y_3262_;
v___y_3242_ = v___y_3264_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___y_3265_;
v___y_3245_ = v___y_3275_;
v___y_3246_ = v___y_3278_;
v___y_3247_ = v___y_3270_;
v_args_3248_ = v___x_3292_;
goto v___jp_3227_;
}
}
v___jp_3293_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3305_ = lean_unsigned_to_nat(3u);
v___x_3306_ = l_Lean_Syntax_getArg(v_stx_3144_, v___x_3305_);
lean_dec(v_stx_3144_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7));
lean_inc(v___x_3306_);
v___x_3308_ = l_Lean_Syntax_isOfKind(v___x_3306_, v___x_3307_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; 
lean_dec(v___x_3306_);
lean_dec(v_unfold_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3296_);
lean_dec(v_tk_3163_);
v___x_3309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3309_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3310_ = l_Lean_Syntax_getArg(v___x_3306_, v___x_3162_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9));
lean_inc(v___x_3310_);
v___x_3312_ = l_Lean_Syntax_isOfKind(v___x_3310_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec(v___x_3310_);
lean_dec(v___x_3306_);
lean_dec(v_unfold_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3296_);
lean_dec(v_tk_3163_);
v___x_3313_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v___x_3314_ = l_Lean_Syntax_getArg(v___x_3306_, v___x_3164_);
v___x_3315_ = l_Lean_Syntax_getArg(v___x_3306_, v___y_3303_);
v___x_3316_ = l_Lean_Syntax_isNone(v___x_3315_);
if (v___x_3316_ == 0)
{
uint8_t v___x_3317_; 
lean_inc(v___x_3315_);
v___x_3317_ = l_Lean_Syntax_matchesNull(v___x_3315_, v___x_3164_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_dec(v___x_3315_);
lean_dec(v___x_3314_);
lean_dec(v___x_3310_);
lean_dec(v___x_3306_);
lean_dec(v_unfold_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3296_);
lean_dec(v_tk_3163_);
v___x_3318_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3318_;
}
else
{
lean_object* v_only_3319_; lean_object* v___x_3320_; 
v_only_3319_ = l_Lean_Syntax_getArg(v___x_3315_, v___x_3162_);
lean_dec(v___x_3315_);
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_only_3319_);
lean_inc(v___y_3303_);
v___y_3260_ = v___x_3312_;
v___y_3261_ = v___x_3307_;
v___y_3262_ = v___y_3296_;
v___y_3263_ = v___x_3310_;
v___y_3264_ = v___x_3305_;
v___y_3265_ = v_unfold_3304_;
v___y_3266_ = v___x_3311_;
v___y_3267_ = v___y_3303_;
v___y_3268_ = v___x_3314_;
v___y_3269_ = v___x_3305_;
v___y_3270_ = v___x_3306_;
v___y_3271_ = v___y_3303_;
v_only_3272_ = v___x_3320_;
v___y_3273_ = v___y_3302_;
v___y_3274_ = v___y_3298_;
v___y_3275_ = v___y_3301_;
v___y_3276_ = v___y_3295_;
v___y_3277_ = v___y_3300_;
v___y_3278_ = v___y_3294_;
v___y_3279_ = v___y_3297_;
v___y_3280_ = v___y_3299_;
goto v___jp_3259_;
}
}
else
{
lean_object* v___x_3321_; 
lean_dec(v___x_3315_);
v___x_3321_ = lean_box(0);
lean_inc(v___y_3303_);
v___y_3260_ = v___x_3312_;
v___y_3261_ = v___x_3307_;
v___y_3262_ = v___y_3296_;
v___y_3263_ = v___x_3310_;
v___y_3264_ = v___x_3305_;
v___y_3265_ = v_unfold_3304_;
v___y_3266_ = v___x_3311_;
v___y_3267_ = v___y_3303_;
v___y_3268_ = v___x_3314_;
v___y_3269_ = v___x_3305_;
v___y_3270_ = v___x_3306_;
v___y_3271_ = v___y_3303_;
v_only_3272_ = v___x_3321_;
v___y_3273_ = v___y_3302_;
v___y_3274_ = v___y_3298_;
v___y_3275_ = v___y_3301_;
v___y_3276_ = v___y_3295_;
v___y_3277_ = v___y_3300_;
v___y_3278_ = v___y_3294_;
v___y_3279_ = v___y_3297_;
v___y_3280_ = v___y_3299_;
goto v___jp_3259_;
}
}
}
}
v___jp_3322_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3332_ = lean_unsigned_to_nat(2u);
v___x_3333_ = l_Lean_Syntax_getArg(v_stx_3144_, v___x_3332_);
v___x_3334_ = l_Lean_Syntax_isNone(v___x_3333_);
if (v___x_3334_ == 0)
{
uint8_t v___x_3335_; 
lean_inc(v___x_3333_);
v___x_3335_ = l_Lean_Syntax_matchesNull(v___x_3333_, v___x_3164_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec(v___x_3333_);
lean_dec(v_squeeze_3323_);
lean_dec(v_tk_3163_);
lean_dec(v_stx_3144_);
v___x_3336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3336_;
}
else
{
lean_object* v_unfold_3337_; lean_object* v___x_3338_; 
v_unfold_3337_ = l_Lean_Syntax_getArg(v___x_3333_, v___x_3162_);
lean_dec(v___x_3333_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_unfold_3337_);
v___y_3294_ = v___y_3329_;
v___y_3295_ = v___y_3327_;
v___y_3296_ = v_squeeze_3323_;
v___y_3297_ = v___y_3330_;
v___y_3298_ = v___y_3325_;
v___y_3299_ = v___y_3331_;
v___y_3300_ = v___y_3328_;
v___y_3301_ = v___y_3326_;
v___y_3302_ = v___y_3324_;
v___y_3303_ = v___x_3332_;
v_unfold_3304_ = v___x_3338_;
goto v___jp_3293_;
}
}
else
{
lean_object* v___x_3339_; 
lean_dec(v___x_3333_);
v___x_3339_ = lean_box(0);
v___y_3294_ = v___y_3329_;
v___y_3295_ = v___y_3327_;
v___y_3296_ = v_squeeze_3323_;
v___y_3297_ = v___y_3330_;
v___y_3298_ = v___y_3325_;
v___y_3299_ = v___y_3331_;
v___y_3300_ = v___y_3328_;
v___y_3301_ = v___y_3326_;
v___y_3302_ = v___y_3324_;
v___y_3303_ = v___x_3332_;
v_unfold_3304_ = v___x_3339_;
goto v___jp_3293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3347_, lean_object* v_stx_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
uint8_t v_useReducible_boxed_3358_; lean_object* v_res_3359_; 
v_useReducible_boxed_3358_ = lean_unbox(v_useReducible_3347_);
v_res_3359_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3358_, v_stx_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3360_, lean_object* v_val_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3360_, v_val_3361_, v___y_3367_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3372_, lean_object* v_val_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3372_, v_val_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3384_, v___y_3392_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v_00_u03b1_3406_, lean_object* v_msg_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_3407_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_msg_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_3418_, v_msg_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_00_u03b1_3430_, lean_object* v_x_3431_, lean_object* v_mkInfoTree_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_3431_, v_mkInfoTree_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_00_u03b1_3443_, lean_object* v_x_3444_, lean_object* v_mkInfoTree_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_3443_, v_x_3444_, v_mkInfoTree_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3456_, lean_object* v_x_3457_, lean_object* v_x_3458_, lean_object* v_x_3459_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3457_, v_x_3458_, v_x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3461_, lean_object* v_m_3462_, lean_object* v_a_3463_){
_start:
{
uint8_t v___x_3464_; 
v___x_3464_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3462_, v_a_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3465_, lean_object* v_m_3466_, lean_object* v_a_3467_){
_start:
{
uint8_t v_res_3468_; lean_object* v_r_3469_; 
v_res_3468_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_3465_, v_m_3466_, v_a_3467_);
lean_dec_ref(v_a_3467_);
lean_dec_ref(v_m_3466_);
v_r_3469_ = lean_box(v_res_3468_);
return v_r_3469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3470_, lean_object* v_m_3471_, lean_object* v_a_3472_, lean_object* v_b_3473_){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_m_3471_, v_a_3472_, v_b_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3475_, v___y_3476_, v___y_3482_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(v_mvarId_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v_mvarId_3487_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3499_, v___y_3500_, v___y_3506_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_mvarId_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v_mvarId_3511_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3523_, lean_object* v_x_3524_, size_t v_x_3525_, size_t v_x_3526_, lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_3524_, v_x_3525_, v_x_3526_, v_x_3527_, v_x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3530_, lean_object* v_x_3531_, lean_object* v_x_3532_, lean_object* v_x_3533_, lean_object* v_x_3534_, lean_object* v_x_3535_){
_start:
{
size_t v_x_99109__boxed_3536_; size_t v_x_99110__boxed_3537_; lean_object* v_res_3538_; 
v_x_99109__boxed_3536_ = lean_unbox_usize(v_x_3532_);
lean_dec(v_x_3532_);
v_x_99110__boxed_3537_ = lean_unbox_usize(v_x_3533_);
lean_dec(v_x_3533_);
v_res_3538_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_3530_, v_x_3531_, v_x_99109__boxed_3536_, v_x_99110__boxed_3537_, v_x_3534_, v_x_3535_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(lean_object* v_ref_3539_, lean_object* v_msgData_3540_, uint8_t v_severity_3541_, uint8_t v_isSilent_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_3539_, v_msgData_3540_, v_severity_3541_, v_isSilent_3542_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3553_, lean_object* v_msgData_3554_, lean_object* v_severity_3555_, lean_object* v_isSilent_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
uint8_t v_severity_boxed_3566_; uint8_t v_isSilent_boxed_3567_; lean_object* v_res_3568_; 
v_severity_boxed_3566_ = lean_unbox(v_severity_3555_);
v_isSilent_boxed_3567_ = lean_unbox(v_isSilent_3556_);
v_res_3568_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(v_ref_3553_, v_msgData_3554_, v_severity_boxed_3566_, v_isSilent_boxed_3567_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v_ref_3553_);
return v_res_3568_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3569_, lean_object* v_a_3570_, lean_object* v_x_3571_){
_start:
{
uint8_t v___x_3572_; 
v___x_3572_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3570_, v_x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3573_, lean_object* v_a_3574_, lean_object* v_x_3575_){
_start:
{
uint8_t v_res_3576_; lean_object* v_r_3577_; 
v_res_3576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3573_, v_a_3574_, v_x_3575_);
lean_dec(v_x_3575_);
lean_dec_ref(v_a_3574_);
v_r_3577_ = lean_box(v_res_3576_);
return v_r_3577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3578_, lean_object* v_data_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3581_, lean_object* v_n_3582_, lean_object* v_k_3583_, lean_object* v_v_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3582_, v_k_3583_, v_v_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3586_, size_t v_depth_3587_, lean_object* v_keys_3588_, lean_object* v_vals_3589_, lean_object* v_heq_3590_, lean_object* v_i_3591_, lean_object* v_entries_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3587_, v_keys_3588_, v_vals_3589_, v_i_3591_, v_entries_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3594_, lean_object* v_depth_3595_, lean_object* v_keys_3596_, lean_object* v_vals_3597_, lean_object* v_heq_3598_, lean_object* v_i_3599_, lean_object* v_entries_3600_){
_start:
{
size_t v_depth_boxed_3601_; lean_object* v_res_3602_; 
v_depth_boxed_3601_ = lean_unbox_usize(v_depth_3595_);
lean_dec(v_depth_3595_);
v_res_3602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3594_, v_depth_boxed_3601_, v_keys_3596_, v_vals_3597_, v_heq_3598_, v_i_3599_, v_entries_3600_);
lean_dec_ref(v_vals_3597_);
lean_dec_ref(v_keys_3596_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3603_, lean_object* v_i_3604_, lean_object* v_source_3605_, lean_object* v_target_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3604_, v_source_3605_, v_target_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3608_, lean_object* v_x_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3609_, v_x_3610_, v_x_3611_, v_x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3614_, lean_object* v_x_3615_, lean_object* v_x_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3615_, v_x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
uint8_t v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = 1;
v___x_3629_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_3628_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3650_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3651_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3653_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3654_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3650_, v___x_3651_, v___x_3652_, v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3685_ = l_Lean_addBuiltinDeclarationRanges(v___x_3683_, v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_3692_);
lean_dec(v_x_3692_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; uint8_t v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v___x_3746_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_3705_);
v___x_3747_ = l_Lean_Syntax_isOfKind(v_stx_3705_, v___x_3746_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; 
lean_dec(v_stx_3705_);
v___x_3748_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3748_;
}
else
{
lean_object* v___x_3749_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; uint8_t v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; uint8_t v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; uint8_t v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; uint8_t v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v_tk_3876_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v_args_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___x_3936_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v_only_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v_unfold_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v_squeeze_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_3749_ = lean_unsigned_to_nat(0u);
v_tk_3876_ = l_Lean_Syntax_getArg(v_stx_3705_, v___x_3749_);
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_4012_ = l_Lean_Syntax_getArg(v_stx_3705_, v___x_3936_);
v___x_4013_ = l_Lean_Syntax_isNone(v___x_4012_);
if (v___x_4013_ == 0)
{
uint8_t v___x_4014_; 
lean_inc(v___x_4012_);
v___x_4014_ = l_Lean_Syntax_matchesNull(v___x_4012_, v___x_3936_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec(v___x_4012_);
lean_dec(v_tk_3876_);
lean_dec(v_stx_3705_);
v___x_4015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4015_;
}
else
{
lean_object* v_squeeze_4016_; lean_object* v___x_4017_; 
v_squeeze_4016_ = l_Lean_Syntax_getArg(v___x_4012_, v___x_3749_);
lean_dec(v___x_4012_);
v___x_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4017_, 0, v_squeeze_4016_);
v_squeeze_3995_ = v___x_4017_;
v___y_3996_ = v_a_3706_;
v___y_3997_ = v_a_3707_;
v___y_3998_ = v_a_3708_;
v___y_3999_ = v_a_3709_;
v___y_4000_ = v_a_3710_;
v___y_4001_ = v_a_3711_;
v___y_4002_ = v_a_3712_;
v___y_4003_ = v_a_3713_;
goto v___jp_3994_;
}
}
else
{
lean_object* v___x_4018_; 
lean_dec(v___x_4012_);
v___x_4018_ = lean_box(0);
v_squeeze_3995_ = v___x_4018_;
v___y_3996_ = v_a_3706_;
v___y_3997_ = v_a_3707_;
v___y_3998_ = v_a_3708_;
v___y_3999_ = v_a_3709_;
v___y_4000_ = v_a_3710_;
v___y_4001_ = v_a_3711_;
v___y_4002_ = v_a_3712_;
v___y_4003_ = v_a_3713_;
goto v___jp_3994_;
}
v___jp_3750_:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_inc_ref(v___y_3770_);
v___x_3773_ = l_Array_append___redArg(v___y_3770_, v___y_3772_);
lean_dec_ref(v___y_3772_);
lean_inc(v___y_3766_);
lean_inc(v___y_3760_);
v___x_3774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3774_, 0, v___y_3760_);
lean_ctor_set(v___x_3774_, 1, v___y_3766_);
lean_ctor_set(v___x_3774_, 2, v___x_3773_);
if (lean_obj_tag(v___y_3762_) == 1)
{
lean_object* v_val_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_val_3775_ = lean_ctor_get(v___y_3762_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v___y_3762_, 1);
v___x_3776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
v___x_3777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3760_, 4);
v___x_3778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___y_3760_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
lean_inc_ref(v___y_3770_);
v___x_3779_ = l_Array_append___redArg(v___y_3770_, v_val_3775_);
lean_dec(v_val_3775_);
lean_inc(v___y_3766_);
v___x_3780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3780_, 0, v___y_3760_);
lean_ctor_set(v___x_3780_, 1, v___y_3766_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___y_3760_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = l_Lean_Syntax_node3(v___y_3760_, v___x_3776_, v___x_3778_, v___x_3780_, v___x_3782_);
v___x_3784_ = l_Array_mkArray1___redArg(v___x_3783_);
v___y_3716_ = v___y_3751_;
v___y_3717_ = v___y_3752_;
v___y_3718_ = v___x_3774_;
v___y_3719_ = v___y_3753_;
v___y_3720_ = v___y_3754_;
v___y_3721_ = v___y_3755_;
v___y_3722_ = v___y_3756_;
v___y_3723_ = v___y_3757_;
v___y_3724_ = v___y_3758_;
v___y_3725_ = v___y_3759_;
v___y_3726_ = v___y_3761_;
v___y_3727_ = v___y_3760_;
v___y_3728_ = v___y_3764_;
v___y_3729_ = v___y_3763_;
v___y_3730_ = v___y_3765_;
v___y_3731_ = v___y_3766_;
v___y_3732_ = v___y_3769_;
v___y_3733_ = v___y_3768_;
v___y_3734_ = v___y_3770_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3771_;
v___y_3737_ = v___x_3784_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3785_; 
lean_dec(v___y_3762_);
v___x_3785_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3716_ = v___y_3751_;
v___y_3717_ = v___y_3752_;
v___y_3718_ = v___x_3774_;
v___y_3719_ = v___y_3753_;
v___y_3720_ = v___y_3754_;
v___y_3721_ = v___y_3755_;
v___y_3722_ = v___y_3756_;
v___y_3723_ = v___y_3757_;
v___y_3724_ = v___y_3758_;
v___y_3725_ = v___y_3759_;
v___y_3726_ = v___y_3761_;
v___y_3727_ = v___y_3760_;
v___y_3728_ = v___y_3764_;
v___y_3729_ = v___y_3763_;
v___y_3730_ = v___y_3765_;
v___y_3731_ = v___y_3766_;
v___y_3732_ = v___y_3769_;
v___y_3733_ = v___y_3768_;
v___y_3734_ = v___y_3770_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3771_;
v___y_3737_ = v___x_3785_;
goto v___jp_3715_;
}
}
v___jp_3786_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
lean_inc_ref(v___y_3805_);
v___x_3809_ = l_Array_append___redArg(v___y_3805_, v___y_3808_);
lean_dec_ref(v___y_3808_);
lean_inc(v___y_3801_);
lean_inc(v___y_3795_);
v___x_3810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3810_, 0, v___y_3795_);
lean_ctor_set(v___x_3810_, 1, v___y_3801_);
lean_ctor_set(v___x_3810_, 2, v___x_3809_);
if (lean_obj_tag(v___y_3806_) == 1)
{
lean_object* v_val_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v_val_3811_ = lean_ctor_get(v___y_3806_, 0);
lean_inc(v_val_3811_);
lean_dec_ref_known(v___y_3806_, 1);
v___x_3812_ = l_Lean_SourceInfo_fromRef(v_val_3811_, v___x_3747_);
lean_dec(v_val_3811_);
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = l_Array_mkArray1___redArg(v___x_3814_);
v___y_3751_ = v___x_3810_;
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
v___y_3757_ = v___y_3792_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3794_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v___y_3796_;
v___y_3762_ = v___y_3799_;
v___y_3763_ = v___y_3798_;
v___y_3764_ = v___y_3797_;
v___y_3765_ = v___y_3800_;
v___y_3766_ = v___y_3801_;
v___y_3767_ = v___y_3804_;
v___y_3768_ = v___y_3803_;
v___y_3769_ = v___y_3802_;
v___y_3770_ = v___y_3805_;
v___y_3771_ = v___y_3807_;
v___y_3772_ = v___x_3815_;
goto v___jp_3750_;
}
else
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3806_);
lean_dec(v___y_3806_);
v___y_3751_ = v___x_3810_;
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3791_;
v___y_3757_ = v___y_3792_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3794_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v___y_3796_;
v___y_3762_ = v___y_3799_;
v___y_3763_ = v___y_3798_;
v___y_3764_ = v___y_3797_;
v___y_3765_ = v___y_3800_;
v___y_3766_ = v___y_3801_;
v___y_3767_ = v___y_3804_;
v___y_3768_ = v___y_3803_;
v___y_3769_ = v___y_3802_;
v___y_3770_ = v___y_3805_;
v___y_3771_ = v___y_3807_;
v___y_3772_ = v___x_3816_;
goto v___jp_3750_;
}
}
v___jp_3817_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_inc_ref(v___y_3835_);
v___x_3839_ = l_Array_append___redArg(v___y_3835_, v___y_3838_);
lean_dec_ref(v___y_3838_);
lean_inc(v___y_3831_);
lean_inc(v___y_3826_);
v___x_3840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3840_, 0, v___y_3826_);
lean_ctor_set(v___x_3840_, 1, v___y_3831_);
lean_ctor_set(v___x_3840_, 2, v___x_3839_);
v___x_3841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7));
if (lean_obj_tag(v___y_3824_) == 0)
{
lean_object* v___x_3842_; 
v___x_3842_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3787_ = v___y_3818_;
v___y_3788_ = v___y_3819_;
v___y_3789_ = v___y_3820_;
v___y_3790_ = v___y_3821_;
v___y_3791_ = v___y_3822_;
v___y_3792_ = v___x_3840_;
v___y_3793_ = v___y_3823_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v___y_3826_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3829_;
v___y_3798_ = v___y_3830_;
v___y_3799_ = v___y_3828_;
v___y_3800_ = v___x_3841_;
v___y_3801_ = v___y_3831_;
v___y_3802_ = v___y_3834_;
v___y_3803_ = v___y_3833_;
v___y_3804_ = v___y_3832_;
v___y_3805_ = v___y_3835_;
v___y_3806_ = v___y_3836_;
v___y_3807_ = v___y_3837_;
v___y_3808_ = v___x_3842_;
goto v___jp_3786_;
}
else
{
lean_object* v_val_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v_val_3843_ = lean_ctor_get(v___y_3824_, 0);
lean_inc(v_val_3843_);
lean_dec_ref_known(v___y_3824_, 1);
v___x_3844_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3845_ = lean_array_push(v___x_3844_, v_val_3843_);
v___y_3787_ = v___y_3818_;
v___y_3788_ = v___y_3819_;
v___y_3789_ = v___y_3820_;
v___y_3790_ = v___y_3821_;
v___y_3791_ = v___y_3822_;
v___y_3792_ = v___x_3840_;
v___y_3793_ = v___y_3823_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v___y_3826_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3829_;
v___y_3798_ = v___y_3830_;
v___y_3799_ = v___y_3828_;
v___y_3800_ = v___x_3841_;
v___y_3801_ = v___y_3831_;
v___y_3802_ = v___y_3834_;
v___y_3803_ = v___y_3833_;
v___y_3804_ = v___y_3832_;
v___y_3805_ = v___y_3835_;
v___y_3806_ = v___y_3836_;
v___y_3807_ = v___y_3837_;
v___y_3808_ = v___x_3845_;
goto v___jp_3786_;
}
}
v___jp_3846_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
lean_inc_ref(v___y_3864_);
v___x_3868_ = l_Array_append___redArg(v___y_3864_, v___y_3867_);
lean_dec_ref(v___y_3867_);
lean_inc(v___y_3860_);
lean_inc(v___y_3854_);
v___x_3869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3869_, 0, v___y_3854_);
lean_ctor_set(v___x_3869_, 1, v___y_3860_);
lean_ctor_set(v___x_3869_, 2, v___x_3868_);
if (lean_obj_tag(v___y_3856_) == 1)
{
lean_object* v_val_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v_val_3870_ = lean_ctor_get(v___y_3856_, 0);
lean_inc(v_val_3870_);
lean_dec_ref_known(v___y_3856_, 1);
v___x_3871_ = l_Lean_SourceInfo_fromRef(v_val_3870_, v___x_3747_);
lean_dec(v_val_3870_);
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_3873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l_Array_mkArray1___redArg(v___x_3873_);
v___y_3818_ = v___y_3847_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3850_;
v___y_3822_ = v___y_3851_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3853_;
v___y_3825_ = v___x_3869_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v___y_3855_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3859_;
v___y_3830_ = v___y_3857_;
v___y_3831_ = v___y_3860_;
v___y_3832_ = v___y_3863_;
v___y_3833_ = v___y_3862_;
v___y_3834_ = v___y_3861_;
v___y_3835_ = v___y_3864_;
v___y_3836_ = v___y_3865_;
v___y_3837_ = v___y_3866_;
v___y_3838_ = v___x_3874_;
goto v___jp_3817_;
}
else
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3856_);
lean_dec(v___y_3856_);
v___y_3818_ = v___y_3847_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3850_;
v___y_3822_ = v___y_3851_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3853_;
v___y_3825_ = v___x_3869_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v___y_3855_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3859_;
v___y_3830_ = v___y_3857_;
v___y_3831_ = v___y_3860_;
v___y_3832_ = v___y_3863_;
v___y_3833_ = v___y_3862_;
v___y_3834_ = v___y_3861_;
v___y_3835_ = v___y_3864_;
v___y_3836_ = v___y_3865_;
v___y_3837_ = v___y_3866_;
v___y_3838_ = v___x_3875_;
goto v___jp_3817_;
}
}
v___jp_3877_:
{
lean_object* v_ref_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_ref_3893_ = lean_ctor_get(v___y_3878_, 5);
v___x_3894_ = 0;
v___x_3895_ = l_Lean_SourceInfo_fromRef(v_ref_3893_, v___x_3894_);
v___x_3896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3898_ = l_Lean_SourceInfo_fromRef(v_tk_3876_, v___x_3747_);
lean_dec(v_tk_3876_);
v___x_3899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
lean_ctor_set(v___x_3899_, 1, v___x_3896_);
v___x_3900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_3901_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_3886_) == 1)
{
lean_object* v_val_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_val_3902_ = lean_ctor_get(v___y_3886_, 0);
lean_inc(v_val_3902_);
lean_dec_ref_known(v___y_3886_, 1);
v___x_3903_ = l_Lean_SourceInfo_fromRef(v_val_3902_, v___x_3747_);
lean_dec(v_val_3902_);
v___x_3904_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_3905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3903_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
v___x_3906_ = l_Array_mkArray1___redArg(v___x_3905_);
v___y_3847_ = v___y_3878_;
v___y_3848_ = v___y_3879_;
v___y_3849_ = v___x_3897_;
v___y_3850_ = v___y_3880_;
v___y_3851_ = v___x_3899_;
v___y_3852_ = v___x_3894_;
v___y_3853_ = v___y_3892_;
v___y_3854_ = v___x_3895_;
v___y_3855_ = v___y_3881_;
v___y_3856_ = v___y_3882_;
v___y_3857_ = v___y_3883_;
v___y_3858_ = v___y_3884_;
v___y_3859_ = v___y_3885_;
v___y_3860_ = v___x_3900_;
v___y_3861_ = v___y_3887_;
v___y_3862_ = v___y_3888_;
v___y_3863_ = v___y_3889_;
v___y_3864_ = v___x_3901_;
v___y_3865_ = v___y_3890_;
v___y_3866_ = v___y_3891_;
v___y_3867_ = v___x_3906_;
goto v___jp_3846_;
}
else
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3886_);
lean_dec(v___y_3886_);
v___y_3847_ = v___y_3878_;
v___y_3848_ = v___y_3879_;
v___y_3849_ = v___x_3897_;
v___y_3850_ = v___y_3880_;
v___y_3851_ = v___x_3899_;
v___y_3852_ = v___x_3894_;
v___y_3853_ = v___y_3892_;
v___y_3854_ = v___x_3895_;
v___y_3855_ = v___y_3881_;
v___y_3856_ = v___y_3882_;
v___y_3857_ = v___y_3883_;
v___y_3858_ = v___y_3884_;
v___y_3859_ = v___y_3885_;
v___y_3860_ = v___x_3900_;
v___y_3861_ = v___y_3887_;
v___y_3862_ = v___y_3888_;
v___y_3863_ = v___y_3889_;
v___y_3864_ = v___x_3901_;
v___y_3865_ = v___y_3890_;
v___y_3866_ = v___y_3891_;
v___y_3867_ = v___x_3907_;
goto v___jp_3846_;
}
}
v___jp_3908_:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = lean_unsigned_to_nat(5u);
v___x_3925_ = l_Lean_Syntax_getArg(v___y_3910_, v___x_3924_);
lean_dec(v___y_3910_);
v___x_3926_ = l_Lean_Syntax_getOptional_x3f(v___y_3912_);
lean_dec(v___y_3912_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_box(0);
v___y_3878_ = v___y_3922_;
v___y_3879_ = v___x_3925_;
v___y_3880_ = v___y_3921_;
v___y_3881_ = v___y_3919_;
v___y_3882_ = v___y_3909_;
v___y_3883_ = v___y_3916_;
v___y_3884_ = v_args_3915_;
v___y_3885_ = v___y_3918_;
v___y_3886_ = v___y_3911_;
v___y_3887_ = v___y_3923_;
v___y_3888_ = v___y_3917_;
v___y_3889_ = v___y_3913_;
v___y_3890_ = v___y_3914_;
v___y_3891_ = v___y_3920_;
v___y_3892_ = v___x_3927_;
goto v___jp_3877_;
}
else
{
lean_object* v_val_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
v_val_3928_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3926_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_val_3928_);
lean_dec(v___x_3926_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_val_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
v___y_3878_ = v___y_3922_;
v___y_3879_ = v___x_3925_;
v___y_3880_ = v___y_3921_;
v___y_3881_ = v___y_3919_;
v___y_3882_ = v___y_3909_;
v___y_3883_ = v___y_3916_;
v___y_3884_ = v_args_3915_;
v___y_3885_ = v___y_3918_;
v___y_3886_ = v___y_3911_;
v___y_3887_ = v___y_3923_;
v___y_3888_ = v___y_3917_;
v___y_3889_ = v___y_3913_;
v___y_3890_ = v___y_3914_;
v___y_3891_ = v___y_3920_;
v___y_3892_ = v___x_3933_;
goto v___jp_3877_;
}
}
}
}
v___jp_3937_:
{
lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3953_ = l_Lean_Syntax_getArg(v___y_3939_, v___y_3941_);
v___x_3954_ = l_Lean_Syntax_isNone(v___x_3953_);
if (v___x_3954_ == 0)
{
uint8_t v___x_3955_; 
lean_inc(v___x_3953_);
v___x_3955_ = l_Lean_Syntax_matchesNull(v___x_3953_, v___x_3936_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec(v___x_3953_);
lean_dec(v_only_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec(v_tk_3876_);
v___x_3956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3957_ = l_Lean_Syntax_getArg(v___x_3953_, v___x_3749_);
lean_dec(v___x_3953_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5));
lean_inc(v___x_3957_);
v___x_3959_ = l_Lean_Syntax_isOfKind(v___x_3957_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; 
lean_dec(v___x_3957_);
lean_dec(v_only_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec(v_tk_3876_);
v___x_3960_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v_args_3962_; lean_object* v___x_3963_; 
v___x_3961_ = l_Lean_Syntax_getArg(v___x_3957_, v___x_3936_);
lean_dec(v___x_3957_);
v_args_3962_ = l_Lean_Syntax_getArgs(v___x_3961_);
lean_dec(v___x_3961_);
v___x_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3963_, 0, v_args_3962_);
v___y_3909_ = v___y_3938_;
v___y_3910_ = v___y_3939_;
v___y_3911_ = v___y_3940_;
v___y_3912_ = v___y_3943_;
v___y_3913_ = v___y_3942_;
v___y_3914_ = v_only_3944_;
v_args_3915_ = v___x_3963_;
v___y_3916_ = v___y_3945_;
v___y_3917_ = v___y_3946_;
v___y_3918_ = v___y_3947_;
v___y_3919_ = v___y_3948_;
v___y_3920_ = v___y_3949_;
v___y_3921_ = v___y_3950_;
v___y_3922_ = v___y_3951_;
v___y_3923_ = v___y_3952_;
goto v___jp_3908_;
}
}
}
else
{
lean_object* v___x_3964_; 
lean_dec(v___x_3953_);
v___x_3964_ = lean_box(0);
v___y_3909_ = v___y_3938_;
v___y_3910_ = v___y_3939_;
v___y_3911_ = v___y_3940_;
v___y_3912_ = v___y_3943_;
v___y_3913_ = v___y_3942_;
v___y_3914_ = v_only_3944_;
v_args_3915_ = v___x_3964_;
v___y_3916_ = v___y_3945_;
v___y_3917_ = v___y_3946_;
v___y_3918_ = v___y_3947_;
v___y_3919_ = v___y_3948_;
v___y_3920_ = v___y_3949_;
v___y_3921_ = v___y_3950_;
v___y_3922_ = v___y_3951_;
v___y_3923_ = v___y_3952_;
goto v___jp_3908_;
}
}
v___jp_3965_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3977_ = lean_unsigned_to_nat(3u);
v___x_3978_ = l_Lean_Syntax_getArg(v_stx_3705_, v___x_3977_);
lean_dec(v_stx_3705_);
v___x_3979_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_3978_);
v___x_3980_ = l_Lean_Syntax_isOfKind(v___x_3978_, v___x_3979_);
if (v___x_3980_ == 0)
{
lean_object* v___x_3981_; 
lean_dec(v___x_3978_);
lean_dec(v_unfold_3968_);
lean_dec(v___y_3967_);
lean_dec(v_tk_3876_);
v___x_3981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3982_ = l_Lean_Syntax_getArg(v___x_3978_, v___x_3749_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9));
lean_inc(v___x_3982_);
v___x_3984_ = l_Lean_Syntax_isOfKind(v___x_3982_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; 
lean_dec(v___x_3982_);
lean_dec(v___x_3978_);
lean_dec(v_unfold_3968_);
lean_dec(v___y_3967_);
lean_dec(v_tk_3876_);
v___x_3985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3985_;
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3986_ = l_Lean_Syntax_getArg(v___x_3978_, v___x_3936_);
v___x_3987_ = l_Lean_Syntax_getArg(v___x_3978_, v___y_3966_);
v___x_3988_ = l_Lean_Syntax_isNone(v___x_3987_);
if (v___x_3988_ == 0)
{
uint8_t v___x_3989_; 
lean_inc(v___x_3987_);
v___x_3989_ = l_Lean_Syntax_matchesNull(v___x_3987_, v___x_3936_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; 
lean_dec(v___x_3987_);
lean_dec(v___x_3986_);
lean_dec(v___x_3982_);
lean_dec(v___x_3978_);
lean_dec(v_unfold_3968_);
lean_dec(v___y_3967_);
lean_dec(v_tk_3876_);
v___x_3990_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3990_;
}
else
{
lean_object* v_only_3991_; lean_object* v___x_3992_; 
v_only_3991_ = l_Lean_Syntax_getArg(v___x_3987_, v___x_3749_);
lean_dec(v___x_3987_);
v___x_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3992_, 0, v_only_3991_);
v___y_3938_ = v_unfold_3968_;
v___y_3939_ = v___x_3978_;
v___y_3940_ = v___y_3967_;
v___y_3941_ = v___x_3977_;
v___y_3942_ = v___x_3982_;
v___y_3943_ = v___x_3986_;
v_only_3944_ = v___x_3992_;
v___y_3945_ = v___y_3969_;
v___y_3946_ = v___y_3970_;
v___y_3947_ = v___y_3971_;
v___y_3948_ = v___y_3972_;
v___y_3949_ = v___y_3973_;
v___y_3950_ = v___y_3974_;
v___y_3951_ = v___y_3975_;
v___y_3952_ = v___y_3976_;
goto v___jp_3937_;
}
}
else
{
lean_object* v___x_3993_; 
lean_dec(v___x_3987_);
v___x_3993_ = lean_box(0);
v___y_3938_ = v_unfold_3968_;
v___y_3939_ = v___x_3978_;
v___y_3940_ = v___y_3967_;
v___y_3941_ = v___x_3977_;
v___y_3942_ = v___x_3982_;
v___y_3943_ = v___x_3986_;
v_only_3944_ = v___x_3993_;
v___y_3945_ = v___y_3969_;
v___y_3946_ = v___y_3970_;
v___y_3947_ = v___y_3971_;
v___y_3948_ = v___y_3972_;
v___y_3949_ = v___y_3973_;
v___y_3950_ = v___y_3974_;
v___y_3951_ = v___y_3975_;
v___y_3952_ = v___y_3976_;
goto v___jp_3937_;
}
}
}
}
v___jp_3994_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v___x_4004_ = lean_unsigned_to_nat(2u);
v___x_4005_ = l_Lean_Syntax_getArg(v_stx_3705_, v___x_4004_);
v___x_4006_ = l_Lean_Syntax_isNone(v___x_4005_);
if (v___x_4006_ == 0)
{
uint8_t v___x_4007_; 
lean_inc(v___x_4005_);
v___x_4007_ = l_Lean_Syntax_matchesNull(v___x_4005_, v___x_3936_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; 
lean_dec(v___x_4005_);
lean_dec(v_squeeze_3995_);
lean_dec(v_tk_3876_);
lean_dec(v_stx_3705_);
v___x_4008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4008_;
}
else
{
lean_object* v_unfold_4009_; lean_object* v___x_4010_; 
v_unfold_4009_ = l_Lean_Syntax_getArg(v___x_4005_, v___x_3749_);
lean_dec(v___x_4005_);
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v_unfold_4009_);
v___y_3966_ = v___x_4004_;
v___y_3967_ = v_squeeze_3995_;
v_unfold_3968_ = v___x_4010_;
v___y_3969_ = v___y_3996_;
v___y_3970_ = v___y_3997_;
v___y_3971_ = v___y_3998_;
v___y_3972_ = v___y_3999_;
v___y_3973_ = v___y_4000_;
v___y_3974_ = v___y_4001_;
v___y_3975_ = v___y_4002_;
v___y_3976_ = v___y_4003_;
goto v___jp_3965_;
}
}
else
{
lean_object* v___x_4011_; 
lean_dec(v___x_4005_);
v___x_4011_ = lean_box(0);
v___y_3966_ = v___x_4004_;
v___y_3967_ = v_squeeze_3995_;
v_unfold_3968_ = v___x_4011_;
v___y_3969_ = v___y_3996_;
v___y_3970_ = v___y_3997_;
v___y_3971_ = v___y_3998_;
v___y_3972_ = v___y_3999_;
v___y_3973_ = v___y_4000_;
v___y_3974_ = v___y_4001_;
v___y_3975_ = v___y_4002_;
v___y_3976_ = v___y_4003_;
goto v___jp_3965_;
}
}
}
v___jp_3715_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_inc_ref(v___y_3734_);
v___x_3738_ = l_Array_append___redArg(v___y_3734_, v___y_3737_);
lean_dec_ref(v___y_3737_);
lean_inc_n(v___y_3731_, 2);
lean_inc_n(v___y_3727_, 4);
v___x_3739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3739_, 0, v___y_3727_);
lean_ctor_set(v___x_3739_, 1, v___y_3731_);
lean_ctor_set(v___x_3739_, 2, v___x_3738_);
v___x_3740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___y_3727_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = l_Lean_Syntax_node2(v___y_3727_, v___y_3731_, v___x_3741_, v___y_3719_);
lean_inc(v___y_3730_);
v___x_3743_ = l_Lean_Syntax_node5(v___y_3727_, v___y_3730_, v___y_3735_, v___y_3716_, v___y_3718_, v___x_3739_, v___x_3742_);
lean_inc(v___y_3720_);
v___x_3744_ = l_Lean_Syntax_node4(v___y_3727_, v___y_3720_, v___y_3722_, v___y_3725_, v___y_3723_, v___x_3743_);
v___x_3745_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3724_, v___x_3744_, v___y_3729_, v___y_3733_, v___y_3728_, v___y_3726_, v___y_3736_, v___y_3721_, v___y_3717_, v___y_3732_);
return v___x_3745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4038_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4039_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4040_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4041_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4042_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4038_, v___x_4039_, v___x_4040_, v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4044_;
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
