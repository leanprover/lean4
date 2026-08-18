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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unnecessarySimpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(182, 23, 154, 96, 189, 166, 9, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "enable the 'unnecessary simpa' linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(219, 182, 224, 198, 198, 122, 225, 30)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(171, 130, 7, 230, 108, 210, 159, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_linter_unnecessarySimpa;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0;
static lean_once_cell_t l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1;
static lean_once_cell_t l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 186, 141, 63, 66, 208, 56, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value),LEAN_SCALAR_PTR_LITERAL(158, 198, 190, 154, 66, 126, 242, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpaArgsRest"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 133, 181, 17, 86, 74, 251, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value;
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
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalSimpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value),LEAN_SCALAR_PTR_LITERAL(207, 241, 251, 37, 131, 174, 231, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value),LEAN_SCALAR_PTR_LITERAL(8, 141, 117, 125, 176, 67, 228, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "evalSimpaUsingBang"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 230, 37, 137, 25, 71, 189, 138)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 14, 13, 235, 216, 153, 126, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_54_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
return v_res_56_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object* v_o_57_){
_start:
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = l_Lean_linter_unnecessarySimpa;
v___x_59_ = l_Lean_Linter_getLinterValue(v___x_58_, v_o_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object* v_o_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_o_60_);
lean_dec_ref(v_o_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_box(0);
v___x_64_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0(lean_object* v_x_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; 
lean_inc(v___y_97_);
lean_inc_ref(v___y_96_);
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
v___x_103_ = lean_apply_9(v_x_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, lean_box(0));
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0___boxed(lean_object* v_x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0(v_x_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_mvarId_115_, lean_object* v_x_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___f_126_; lean_object* v___x_127_; 
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_126_, 0, v_x_116_);
lean_closure_set(v___f_126_, 1, v___y_117_);
lean_closure_set(v___f_126_, 2, v___y_118_);
lean_closure_set(v___f_126_, 3, v___y_119_);
lean_closure_set(v___f_126_, 4, v___y_120_);
v___x_127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_115_, v___f_126_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
if (lean_obj_tag(v___x_127_) == 0)
{
return v___x_127_;
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_127_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_mvarId_136_, lean_object* v_x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_mvarId_136_, v_x_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_148_, lean_object* v_mvarId_149_, lean_object* v_x_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_mvarId_149_, v_x_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_161_, lean_object* v_mvarId_162_, lean_object* v_x_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_161_, v_mvarId_162_, v_x_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(32u);
v___x_175_ = lean_mk_empty_array_with_capacity(v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((size_t)5ULL);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_unsigned_to_nat(32u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0);
v___x_182_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_178_);
lean_ctor_set(v___x_182_, 3, v___x_178_);
lean_ctor_set_usize(v___x_182_, 4, v___x_177_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v_infoState_186_; lean_object* v_trees_187_; lean_object* v___x_188_; lean_object* v_infoState_189_; lean_object* v_env_190_; lean_object* v_nextMacroScope_191_; lean_object* v_ngen_192_; lean_object* v_auxDeclNGen_193_; lean_object* v_traceState_194_; lean_object* v_cache_195_; lean_object* v_messages_196_; lean_object* v_snapshotTasks_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_218_; 
v___x_185_ = lean_st_ref_get(v___y_183_);
v_infoState_186_ = lean_ctor_get(v___x_185_, 7);
lean_inc_ref(v_infoState_186_);
lean_dec(v___x_185_);
v_trees_187_ = lean_ctor_get(v_infoState_186_, 2);
lean_inc_ref(v_trees_187_);
lean_dec_ref(v_infoState_186_);
v___x_188_ = lean_st_ref_take(v___y_183_);
v_infoState_189_ = lean_ctor_get(v___x_188_, 7);
v_env_190_ = lean_ctor_get(v___x_188_, 0);
v_nextMacroScope_191_ = lean_ctor_get(v___x_188_, 1);
v_ngen_192_ = lean_ctor_get(v___x_188_, 2);
v_auxDeclNGen_193_ = lean_ctor_get(v___x_188_, 3);
v_traceState_194_ = lean_ctor_get(v___x_188_, 4);
v_cache_195_ = lean_ctor_get(v___x_188_, 5);
v_messages_196_ = lean_ctor_get(v___x_188_, 6);
v_snapshotTasks_197_ = lean_ctor_get(v___x_188_, 8);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_218_ == 0)
{
v___x_199_ = v___x_188_;
v_isShared_200_ = v_isSharedCheck_218_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_snapshotTasks_197_);
lean_inc(v_infoState_189_);
lean_inc(v_messages_196_);
lean_inc(v_cache_195_);
lean_inc(v_traceState_194_);
lean_inc(v_auxDeclNGen_193_);
lean_inc(v_ngen_192_);
lean_inc(v_nextMacroScope_191_);
lean_inc(v_env_190_);
lean_dec(v___x_188_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_218_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
uint8_t v_enabled_201_; lean_object* v_assignment_202_; lean_object* v_lazyAssignment_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v_enabled_201_ = lean_ctor_get_uint8(v_infoState_189_, sizeof(void*)*3);
v_assignment_202_ = lean_ctor_get(v_infoState_189_, 0);
v_lazyAssignment_203_ = lean_ctor_get(v_infoState_189_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_infoState_189_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v_infoState_189_, 2);
lean_dec(v_unused_217_);
v___x_205_ = v_infoState_189_;
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_lazyAssignment_203_);
lean_inc(v_assignment_202_);
lean_dec(v_infoState_189_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 2, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_assignment_202_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_lazyAssignment_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v___x_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*3, v_enabled_201_);
v___x_209_ = v_reuseFailAlloc_215_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 7, v___x_209_);
v___x_211_ = v___x_199_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_env_190_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_nextMacroScope_191_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_ngen_192_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_auxDeclNGen_193_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_traceState_194_);
lean_ctor_set(v_reuseFailAlloc_214_, 5, v_cache_195_);
lean_ctor_set(v_reuseFailAlloc_214_, 6, v_messages_196_);
lean_ctor_set(v_reuseFailAlloc_214_, 7, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_214_, 8, v_snapshotTasks_197_);
v___x_211_ = v_reuseFailAlloc_214_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_st_ref_put(v___y_183_, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_trees_187_);
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_219_);
lean_dec(v___y_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_79973__overap_254_; lean_object* v___x_255_; 
v___f_253_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0));
v___x_79973__overap_254_ = lean_panic_fn_borrowed(v___f_253_, v_msg_243_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_255_ = lean_apply_9(v___x_79973__overap_254_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, lean_box(0));
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___boxed(lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_266_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(lean_object* v_opts_267_, lean_object* v_opt_268_){
_start:
{
lean_object* v_name_269_; lean_object* v_defValue_270_; lean_object* v_map_271_; lean_object* v___x_272_; 
v_name_269_ = lean_ctor_get(v_opt_268_, 0);
v_defValue_270_ = lean_ctor_get(v_opt_268_, 1);
v_map_271_ = lean_ctor_get(v_opts_267_, 0);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_271_, v_name_269_);
if (lean_obj_tag(v___x_272_) == 0)
{
uint8_t v___x_273_; 
v___x_273_ = lean_unbox(v_defValue_270_);
return v___x_273_;
}
else
{
lean_object* v_val_274_; 
v_val_274_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v___x_272_, 1);
if (lean_obj_tag(v_val_274_) == 1)
{
uint8_t v_v_275_; 
v_v_275_ = lean_ctor_get_uint8(v_val_274_, 0);
lean_dec_ref_known(v_val_274_, 0);
return v_v_275_;
}
else
{
uint8_t v___x_276_; 
lean_dec(v_val_274_);
v___x_276_ = lean_unbox(v_defValue_270_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10___boxed(lean_object* v_opts_277_, lean_object* v_opt_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_opts_277_, v_opt_278_);
lean_dec_ref(v_opt_278_);
lean_dec_ref(v_opts_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_ref_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v_ref_290_ = lean_ctor_get(v___y_287_, 5);
v___x_291_ = 0;
v___x_292_ = l_Lean_SourceInfo_fromRef(v_ref_290_, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v_a_304_, lean_object* v_trees_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
v___x_315_ = lean_apply_9(v_a_304_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, lean_box(0));
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v_a_316_);
lean_ctor_set(v___x_320_, 1, v_trees_305_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_trees_305_);
v_a_325_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_315_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_315_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object* v_a_333_, lean_object* v_trees_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v_a_333_, v_trees_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_344_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_351_, lean_object* v_a_352_, uint8_t v___x_353_, uint8_t v___x_354_, lean_object* v_a_355_, lean_object* v_mvarCounter_356_, lean_object* v___x_357_, lean_object* v___x_358_, uint8_t v_useReducible_359_, uint8_t v___x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; 
lean_inc(v_a_351_);
v___x_370_ = l_Lean_MVarId_getType(v_a_351_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_n(v_a_371_, 2);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = l_Lean_mkIdent(v_a_352_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_a_371_);
v___x_374_ = l_Lean_Elab_Term_elabTerm(v___x_372_, v___x_373_, v___x_353_, v___x_353_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___x_409_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v___x_409_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_354_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_550_; 
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; 
v_unused_551_ = lean_ctor_get(v___x_409_, 0);
lean_dec(v_unused_551_);
v___x_411_ = v___x_409_;
v_isShared_412_ = v_isSharedCheck_550_;
goto v_resetjp_410_;
}
else
{
lean_dec(v___x_409_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_550_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; 
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v___y_366_);
lean_inc_ref(v___y_365_);
lean_inc(v_a_375_);
v___x_413_ = lean_infer_type(v_a_375_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; uint8_t v_____do__lift_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
if (v_useReducible_359_ == 0)
{
lean_object* v___x_434_; uint8_t v_foApprox_435_; uint8_t v_ctxApprox_436_; uint8_t v_quasiPatternApprox_437_; uint8_t v_constApprox_438_; uint8_t v_isDefEqStuckEx_439_; uint8_t v_unificationHints_440_; uint8_t v_proofIrrelevance_441_; uint8_t v_offsetCnstrs_442_; uint8_t v_transparency_443_; uint8_t v_etaStruct_444_; uint8_t v_univApprox_445_; uint8_t v_iota_446_; uint8_t v_beta_447_; uint8_t v_proj_448_; uint8_t v_zeta_449_; uint8_t v_zetaDelta_450_; uint8_t v_zetaUnused_451_; uint8_t v_zetaHave_452_; uint8_t v_canUnfoldPredicateConfig_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_484_; 
v___x_434_ = l_Lean_Meta_Context_config(v___y_365_);
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
v_canUnfoldPredicateConfig_453_ = lean_ctor_get_uint8(v___x_434_, 19);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_484_ == 0)
{
v___x_455_ = v___x_434_;
v_isShared_456_ = v_isSharedCheck_484_;
goto v_resetjp_454_;
}
else
{
lean_dec(v___x_434_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_484_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
uint8_t v_trackZetaDelta_457_; lean_object* v_zetaDeltaSet_458_; lean_object* v_lctx_459_; lean_object* v_localInstances_460_; lean_object* v_defEqCtx_x3f_461_; lean_object* v_synthPendingDepth_462_; lean_object* v_customCanUnfoldPredicate_x3f_463_; uint8_t v_univApprox_464_; uint8_t v_inTypeClassResolution_465_; uint8_t v_cacheInferType_466_; lean_object* v___x_468_; 
v_trackZetaDelta_457_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7);
v_zetaDeltaSet_458_ = lean_ctor_get(v___y_365_, 1);
v_lctx_459_ = lean_ctor_get(v___y_365_, 2);
v_localInstances_460_ = lean_ctor_get(v___y_365_, 3);
v_defEqCtx_x3f_461_ = lean_ctor_get(v___y_365_, 4);
v_synthPendingDepth_462_ = lean_ctor_get(v___y_365_, 5);
v_customCanUnfoldPredicate_x3f_463_ = lean_ctor_get(v___y_365_, 6);
v_univApprox_464_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_465_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7 + 2);
v_cacheInferType_466_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7 + 3);
if (v_isShared_456_ == 0)
{
v___x_468_ = v___x_455_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 0, v_foApprox_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 1, v_ctxApprox_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 2, v_quasiPatternApprox_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 3, v_constApprox_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 4, v_isDefEqStuckEx_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 5, v_unificationHints_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 6, v_proofIrrelevance_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 8, v_offsetCnstrs_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 9, v_transparency_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 10, v_etaStruct_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 11, v_univApprox_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 12, v_iota_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 13, v_beta_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 14, v_proj_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 15, v_zeta_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 16, v_zetaDelta_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 17, v_zetaUnused_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 18, v_zetaHave_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, 19, v_canUnfoldPredicateConfig_453_);
v___x_468_ = v_reuseFailAlloc_483_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
uint64_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_ctor_set_uint8(v___x_468_, 7, v___x_360_);
v___x_469_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set_uint64(v___x_470_, sizeof(void*)*1, v___x_469_);
lean_inc(v_customCanUnfoldPredicate_x3f_463_);
lean_inc(v_synthPendingDepth_462_);
lean_inc(v_defEqCtx_x3f_461_);
lean_inc_ref(v_localInstances_460_);
lean_inc_ref(v_lctx_459_);
lean_inc(v_zetaDeltaSet_458_);
v___x_471_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_zetaDeltaSet_458_);
lean_ctor_set(v___x_471_, 2, v_lctx_459_);
lean_ctor_set(v___x_471_, 3, v_localInstances_460_);
lean_ctor_set(v___x_471_, 4, v_defEqCtx_x3f_461_);
lean_ctor_set(v___x_471_, 5, v_synthPendingDepth_462_);
lean_ctor_set(v___x_471_, 6, v_customCanUnfoldPredicate_x3f_463_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*7, v_trackZetaDelta_457_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*7 + 1, v_univApprox_464_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*7 + 2, v_inTypeClassResolution_465_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*7 + 3, v_cacheInferType_466_);
lean_inc(v_a_414_);
lean_inc(v_a_371_);
v___x_472_ = l_Lean_Meta_isExprDefEq(v_a_371_, v_a_414_, v___x_471_, v___y_366_, v___y_367_, v___y_368_);
lean_dec_ref_known(v___x_471_, 7);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; uint8_t v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = lean_unbox(v_a_473_);
lean_dec(v_a_473_);
v_____do__lift_416_ = v___x_474_;
v___y_417_ = v___y_361_;
v___y_418_ = v___y_362_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
v___y_421_ = v___y_365_;
v___y_422_ = v___y_366_;
v___y_423_ = v___y_367_;
v___y_424_ = v___y_368_;
goto v___jp_415_;
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_a_414_);
lean_del_object(v___x_411_);
lean_dec(v_a_375_);
lean_dec(v_a_371_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___x_358_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_351_);
v_a_475_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_472_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_472_);
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
}
else
{
lean_object* v_keyedConfig_485_; uint8_t v_trackZetaDelta_486_; lean_object* v_zetaDeltaSet_487_; lean_object* v_lctx_488_; lean_object* v_localInstances_489_; lean_object* v_defEqCtx_x3f_490_; lean_object* v_synthPendingDepth_491_; lean_object* v_customCanUnfoldPredicate_x3f_492_; uint8_t v_univApprox_493_; uint8_t v_inTypeClassResolution_494_; uint8_t v_cacheInferType_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v_foApprox_500_; uint8_t v_ctxApprox_501_; uint8_t v_quasiPatternApprox_502_; uint8_t v_constApprox_503_; uint8_t v_isDefEqStuckEx_504_; uint8_t v_unificationHints_505_; uint8_t v_proofIrrelevance_506_; uint8_t v_offsetCnstrs_507_; uint8_t v_transparency_508_; uint8_t v_etaStruct_509_; uint8_t v_univApprox_510_; uint8_t v_iota_511_; uint8_t v_beta_512_; uint8_t v_proj_513_; uint8_t v_zeta_514_; uint8_t v_zetaDelta_515_; uint8_t v_zetaUnused_516_; uint8_t v_zetaHave_517_; uint8_t v_canUnfoldPredicateConfig_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_541_; 
v_keyedConfig_485_ = lean_ctor_get(v___y_365_, 0);
v_trackZetaDelta_486_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7);
v_zetaDeltaSet_487_ = lean_ctor_get(v___y_365_, 1);
v_lctx_488_ = lean_ctor_get(v___y_365_, 2);
v_localInstances_489_ = lean_ctor_get(v___y_365_, 3);
v_defEqCtx_x3f_490_ = lean_ctor_get(v___y_365_, 4);
v_synthPendingDepth_491_ = lean_ctor_get(v___y_365_, 5);
v_customCanUnfoldPredicate_x3f_492_ = lean_ctor_get(v___y_365_, 6);
v_univApprox_493_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_494_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7 + 2);
v_cacheInferType_495_ = lean_ctor_get_uint8(v___y_365_, sizeof(void*)*7 + 3);
v___x_496_ = 2;
lean_inc_ref(v_keyedConfig_485_);
v___x_497_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_496_, v_keyedConfig_485_);
lean_inc(v_customCanUnfoldPredicate_x3f_492_);
lean_inc(v_synthPendingDepth_491_);
lean_inc(v_defEqCtx_x3f_490_);
lean_inc_ref(v_localInstances_489_);
lean_inc_ref(v_lctx_488_);
lean_inc(v_zetaDeltaSet_487_);
v___x_498_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_zetaDeltaSet_487_);
lean_ctor_set(v___x_498_, 2, v_lctx_488_);
lean_ctor_set(v___x_498_, 3, v_localInstances_489_);
lean_ctor_set(v___x_498_, 4, v_defEqCtx_x3f_490_);
lean_ctor_set(v___x_498_, 5, v_synthPendingDepth_491_);
lean_ctor_set(v___x_498_, 6, v_customCanUnfoldPredicate_x3f_492_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*7, v_trackZetaDelta_486_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*7 + 1, v_univApprox_493_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*7 + 2, v_inTypeClassResolution_494_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*7 + 3, v_cacheInferType_495_);
v___x_499_ = l_Lean_Meta_Context_config(v___x_498_);
lean_dec_ref_known(v___x_498_, 7);
v_foApprox_500_ = lean_ctor_get_uint8(v___x_499_, 0);
v_ctxApprox_501_ = lean_ctor_get_uint8(v___x_499_, 1);
v_quasiPatternApprox_502_ = lean_ctor_get_uint8(v___x_499_, 2);
v_constApprox_503_ = lean_ctor_get_uint8(v___x_499_, 3);
v_isDefEqStuckEx_504_ = lean_ctor_get_uint8(v___x_499_, 4);
v_unificationHints_505_ = lean_ctor_get_uint8(v___x_499_, 5);
v_proofIrrelevance_506_ = lean_ctor_get_uint8(v___x_499_, 6);
v_offsetCnstrs_507_ = lean_ctor_get_uint8(v___x_499_, 8);
v_transparency_508_ = lean_ctor_get_uint8(v___x_499_, 9);
v_etaStruct_509_ = lean_ctor_get_uint8(v___x_499_, 10);
v_univApprox_510_ = lean_ctor_get_uint8(v___x_499_, 11);
v_iota_511_ = lean_ctor_get_uint8(v___x_499_, 12);
v_beta_512_ = lean_ctor_get_uint8(v___x_499_, 13);
v_proj_513_ = lean_ctor_get_uint8(v___x_499_, 14);
v_zeta_514_ = lean_ctor_get_uint8(v___x_499_, 15);
v_zetaDelta_515_ = lean_ctor_get_uint8(v___x_499_, 16);
v_zetaUnused_516_ = lean_ctor_get_uint8(v___x_499_, 17);
v_zetaHave_517_ = lean_ctor_get_uint8(v___x_499_, 18);
v_canUnfoldPredicateConfig_518_ = lean_ctor_get_uint8(v___x_499_, 19);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_541_ == 0)
{
v___x_520_ = v___x_499_;
v_isShared_521_ = v_isSharedCheck_541_;
goto v_resetjp_519_;
}
else
{
lean_dec(v___x_499_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_541_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 0, v_foApprox_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 1, v_ctxApprox_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 2, v_quasiPatternApprox_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 3, v_constApprox_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 4, v_isDefEqStuckEx_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 5, v_unificationHints_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 6, v_proofIrrelevance_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 8, v_offsetCnstrs_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 9, v_transparency_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 10, v_etaStruct_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 11, v_univApprox_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 12, v_iota_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 13, v_beta_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 14, v_proj_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 15, v_zeta_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 16, v_zetaDelta_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 17, v_zetaUnused_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 18, v_zetaHave_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_540_, 19, v_canUnfoldPredicateConfig_518_);
v___x_523_ = v_reuseFailAlloc_540_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
uint64_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_ctor_set_uint8(v___x_523_, 7, v___x_360_);
v___x_524_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set_uint64(v___x_525_, sizeof(void*)*1, v___x_524_);
lean_inc(v_customCanUnfoldPredicate_x3f_492_);
lean_inc(v_synthPendingDepth_491_);
lean_inc(v_defEqCtx_x3f_490_);
lean_inc_ref(v_localInstances_489_);
lean_inc_ref(v_lctx_488_);
lean_inc(v_zetaDeltaSet_487_);
v___x_526_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v_zetaDeltaSet_487_);
lean_ctor_set(v___x_526_, 2, v_lctx_488_);
lean_ctor_set(v___x_526_, 3, v_localInstances_489_);
lean_ctor_set(v___x_526_, 4, v_defEqCtx_x3f_490_);
lean_ctor_set(v___x_526_, 5, v_synthPendingDepth_491_);
lean_ctor_set(v___x_526_, 6, v_customCanUnfoldPredicate_x3f_492_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*7, v_trackZetaDelta_486_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*7 + 1, v_univApprox_493_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*7 + 2, v_inTypeClassResolution_494_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*7 + 3, v_cacheInferType_495_);
lean_inc(v_a_414_);
lean_inc(v_a_371_);
v___x_527_ = l_Lean_Meta_isExprDefEq(v_a_371_, v_a_414_, v___x_526_, v___y_366_, v___y_367_, v___y_368_);
lean_dec_ref_known(v___x_526_, 7);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; uint8_t v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = lean_unbox(v_a_528_);
lean_dec(v_a_528_);
v_____do__lift_416_ = v___x_529_;
v___y_417_ = v___y_361_;
v___y_418_ = v___y_362_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
v___y_421_ = v___y_365_;
v___y_422_ = v___y_366_;
v___y_423_ = v___y_367_;
v___y_424_ = v___y_368_;
goto v___jp_415_;
}
else
{
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_530_; uint8_t v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_527_, 1);
v___x_531_ = lean_unbox(v_a_530_);
lean_dec(v_a_530_);
v_____do__lift_416_ = v___x_531_;
v___y_417_ = v___y_361_;
v___y_418_ = v___y_362_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
v___y_421_ = v___y_365_;
v___y_422_ = v___y_366_;
v___y_423_ = v___y_367_;
v___y_424_ = v___y_368_;
goto v___jp_415_;
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_414_);
lean_del_object(v___x_411_);
lean_dec(v_a_375_);
lean_dec(v_a_371_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___x_358_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_351_);
v_a_532_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_527_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_527_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
v___jp_415_:
{
if (v_____do__lift_416_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_425_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1);
lean_inc_ref(v_a_355_);
v___x_426_ = l_Lean_indentExpr(v_a_355_);
v___x_427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 1);
lean_ctor_set(v___x_411_, 0, v___x_429_);
v___x_431_ = v___x_411_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
lean_inc(v_a_375_);
v___x_432_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_431_, v_a_371_, v_a_414_, v_a_375_, v___x_358_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec_ref(v___x_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_dec_ref_known(v___x_432_, 1);
v___y_377_ = v___y_417_;
v___y_378_ = v___y_418_;
v___y_379_ = v___y_419_;
v___y_380_ = v___y_420_;
v___y_381_ = v___y_421_;
v___y_382_ = v___y_422_;
v___y_383_ = v___y_423_;
v___y_384_ = v___y_424_;
goto v___jp_376_;
}
else
{
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v_a_375_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_351_);
return v___x_432_;
}
}
}
else
{
lean_dec(v_a_414_);
lean_del_object(v___x_411_);
lean_dec(v_a_371_);
lean_dec(v___x_358_);
v___y_377_ = v___y_417_;
v___y_378_ = v___y_418_;
v___y_379_ = v___y_419_;
v___y_380_ = v___y_420_;
v___y_381_ = v___y_421_;
v___y_382_ = v___y_422_;
v___y_383_ = v___y_423_;
v___y_384_ = v___y_424_;
goto v___jp_376_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_del_object(v___x_411_);
lean_dec(v_a_375_);
lean_dec(v_a_371_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___x_358_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_351_);
v_a_542_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_413_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_413_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_dec(v_a_375_);
lean_dec(v_a_371_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___x_358_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_351_);
return v___x_409_;
}
v___jp_376_:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_getMVars(v_a_355_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_386_, v_mvarCounter_356_, v___y_382_);
lean_dec(v_a_386_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_388_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v_a_388_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_390_; 
lean_dec_ref_known(v___x_389_, 1);
v___x_390_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_351_, v___y_378_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec_ref_known(v___x_390_, 1);
v___x_391_ = l_Lean_Name_mkStr1(v___x_357_);
v___x_392_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_391_, v_a_375_, v___x_354_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v___x_392_;
}
else
{
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v_a_375_);
lean_dec_ref(v___x_357_);
return v___x_390_;
}
}
else
{
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v_a_375_);
lean_dec_ref(v___x_357_);
lean_dec(v_a_351_);
return v___x_389_;
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v_a_375_);
lean_dec_ref(v___x_357_);
lean_dec(v_a_351_);
v_a_393_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_387_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_387_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v_a_375_);
lean_dec_ref(v___x_357_);
lean_dec(v_a_351_);
v_a_401_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_385_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_385_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_a_371_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___x_358_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_351_);
v_a_552_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_374_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_374_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___x_358_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_352_);
lean_dec(v_a_351_);
v_a_560_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_370_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_370_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object** _args){
lean_object* v_a_568_ = _args[0];
lean_object* v_a_569_ = _args[1];
lean_object* v___x_570_ = _args[2];
lean_object* v___x_571_ = _args[3];
lean_object* v_a_572_ = _args[4];
lean_object* v_mvarCounter_573_ = _args[5];
lean_object* v___x_574_ = _args[6];
lean_object* v___x_575_ = _args[7];
lean_object* v_useReducible_576_ = _args[8];
lean_object* v___x_577_ = _args[9];
lean_object* v___y_578_ = _args[10];
lean_object* v___y_579_ = _args[11];
lean_object* v___y_580_ = _args[12];
lean_object* v___y_581_ = _args[13];
lean_object* v___y_582_ = _args[14];
lean_object* v___y_583_ = _args[15];
lean_object* v___y_584_ = _args[16];
lean_object* v___y_585_ = _args[17];
lean_object* v___y_586_ = _args[18];
_start:
{
uint8_t v___x_93096__boxed_587_; uint8_t v___x_93097__boxed_588_; uint8_t v_useReducible_boxed_589_; uint8_t v___x_93101__boxed_590_; lean_object* v_res_591_; 
v___x_93096__boxed_587_ = lean_unbox(v___x_570_);
v___x_93097__boxed_588_ = lean_unbox(v___x_571_);
v_useReducible_boxed_589_ = lean_unbox(v_useReducible_576_);
v___x_93101__boxed_590_ = lean_unbox(v___x_577_);
v_res_591_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_568_, v_a_569_, v___x_93096__boxed_587_, v___x_93097__boxed_588_, v_a_572_, v_mvarCounter_573_, v___x_574_, v___x_575_, v_useReducible_boxed_589_, v___x_93101__boxed_590_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v_mvarCounter_573_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; lean_object* v_infoState_603_; lean_object* v_env_604_; lean_object* v_nextMacroScope_605_; lean_object* v_ngen_606_; lean_object* v_auxDeclNGen_607_; lean_object* v_traceState_608_; lean_object* v_cache_609_; lean_object* v_messages_610_; lean_object* v_snapshotTasks_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_632_; 
v___x_602_ = lean_st_ref_take(v___y_600_);
v_infoState_603_ = lean_ctor_get(v___x_602_, 7);
v_env_604_ = lean_ctor_get(v___x_602_, 0);
v_nextMacroScope_605_ = lean_ctor_get(v___x_602_, 1);
v_ngen_606_ = lean_ctor_get(v___x_602_, 2);
v_auxDeclNGen_607_ = lean_ctor_get(v___x_602_, 3);
v_traceState_608_ = lean_ctor_get(v___x_602_, 4);
v_cache_609_ = lean_ctor_get(v___x_602_, 5);
v_messages_610_ = lean_ctor_get(v___x_602_, 6);
v_snapshotTasks_611_ = lean_ctor_get(v___x_602_, 8);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_632_ == 0)
{
v___x_613_ = v___x_602_;
v_isShared_614_ = v_isSharedCheck_632_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_snapshotTasks_611_);
lean_inc(v_infoState_603_);
lean_inc(v_messages_610_);
lean_inc(v_cache_609_);
lean_inc(v_traceState_608_);
lean_inc(v_auxDeclNGen_607_);
lean_inc(v_ngen_606_);
lean_inc(v_nextMacroScope_605_);
lean_inc(v_env_604_);
lean_dec(v___x_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_632_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v_enabled_615_; lean_object* v_assignment_616_; lean_object* v_lazyAssignment_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_630_; 
v_enabled_615_ = lean_ctor_get_uint8(v_infoState_603_, sizeof(void*)*3);
v_assignment_616_ = lean_ctor_get(v_infoState_603_, 0);
v_lazyAssignment_617_ = lean_ctor_get(v_infoState_603_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_infoState_603_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_infoState_603_, 2);
lean_dec(v_unused_631_);
v___x_619_ = v_infoState_603_;
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_lazyAssignment_617_);
lean_inc(v_assignment_616_);
lean_dec(v_infoState_603_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_630_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 2, v_a_592_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_assignment_616_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_lazyAssignment_617_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_a_592_);
lean_ctor_set_uint8(v_reuseFailAlloc_629_, sizeof(void*)*3, v_enabled_615_);
v___x_622_ = v_reuseFailAlloc_629_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 7, v___x_622_);
v___x_624_ = v___x_613_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_env_604_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_nextMacroScope_605_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_ngen_606_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v_auxDeclNGen_607_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v_traceState_608_);
lean_ctor_set(v_reuseFailAlloc_628_, 5, v_cache_609_);
lean_ctor_set(v_reuseFailAlloc_628_, 6, v_messages_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 7, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_628_, 8, v_snapshotTasks_611_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_st_ref_put(v___y_600_, v___x_624_);
v___x_626_ = lean_box(0);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object* v_a_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_m_644_, lean_object* v_query_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v_zero_649_; uint8_t v_isZero_650_; 
v_zero_649_ = lean_unsigned_to_nat(0u);
v_isZero_650_ = lean_nat_dec_eq(v_x_647_, v_zero_649_);
if (v_isZero_650_ == 1)
{
lean_dec(v_x_648_);
lean_dec(v_x_647_);
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_box(2);
return v___x_651_;
}
else
{
lean_object* v_val_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_val_652_ = lean_ctor_get(v_x_646_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v_x_646_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_val_652_);
lean_dec(v_x_646_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_val_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_keyArray_660_; lean_object* v_valueArray_661_; lean_object* v___x_662_; uint8_t v_isSome_663_; 
v_keyArray_660_ = lean_ctor_get(v_m_644_, 1);
v_valueArray_661_ = lean_ctor_get(v_m_644_, 2);
v___x_662_ = lean_array_fget_borrowed(v_keyArray_660_, v_x_648_);
v_isSome_663_ = lean_noption_is_some(v___x_662_);
if (v_isSome_663_ == 0)
{
lean_dec(v_x_647_);
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v_x_648_);
return v___x_664_;
}
else
{
lean_object* v_val_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_x_648_);
v_val_665_ = lean_ctor_get(v_x_646_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v_x_646_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_val_665_);
lean_dec(v_x_646_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_val_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_one_673_; lean_object* v_n_674_; lean_object* v___y_676_; 
v_one_673_ = lean_unsigned_to_nat(1u);
v_n_674_ = lean_nat_sub(v_x_647_, v_one_673_);
lean_dec(v_x_647_);
if (v_isSome_663_ == 0)
{
goto v___jp_682_;
}
else
{
lean_object* v___x_684_; uint8_t v_isSome_685_; 
v___x_684_ = lean_array_fget_borrowed(v_valueArray_661_, v_x_648_);
v_isSome_685_ = lean_noption_is_some(v___x_684_);
if (v_isSome_685_ == 0)
{
goto v___jp_682_;
}
else
{
lean_object* v_val_686_; uint8_t v___x_687_; 
lean_inc(v___x_662_);
v_val_686_ = lean_noption_get(v___x_662_);
v___x_687_ = lean_expr_eqv(v_val_686_, v_query_645_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
lean_dec(v_val_686_);
v___x_688_ = lean_array_get_size(v_keyArray_660_);
v___x_689_ = lean_nat_add(v_x_648_, v_one_673_);
lean_dec(v_x_648_);
v___x_690_ = lean_nat_dec_lt(v___x_689_, v___x_688_);
if (v___x_690_ == 0)
{
lean_dec(v___x_689_);
v_x_647_ = v_n_674_;
v_x_648_ = v_zero_649_;
goto _start;
}
else
{
v_x_647_ = v_n_674_;
v_x_648_ = v___x_689_;
goto _start;
}
}
else
{
lean_object* v_val_693_; lean_object* v___x_694_; 
lean_dec(v_n_674_);
lean_dec(v_x_646_);
lean_inc(v___x_684_);
v_val_693_ = lean_noption_get(v___x_684_);
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v_x_648_);
lean_ctor_set(v___x_694_, 1, v_val_686_);
lean_ctor_set(v___x_694_, 2, v_val_693_);
return v___x_694_;
}
}
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_677_ = lean_array_get_size(v_keyArray_660_);
v___x_678_ = lean_nat_add(v_x_648_, v_one_673_);
lean_dec(v_x_648_);
v___x_679_ = lean_nat_dec_lt(v___x_678_, v___x_677_);
if (v___x_679_ == 0)
{
lean_dec(v___x_678_);
v_x_646_ = v___y_676_;
v_x_647_ = v_n_674_;
v_x_648_ = v_zero_649_;
goto _start;
}
else
{
v_x_646_ = v___y_676_;
v_x_647_ = v_n_674_;
v_x_648_ = v___x_678_;
goto _start;
}
}
v___jp_682_:
{
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v___x_683_; 
lean_inc(v_x_648_);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v_x_648_);
v___y_676_ = v___x_683_;
goto v___jp_675_;
}
else
{
v___y_676_ = v_x_646_;
goto v___jp_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_m_695_, lean_object* v_query_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_m_695_, v_query_696_, v_x_697_, v_x_698_, v_x_699_);
lean_dec_ref(v_query_696_);
lean_dec_ref(v_m_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(lean_object* v_m_701_, lean_object* v_query_702_){
_start:
{
lean_object* v_keyArray_703_; lean_object* v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v_fold_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_keyArray_703_ = lean_ctor_get(v_m_701_, 1);
v___x_704_ = lean_array_get_size(v_keyArray_703_);
v___x_705_ = l_Lean_Expr_hash(v_query_702_);
v___x_706_ = 32ULL;
v___x_707_ = lean_uint64_shift_right(v___x_705_, v___x_706_);
v_fold_708_ = lean_uint64_xor(v___x_705_, v___x_707_);
v___x_709_ = 16ULL;
v___x_710_ = lean_uint64_shift_right(v_fold_708_, v___x_709_);
v___x_711_ = lean_uint64_xor(v_fold_708_, v___x_710_);
v___x_712_ = lean_uint64_to_usize(v___x_711_);
v___x_713_ = lean_usize_of_nat(v___x_704_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_sub(v___x_713_, v___x_714_);
v___x_716_ = lean_usize_land(v___x_712_, v___x_715_);
v___x_717_ = lean_usize_to_nat(v___x_716_);
v___x_718_ = lean_box(0);
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_m_701_, v_query_702_, v___x_718_, v___x_704_, v___x_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_m_720_, lean_object* v_query_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(v_m_720_, v_query_721_);
lean_dec_ref(v_query_721_);
lean_dec_ref(v_m_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___redArg(lean_object* v_b_723_, lean_object* v_acc_724_, lean_object* v_i_725_){
_start:
{
lean_object* v___y_727_; lean_object* v_keyArray_735_; lean_object* v_valueArray_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_keyArray_735_ = lean_ctor_get(v_b_723_, 1);
v_valueArray_736_ = lean_ctor_get(v_b_723_, 2);
v___x_737_ = lean_array_get_size(v_keyArray_735_);
v___x_738_ = lean_nat_dec_lt(v_i_725_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec(v_i_725_);
return v_acc_724_;
}
else
{
lean_object* v___x_739_; uint8_t v_isSome_740_; 
v___x_739_ = lean_array_fget_borrowed(v_keyArray_735_, v_i_725_);
v_isSome_740_ = lean_noption_is_some(v___x_739_);
if (v_isSome_740_ == 0)
{
goto v___jp_731_;
}
else
{
lean_object* v___x_741_; uint8_t v_isSome_742_; 
v___x_741_ = lean_array_fget_borrowed(v_valueArray_736_, v_i_725_);
v_isSome_742_ = lean_noption_is_some(v___x_741_);
if (v_isSome_742_ == 0)
{
goto v___jp_731_;
}
else
{
lean_object* v_val_743_; lean_object* v_val_744_; lean_object* v_i_746_; lean_object* v___x_751_; 
lean_inc(v___x_739_);
v_val_743_ = lean_noption_get(v___x_739_);
lean_inc(v___x_741_);
v_val_744_ = lean_noption_get(v___x_741_);
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(v_acc_724_, v_val_743_);
switch(lean_obj_tag(v___x_751_))
{
case 0:
{
lean_object* v_index_752_; lean_object* v_size_753_; lean_object* v___x_754_; 
v_index_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_index_752_);
lean_dec_ref_known(v___x_751_, 3);
v_size_753_ = lean_ctor_get(v_acc_724_, 0);
lean_inc(v_size_753_);
v___x_754_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_724_, v_size_753_, v_index_752_, v_val_743_, v_val_744_);
lean_dec(v_index_752_);
v___y_727_ = v___x_754_;
goto v___jp_726_;
}
case 1:
{
lean_object* v_index_755_; 
v_index_755_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_index_755_);
lean_dec_ref_known(v___x_751_, 1);
v_i_746_ = v_index_755_;
goto v___jp_745_;
}
default: 
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_724_, v___x_756_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_index_758_; 
v_index_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_index_758_);
lean_dec_ref_known(v___x_757_, 1);
v_i_746_ = v_index_758_;
goto v___jp_745_;
}
else
{
lean_dec(v_val_744_);
lean_dec(v_val_743_);
v___y_727_ = v_acc_724_;
goto v___jp_726_;
}
}
}
v___jp_745_:
{
lean_object* v_size_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_size_747_ = lean_ctor_get(v_acc_724_, 0);
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_size_747_, v___x_748_);
v___x_750_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_724_, v___x_749_, v_i_746_, v_val_743_, v_val_744_);
lean_dec(v_i_746_);
v___y_727_ = v___x_750_;
goto v___jp_726_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_i_725_, v___x_728_);
lean_dec(v_i_725_);
v_acc_724_ = v___y_727_;
v_i_725_ = v___x_729_;
goto _start;
}
v___jp_731_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_i_725_, v___x_732_);
lean_dec(v_i_725_);
v_i_725_ = v___x_733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___redArg___boxed(lean_object* v_b_759_, lean_object* v_acc_760_, lean_object* v_i_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___redArg(v_b_759_, v_acc_760_, v_i_761_);
lean_dec_ref(v_b_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___redArg(lean_object* v_init_763_, lean_object* v_b_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___redArg(v_b_764_, v_init_763_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___redArg___boxed(lean_object* v_init_767_, lean_object* v_b_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___redArg(v_init_767_, v_b_768_);
lean_dec_ref(v_b_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg(lean_object* v_m_770_){
_start:
{
lean_object* v_keyArray_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_cellCount_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_target_778_; lean_object* v___x_779_; 
v_keyArray_771_ = lean_ctor_get(v_m_770_, 1);
v___x_772_ = lean_array_get_size(v_keyArray_771_);
v___x_773_ = lean_unsigned_to_nat(2u);
v_cellCount_774_ = lean_nat_mul(v___x_772_, v___x_773_);
v___x_775_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_774_);
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_774_);
v___x_777_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_774_);
v_target_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_778_, 0, v___x_775_);
lean_ctor_set(v_target_778_, 1, v___x_776_);
lean_ctor_set(v_target_778_, 2, v___x_777_);
v___x_779_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___redArg(v_target_778_, v_m_770_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_m_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg(v_m_780_);
lean_dec_ref(v_m_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_mvarId_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v_mctx_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_786_ = lean_st_ref_get(v___y_784_);
v_mctx_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_mctx_787_);
lean_dec(v___x_786_);
v___x_788_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_787_, v_mvarId_782_);
lean_dec_ref(v_mctx_787_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___y_783_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg___boxed(lean_object* v_mvarId_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec(v_mvarId_792_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___redArg(lean_object* v_mvarId_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_mctx_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_801_ = lean_st_ref_get(v___y_799_);
v_mctx_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc_ref(v_mctx_802_);
lean_dec(v___x_801_);
v___x_803_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_802_, v_mvarId_797_);
lean_dec_ref(v_mctx_802_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___y_798_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___redArg___boxed(lean_object* v_mvarId_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___redArg(v_mvarId_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec(v_mvarId_807_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_m_812_, lean_object* v_query_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(v_m_812_, v_query_813_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_index_815_; lean_object* v_key_816_; lean_object* v_value_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
v_index_815_ = lean_ctor_get(v___x_814_, 0);
v_key_816_ = lean_ctor_get(v___x_814_, 1);
v_value_817_ = lean_ctor_get(v___x_814_, 2);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_814_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_value_817_);
lean_inc(v_key_816_);
lean_inc(v_index_815_);
lean_dec(v___x_814_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_index_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_key_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_value_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
else
{
lean_object* v___x_825_; 
lean_dec(v___x_814_);
v___x_825_ = lean_box(1);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_m_826_, lean_object* v_query_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_m_826_, v_query_827_);
lean_dec_ref(v_query_827_);
lean_dec_ref(v_m_826_);
return v_res_828_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_m_829_, v_a_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
uint8_t v___x_832_; 
lean_dec_ref_known(v___x_831_, 3);
v___x_832_ = 1;
return v___x_832_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = 0;
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_834_, lean_object* v_a_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_834_, v_a_835_);
lean_dec_ref(v_a_835_);
lean_dec_ref(v_m_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_842_, lean_object* v_e_843_, lean_object* v_a_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_d_855_; lean_object* v_b_856_; lean_object* v___y_857_; uint8_t v___x_863_; 
v___x_863_ = l_Lean_Expr_hasExprMVar(v_e_843_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v_e_843_);
v___x_864_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v_a_844_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
else
{
uint8_t v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_844_, v_e_843_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___y_870_; lean_object* v___y_904_; lean_object* v_i_905_; lean_object* v___y_911_; lean_object* v___y_921_; lean_object* v_i_922_; lean_object* v___x_937_; 
v___x_868_ = lean_box(0);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(v_a_844_, v_e_843_);
switch(lean_obj_tag(v___x_937_))
{
case 0:
{
lean_dec_ref_known(v___x_937_, 3);
v___y_870_ = v_a_844_;
goto v___jp_869_;
}
case 1:
{
lean_object* v_index_938_; lean_object* v_size_939_; lean_object* v_keyArray_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_index_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_index_938_);
lean_dec_ref_known(v___x_937_, 1);
v_size_939_ = lean_ctor_get(v_a_844_, 0);
v_keyArray_940_ = lean_ctor_get(v_a_844_, 1);
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_nat_add(v_size_939_, v___x_941_);
v___x_943_ = lean_array_get_size(v_keyArray_940_);
v___x_944_ = lean_nat_dec_lt(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec(v___x_942_);
lean_dec(v_index_938_);
goto v___jp_927_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_945_ = lean_unsigned_to_nat(4u);
v___x_946_ = lean_nat_mul(v___x_942_, v___x_945_);
v___x_947_ = lean_unsigned_to_nat(3u);
v___x_948_ = lean_nat_mul(v___x_943_, v___x_947_);
v___x_949_ = lean_nat_dec_le(v___x_946_, v___x_948_);
lean_dec(v___x_948_);
lean_dec(v___x_946_);
if (v___x_949_ == 0)
{
lean_dec(v___x_942_);
lean_dec(v_index_938_);
goto v___jp_927_;
}
else
{
lean_object* v___x_950_; 
lean_inc_ref(v_e_843_);
v___x_950_ = l_Std_DHashMap_Raw_setEntry___redArg(v_a_844_, v___x_942_, v_index_938_, v_e_843_, v___x_868_);
lean_dec(v_index_938_);
v___y_870_ = v___x_950_;
goto v___jp_869_;
}
}
}
default: 
{
lean_object* v_size_951_; lean_object* v_keyArray_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_size_951_ = lean_ctor_get(v_a_844_, 0);
v_keyArray_952_ = lean_ctor_get(v_a_844_, 1);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_size_951_, v___x_953_);
v___x_955_ = lean_array_get_size(v_keyArray_952_);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_dec(v___x_954_);
v___x_957_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg(v_a_844_);
lean_dec_ref(v_a_844_);
v___y_911_ = v___x_957_;
goto v___jp_910_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_958_ = lean_unsigned_to_nat(4u);
v___x_959_ = lean_nat_mul(v___x_954_, v___x_958_);
lean_dec(v___x_954_);
v___x_960_ = lean_unsigned_to_nat(3u);
v___x_961_ = lean_nat_mul(v___x_955_, v___x_960_);
v___x_962_ = lean_nat_dec_le(v___x_959_, v___x_961_);
lean_dec(v___x_961_);
lean_dec(v___x_959_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg(v_a_844_);
lean_dec_ref(v_a_844_);
v___y_911_ = v___x_963_;
goto v___jp_910_;
}
else
{
v___y_911_ = v_a_844_;
goto v___jp_910_;
}
}
}
}
v___jp_869_:
{
switch(lean_obj_tag(v_e_843_))
{
case 11:
{
lean_object* v_struct_871_; 
v_struct_871_ = lean_ctor_get(v_e_843_, 2);
lean_inc_ref(v_struct_871_);
lean_dec_ref_known(v_e_843_, 3);
v_e_843_ = v_struct_871_;
v_a_844_ = v___y_870_;
goto _start;
}
case 7:
{
lean_object* v_binderType_873_; lean_object* v_body_874_; 
v_binderType_873_ = lean_ctor_get(v_e_843_, 1);
lean_inc_ref(v_binderType_873_);
v_body_874_ = lean_ctor_get(v_e_843_, 2);
lean_inc_ref(v_body_874_);
lean_dec_ref_known(v_e_843_, 3);
v_d_855_ = v_binderType_873_;
v_b_856_ = v_body_874_;
v___y_857_ = v___y_870_;
goto v___jp_854_;
}
case 6:
{
lean_object* v_binderType_875_; lean_object* v_body_876_; 
v_binderType_875_ = lean_ctor_get(v_e_843_, 1);
lean_inc_ref(v_binderType_875_);
v_body_876_ = lean_ctor_get(v_e_843_, 2);
lean_inc_ref(v_body_876_);
lean_dec_ref_known(v_e_843_, 3);
v_d_855_ = v_binderType_875_;
v_b_856_ = v_body_876_;
v___y_857_ = v___y_870_;
goto v___jp_854_;
}
case 8:
{
lean_object* v_type_877_; lean_object* v_value_878_; lean_object* v_body_879_; lean_object* v___x_880_; 
v_type_877_ = lean_ctor_get(v_e_843_, 1);
lean_inc_ref(v_type_877_);
v_value_878_ = lean_ctor_get(v_e_843_, 2);
lean_inc_ref(v_value_878_);
v_body_879_ = lean_ctor_get(v_e_843_, 3);
lean_inc_ref(v_body_879_);
lean_dec_ref_known(v_e_843_, 4);
v___x_880_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_842_, v_type_877_, v___y_870_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v_fst_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
v_fst_882_ = lean_ctor_get(v_a_881_, 0);
if (lean_obj_tag(v_fst_882_) == 0)
{
lean_dec(v_a_881_);
lean_dec_ref(v_body_879_);
lean_dec_ref(v_value_878_);
return v___x_880_;
}
else
{
lean_object* v_snd_883_; lean_object* v___x_884_; 
lean_dec_ref_known(v___x_880_, 1);
v_snd_883_ = lean_ctor_get(v_a_881_, 1);
lean_inc(v_snd_883_);
lean_dec(v_a_881_);
v___x_884_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_842_, v_value_878_, v_snd_883_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v_fst_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
v_fst_886_ = lean_ctor_get(v_a_885_, 0);
if (lean_obj_tag(v_fst_886_) == 0)
{
lean_dec(v_a_885_);
lean_dec_ref(v_body_879_);
return v___x_884_;
}
else
{
lean_object* v_snd_887_; 
lean_dec_ref_known(v___x_884_, 1);
v_snd_887_ = lean_ctor_get(v_a_885_, 1);
lean_inc(v_snd_887_);
lean_dec(v_a_885_);
v_e_843_ = v_body_879_;
v_a_844_ = v_snd_887_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_879_);
return v___x_884_;
}
}
}
else
{
lean_dec_ref(v_body_879_);
lean_dec_ref(v_value_878_);
return v___x_880_;
}
}
case 10:
{
lean_object* v_expr_889_; 
v_expr_889_ = lean_ctor_get(v_e_843_, 1);
lean_inc_ref(v_expr_889_);
lean_dec_ref_known(v_e_843_, 2);
v_e_843_ = v_expr_889_;
v_a_844_ = v___y_870_;
goto _start;
}
case 5:
{
lean_object* v_fn_891_; lean_object* v_arg_892_; lean_object* v___x_893_; 
v_fn_891_ = lean_ctor_get(v_e_843_, 0);
lean_inc_ref(v_fn_891_);
v_arg_892_ = lean_ctor_get(v_e_843_, 1);
lean_inc_ref(v_arg_892_);
lean_dec_ref_known(v_e_843_, 2);
v___x_893_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_842_, v_fn_891_, v___y_870_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_fst_895_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
v_fst_895_ = lean_ctor_get(v_a_894_, 0);
if (lean_obj_tag(v_fst_895_) == 0)
{
lean_dec(v_a_894_);
lean_dec_ref(v_arg_892_);
return v___x_893_;
}
else
{
lean_object* v_snd_896_; 
lean_dec_ref_known(v___x_893_, 1);
v_snd_896_ = lean_ctor_get(v_a_894_, 1);
lean_inc(v_snd_896_);
lean_dec(v_a_894_);
v_e_843_ = v_arg_892_;
v_a_844_ = v_snd_896_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_892_);
return v___x_893_;
}
}
case 2:
{
lean_object* v_mvarId_898_; lean_object* v___x_899_; 
v_mvarId_898_ = lean_ctor_get(v_e_843_, 0);
lean_inc(v_mvarId_898_);
lean_dec_ref_known(v_e_843_, 1);
v___x_899_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_842_, v_mvarId_898_, v___y_870_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_899_;
}
default: 
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec_ref(v_e_843_);
v___x_900_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___y_870_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
}
v___jp_903_:
{
lean_object* v_size_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_size_906_ = lean_ctor_get(v___y_904_, 0);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v_size_906_, v___x_907_);
lean_inc_ref(v_e_843_);
v___x_909_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_904_, v___x_908_, v_i_905_, v_e_843_, v___x_868_);
lean_dec(v_i_905_);
v___y_870_ = v___x_909_;
goto v___jp_869_;
}
v___jp_910_:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(v___y_911_, v_e_843_);
switch(lean_obj_tag(v___x_912_))
{
case 0:
{
lean_object* v_index_913_; lean_object* v_size_914_; lean_object* v___x_915_; 
v_index_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_index_913_);
lean_dec_ref_known(v___x_912_, 3);
v_size_914_ = lean_ctor_get(v___y_911_, 0);
lean_inc(v_size_914_);
lean_inc_ref(v_e_843_);
v___x_915_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_911_, v_size_914_, v_index_913_, v_e_843_, v___x_868_);
lean_dec(v_index_913_);
v___y_870_ = v___x_915_;
goto v___jp_869_;
}
case 1:
{
lean_object* v_index_916_; 
v_index_916_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_index_916_);
lean_dec_ref_known(v___x_912_, 1);
v___y_904_ = v___y_911_;
v_i_905_ = v_index_916_;
goto v___jp_903_;
}
default: 
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_911_, v___x_917_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_index_919_; 
v_index_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_index_919_);
lean_dec_ref_known(v___x_918_, 1);
v___y_904_ = v___y_911_;
v_i_905_ = v_index_919_;
goto v___jp_903_;
}
else
{
v___y_870_ = v___y_911_;
goto v___jp_869_;
}
}
}
}
v___jp_920_:
{
lean_object* v_size_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_size_923_ = lean_ctor_get(v___y_921_, 0);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_add(v_size_923_, v___x_924_);
lean_inc_ref(v_e_843_);
v___x_926_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_921_, v___x_925_, v_i_922_, v_e_843_, v___x_868_);
lean_dec(v_i_922_);
v___y_870_ = v___x_926_;
goto v___jp_869_;
}
v___jp_927_:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg(v_a_844_);
lean_dec_ref(v_a_844_);
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(v___x_928_, v_e_843_);
switch(lean_obj_tag(v___x_929_))
{
case 0:
{
lean_object* v_index_930_; lean_object* v_size_931_; lean_object* v___x_932_; 
v_index_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_index_930_);
lean_dec_ref_known(v___x_929_, 3);
v_size_931_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_size_931_);
lean_inc_ref(v_e_843_);
v___x_932_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_928_, v_size_931_, v_index_930_, v_e_843_, v___x_868_);
lean_dec(v_index_930_);
v___y_870_ = v___x_932_;
goto v___jp_869_;
}
case 1:
{
lean_object* v_index_933_; 
v_index_933_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_index_933_);
lean_dec_ref_known(v___x_929_, 1);
v___y_921_ = v___x_928_;
v_i_922_ = v_index_933_;
goto v___jp_920_;
}
default: 
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_928_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_index_936_; 
v_index_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_index_936_);
lean_dec_ref_known(v___x_935_, 1);
v___y_921_ = v___x_928_;
v_i_922_ = v_index_936_;
goto v___jp_920_;
}
else
{
v___y_870_ = v___x_928_;
goto v___jp_869_;
}
}
}
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_e_843_);
v___x_964_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v_a_844_);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
v___jp_854_:
{
lean_object* v___x_858_; 
v___x_858_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_842_, v_d_855_, v___y_857_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v_fst_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
v_fst_860_ = lean_ctor_get(v_a_859_, 0);
if (lean_obj_tag(v_fst_860_) == 0)
{
lean_dec(v_a_859_);
lean_dec_ref(v_b_856_);
return v___x_858_;
}
else
{
lean_object* v_snd_861_; 
lean_dec_ref_known(v___x_858_, 1);
v_snd_861_ = lean_ctor_get(v_a_859_, 1);
lean_inc(v_snd_861_);
lean_dec(v_a_859_);
v_e_843_ = v_b_856_;
v_a_844_ = v_snd_861_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_856_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_mvarId_967_, lean_object* v_mvarId_x27_968_, lean_object* v_a_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = l_Lean_instBEqMVarId_beq(v_mvarId_967_, v_mvarId_x27_968_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_x27_968_, v_a_969_, v___y_975_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1064_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1064_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1064_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_fst_985_; 
v_fst_985_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_fst_985_);
if (lean_obj_tag(v_fst_985_) == 0)
{
lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_mvarId_x27_968_);
v_snd_986_ = lean_ctor_get(v_a_981_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v_a_981_, 0);
lean_dec(v_unused_1005_);
v___x_988_ = v_a_981_;
v_isShared_989_ = v_isSharedCheck_1004_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_dec(v_a_981_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1004_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1003_; 
v_a_990_ = lean_ctor_get(v_fst_985_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_fst_985_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_992_ = v_fst_985_;
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v_fst_985_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_1002_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_995_);
v___x_997_ = v___x_988_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_snd_986_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_997_);
v___x_999_ = v___x_983_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
else
{
lean_object* v_a_1006_; 
lean_del_object(v___x_983_);
v_a_1006_ = lean_ctor_get(v_fst_985_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v_fst_985_, 1);
if (lean_obj_tag(v_a_1006_) == 0)
{
lean_object* v_snd_1007_; lean_object* v___x_1008_; 
v_snd_1007_ = lean_ctor_get(v_a_981_, 1);
lean_inc(v_snd_1007_);
lean_dec(v_a_981_);
v___x_1008_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___redArg(v_mvarId_x27_968_, v_snd_1007_, v___y_975_);
lean_dec(v_mvarId_x27_968_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1052_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1052_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1052_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_fst_1013_; 
v_fst_1013_ = lean_ctor_get(v_a_1009_, 0);
lean_inc(v_fst_1013_);
if (lean_obj_tag(v_fst_1013_) == 0)
{
lean_object* v_snd_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1032_; 
v_snd_1014_ = lean_ctor_get(v_a_1009_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_a_1009_, 0);
lean_dec(v_unused_1033_);
v___x_1016_ = v_a_1009_;
v_isShared_1017_ = v_isSharedCheck_1032_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_snd_1014_);
lean_dec(v_a_1009_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1032_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1031_; 
v_a_1018_ = lean_ctor_get(v_fst_1013_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_fst_1013_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1020_ = v_fst_1013_;
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v_fst_1013_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1023_);
v___x_1025_ = v___x_1016_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_snd_1014_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1025_);
v___x_1027_ = v___x_1011_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
else
{
lean_object* v_a_1034_; 
v_a_1034_ = lean_ctor_get(v_fst_1013_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v_fst_1013_, 1);
if (lean_obj_tag(v_a_1034_) == 0)
{
lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1046_; 
v_snd_1035_ = lean_ctor_get(v_a_1009_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_a_1009_, 0);
lean_dec(v_unused_1047_);
v___x_1037_ = v_a_1009_;
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_dec(v_a_1009_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_snd_1035_);
v___x_1041_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1041_);
v___x_1043_ = v___x_1011_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v_val_1048_; lean_object* v_snd_1049_; lean_object* v_mvarIdPending_1050_; 
lean_del_object(v___x_1011_);
v_val_1048_ = lean_ctor_get(v_a_1034_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v_a_1034_, 1);
v_snd_1049_ = lean_ctor_get(v_a_1009_, 1);
lean_inc(v_snd_1049_);
lean_dec(v_a_1009_);
v_mvarIdPending_1050_ = lean_ctor_get(v_val_1048_, 1);
lean_inc(v_mvarIdPending_1050_);
lean_dec(v_val_1048_);
v_mvarId_x27_968_ = v_mvarIdPending_1050_;
v_a_969_ = v_snd_1049_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1008_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1008_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
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
else
{
lean_object* v_snd_1061_; lean_object* v_val_1062_; lean_object* v___x_1063_; 
lean_dec(v_mvarId_x27_968_);
v_snd_1061_ = lean_ctor_get(v_a_981_, 1);
lean_inc(v_snd_1061_);
lean_dec(v_a_981_);
v_val_1062_ = lean_ctor_get(v_a_1006_, 0);
lean_inc(v_val_1062_);
lean_dec_ref_known(v_a_1006_, 1);
v___x_1063_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_967_, v_val_1062_, v_snd_1061_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec(v_mvarId_x27_968_);
v_a_1065_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_980_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_980_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v_mvarId_x27_968_);
v___x_1073_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__1));
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_969_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___boxed(lean_object* v_mvarId_1076_, lean_object* v_mvarId_x27_1077_, lean_object* v_a_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_1076_, v_mvarId_x27_1077_, v_a_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v_mvarId_1076_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_1089_, lean_object* v_e_1090_, lean_object* v_a_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1089_, v_e_1090_, v_a_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v_mvarId_1089_);
return v_res_1101_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v_cellCount_1102_; lean_object* v___x_1103_; 
v_cellCount_1102_ = lean_unsigned_to_nat(16u);
v___x_1103_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v_cellCount_1104_; lean_object* v___x_1105_; 
v_cellCount_1104_ = lean_unsigned_to_nat(16u);
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1106_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1107_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v___x_1107_);
lean_ctor_set(v___x_1109_, 2, v___x_1106_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1110_, lean_object* v_e_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v___x_1121_; 
v___x_1121_ = l_Lean_Expr_hasExprMVar(v_e_1111_);
if (v___x_1121_ == 0)
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec_ref(v_e_1111_);
v___x_1122_ = 1;
v___x_1123_ = lean_box(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__2, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__2_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__2);
v___x_1126_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1110_, v_e_1111_, v___x_1125_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1141_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1141_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1141_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v_fst_1131_; 
v_fst_1131_ = lean_ctor_get(v_a_1127_, 0);
lean_inc(v_fst_1131_);
lean_dec(v_a_1127_);
if (lean_obj_tag(v_fst_1131_) == 0)
{
uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_dec_ref_known(v_fst_1131_, 1);
v___x_1132_ = 0;
v___x_1133_ = lean_box(v___x_1132_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1133_);
v___x_1135_ = v___x_1129_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec_ref_known(v_fst_1131_, 1);
v___x_1137_ = lean_box(v___x_1121_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1137_);
v___x_1139_ = v___x_1129_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1126_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1126_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1150_, lean_object* v_e_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1150_, v_e_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v_mvarId_1150_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object* v_msgData_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v_env_1169_; lean_object* v___x_1170_; lean_object* v_mctx_1171_; lean_object* v_lctx_1172_; lean_object* v_options_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1168_ = lean_st_ref_get(v___y_1166_);
v_env_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_env_1169_);
lean_dec(v___x_1168_);
v___x_1170_ = lean_st_ref_get(v___y_1164_);
v_mctx_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc_ref(v_mctx_1171_);
lean_dec(v___x_1170_);
v_lctx_1172_ = lean_ctor_get(v___y_1163_, 2);
v_options_1173_ = lean_ctor_get(v___y_1165_, 2);
lean_inc_ref(v_options_1173_);
lean_inc_ref(v_lctx_1172_);
v___x_1174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1174_, 0, v_env_1169_);
lean_ctor_set(v___x_1174_, 1, v_mctx_1171_);
lean_ctor_set(v___x_1174_, 2, v_lctx_1172_);
lean_ctor_set(v___x_1174_, 3, v_options_1173_);
v___x_1175_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v_msgData_1162_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object* v_msgData_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msgData_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v_msg_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_ref_1190_; lean_object* v___x_1191_; lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_ref_1190_ = lean_ctor_get(v___y_1187_, 5);
v___x_1191_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msg_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_inc(v_ref_1190_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_ref_1190_);
lean_ctor_set(v___x_1196_, 1, v_a_1192_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 1);
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24_spec__27___redArg(lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_ks_1212_; lean_object* v_vs_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1237_; 
v_ks_1212_ = lean_ctor_get(v_x_1208_, 0);
v_vs_1213_ = lean_ctor_get(v_x_1208_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1208_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1215_ = v_x_1208_;
v_isShared_1216_ = v_isSharedCheck_1237_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_vs_1213_);
lean_inc(v_ks_1212_);
lean_dec(v_x_1208_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1237_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = lean_array_get_size(v_ks_1212_);
v___x_1218_ = lean_nat_dec_lt(v_x_1209_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_dec(v_x_1209_);
v___x_1219_ = lean_array_push(v_ks_1212_, v_x_1210_);
v___x_1220_ = lean_array_push(v_vs_1213_, v_x_1211_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1220_);
lean_ctor_set(v___x_1215_, 0, v___x_1219_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
else
{
lean_object* v_k_x27_1224_; uint8_t v___x_1225_; 
v_k_x27_1224_ = lean_array_fget_borrowed(v_ks_1212_, v_x_1209_);
v___x_1225_ = l_Lean_instBEqMVarId_beq(v_x_1210_, v_k_x27_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1227_; 
if (v_isShared_1216_ == 0)
{
v___x_1227_ = v___x_1215_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_ks_1212_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_vs_1213_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_nat_add(v_x_1209_, v___x_1228_);
lean_dec(v_x_1209_);
v_x_1208_ = v___x_1227_;
v_x_1209_ = v___x_1229_;
goto _start;
}
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1232_ = lean_array_fset(v_ks_1212_, v_x_1209_, v_x_1210_);
v___x_1233_ = lean_array_fset(v_vs_1213_, v_x_1209_, v_x_1211_);
lean_dec(v_x_1209_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1233_);
lean_ctor_set(v___x_1215_, 0, v___x_1232_);
v___x_1235_ = v___x_1215_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1233_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24___redArg(lean_object* v_n_1238_, lean_object* v_k_1239_, lean_object* v_v_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24_spec__27___redArg(v_n_1238_, v___x_1241_, v_k_1239_, v_v_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg(lean_object* v_x_1244_, size_t v_x_1245_, size_t v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
lean_object* v_es_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v_j_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v_es_1249_ = lean_ctor_get(v_x_1244_, 0);
v___x_1250_ = ((size_t)31ULL);
v___x_1251_ = lean_usize_land(v_x_1245_, v___x_1250_);
v_j_1252_ = lean_usize_to_nat(v___x_1251_);
v___x_1253_ = lean_array_get_size(v_es_1249_);
v___x_1254_ = lean_nat_dec_lt(v_j_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec(v_j_1252_);
lean_dec(v_x_1248_);
lean_dec(v_x_1247_);
return v_x_1244_;
}
else
{
lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1293_; 
lean_inc_ref(v_es_1249_);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v_x_1244_, 0);
lean_dec(v_unused_1294_);
v___x_1256_ = v_x_1244_;
v_isShared_1257_ = v_isSharedCheck_1293_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v_x_1244_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1293_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_v_1258_; lean_object* v___x_1259_; lean_object* v_xs_x27_1260_; lean_object* v___y_1262_; 
v_v_1258_ = lean_array_fget(v_es_1249_, v_j_1252_);
v___x_1259_ = lean_box(0);
v_xs_x27_1260_ = lean_array_fset(v_es_1249_, v_j_1252_, v___x_1259_);
switch(lean_obj_tag(v_v_1258_))
{
case 0:
{
lean_object* v_key_1267_; lean_object* v_val_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v_key_1267_ = lean_ctor_get(v_v_1258_, 0);
v_val_1268_ = lean_ctor_get(v_v_1258_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_v_1258_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1270_ = v_v_1258_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_val_1268_);
lean_inc(v_key_1267_);
lean_dec(v_v_1258_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_instBEqMVarId_beq(v_x_1247_, v_key_1267_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_del_object(v___x_1270_);
v___x_1273_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1267_, v_val_1268_, v_x_1247_, v_x_1248_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
v___y_1262_ = v___x_1274_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1276_; 
lean_dec(v_val_1268_);
lean_dec(v_key_1267_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v_x_1248_);
lean_ctor_set(v___x_1270_, 0, v_x_1247_);
v___x_1276_ = v___x_1270_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_x_1247_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_x_1248_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
v___y_1262_ = v___x_1276_;
goto v___jp_1261_;
}
}
}
}
case 1:
{
lean_object* v_node_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1291_; 
v_node_1279_ = lean_ctor_get(v_v_1258_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_v_1258_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1281_ = v_v_1258_;
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_node_1279_);
lean_dec(v_v_1258_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1283_ = ((size_t)5ULL);
v___x_1284_ = lean_usize_shift_right(v_x_1245_, v___x_1283_);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_add(v_x_1246_, v___x_1285_);
v___x_1287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg(v_node_1279_, v___x_1284_, v___x_1286_, v_x_1247_, v_x_1248_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1287_);
v___x_1289_ = v___x_1281_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
v___y_1262_ = v___x_1289_;
goto v___jp_1261_;
}
}
}
default: 
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_x_1247_);
lean_ctor_set(v___x_1292_, 1, v_x_1248_);
v___y_1262_ = v___x_1292_;
goto v___jp_1261_;
}
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = lean_array_fset(v_xs_x27_1260_, v_j_1252_, v___y_1262_);
lean_dec(v_j_1252_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1263_);
v___x_1265_ = v___x_1256_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
else
{
lean_object* v_ks_1295_; lean_object* v_vs_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1316_; 
v_ks_1295_ = lean_ctor_get(v_x_1244_, 0);
v_vs_1296_ = lean_ctor_get(v_x_1244_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1298_ = v_x_1244_;
v_isShared_1299_ = v_isSharedCheck_1316_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_vs_1296_);
lean_inc(v_ks_1295_);
lean_dec(v_x_1244_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1316_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_ks_1295_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_vs_1296_);
v___x_1301_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v_newNode_1302_; uint8_t v___y_1304_; size_t v___x_1310_; uint8_t v___x_1311_; 
v_newNode_1302_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24___redArg(v___x_1301_, v_x_1247_, v_x_1248_);
v___x_1310_ = ((size_t)7ULL);
v___x_1311_ = lean_usize_dec_le(v___x_1310_, v_x_1246_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1302_);
v___x_1313_ = lean_unsigned_to_nat(4u);
v___x_1314_ = lean_nat_dec_lt(v___x_1312_, v___x_1313_);
lean_dec(v___x_1312_);
v___y_1304_ = v___x_1314_;
goto v___jp_1303_;
}
else
{
v___y_1304_ = v___x_1311_;
goto v___jp_1303_;
}
v___jp_1303_:
{
if (v___y_1304_ == 0)
{
lean_object* v_ks_1305_; lean_object* v_vs_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_ks_1305_ = lean_ctor_get(v_newNode_1302_, 0);
lean_inc_ref(v_ks_1305_);
v_vs_1306_ = lean_ctor_get(v_newNode_1302_, 1);
lean_inc_ref(v_vs_1306_);
lean_dec_ref(v_newNode_1302_);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___closed__0);
v___x_1309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___redArg(v_x_1246_, v_ks_1305_, v_vs_1306_, v___x_1307_, v___x_1308_);
lean_dec_ref(v_vs_1306_);
lean_dec_ref(v_ks_1305_);
return v___x_1309_;
}
else
{
return v_newNode_1302_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___redArg(size_t v_depth_1317_, lean_object* v_keys_1318_, lean_object* v_vals_1319_, lean_object* v_i_1320_, lean_object* v_entries_1321_){
_start:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_array_get_size(v_keys_1318_);
v___x_1323_ = lean_nat_dec_lt(v_i_1320_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec(v_i_1320_);
return v_entries_1321_;
}
else
{
lean_object* v_k_1324_; lean_object* v_v_1325_; uint64_t v___x_1326_; size_t v_h_1327_; size_t v___x_1328_; lean_object* v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v_h_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_k_1324_ = lean_array_fget_borrowed(v_keys_1318_, v_i_1320_);
v_v_1325_ = lean_array_fget_borrowed(v_vals_1319_, v_i_1320_);
v___x_1326_ = l_Lean_instHashableMVarId_hash(v_k_1324_);
v_h_1327_ = lean_uint64_to_usize(v___x_1326_);
v___x_1328_ = ((size_t)5ULL);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_sub(v_depth_1317_, v___x_1330_);
v___x_1332_ = lean_usize_mul(v___x_1328_, v___x_1331_);
v_h_1333_ = lean_usize_shift_right(v_h_1327_, v___x_1332_);
v___x_1334_ = lean_nat_add(v_i_1320_, v___x_1329_);
lean_dec(v_i_1320_);
lean_inc(v_v_1325_);
lean_inc(v_k_1324_);
v___x_1335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg(v_entries_1321_, v_h_1333_, v_depth_1317_, v_k_1324_, v_v_1325_);
v_i_1320_ = v___x_1334_;
v_entries_1321_ = v___x_1335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___redArg___boxed(lean_object* v_depth_1337_, lean_object* v_keys_1338_, lean_object* v_vals_1339_, lean_object* v_i_1340_, lean_object* v_entries_1341_){
_start:
{
size_t v_depth_boxed_1342_; lean_object* v_res_1343_; 
v_depth_boxed_1342_ = lean_unbox_usize(v_depth_1337_);
lean_dec(v_depth_1337_);
v_res_1343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___redArg(v_depth_boxed_1342_, v_keys_1338_, v_vals_1339_, v_i_1340_, v_entries_1341_);
lean_dec_ref(v_vals_1339_);
lean_dec_ref(v_keys_1338_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg___boxed(lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
size_t v_x_94503__boxed_1349_; size_t v_x_94504__boxed_1350_; lean_object* v_res_1351_; 
v_x_94503__boxed_1349_ = lean_unbox_usize(v_x_1345_);
lean_dec(v_x_1345_);
v_x_94504__boxed_1350_ = lean_unbox_usize(v_x_1346_);
lean_dec(v_x_1346_);
v_res_1351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg(v_x_1344_, v_x_94503__boxed_1349_, v_x_94504__boxed_1350_, v_x_1347_, v_x_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_){
_start:
{
uint64_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1355_ = l_Lean_instHashableMVarId_hash(v_x_1353_);
v___x_1356_ = lean_uint64_to_usize(v___x_1355_);
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg(v_x_1352_, v___x_1356_, v___x_1357_, v_x_1353_, v_x_1354_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_1359_, lean_object* v_val_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v_mctx_1364_; lean_object* v_cache_1365_; lean_object* v_zetaDeltaFVarIds_1366_; lean_object* v_postponed_1367_; lean_object* v_diag_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1397_; 
v___x_1363_ = lean_st_ref_take(v___y_1361_);
v_mctx_1364_ = lean_ctor_get(v___x_1363_, 0);
v_cache_1365_ = lean_ctor_get(v___x_1363_, 1);
v_zetaDeltaFVarIds_1366_ = lean_ctor_get(v___x_1363_, 2);
v_postponed_1367_ = lean_ctor_get(v___x_1363_, 3);
v_diag_1368_ = lean_ctor_get(v___x_1363_, 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1370_ = v___x_1363_;
v_isShared_1371_ = v_isSharedCheck_1397_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_diag_1368_);
lean_inc(v_postponed_1367_);
lean_inc(v_zetaDeltaFVarIds_1366_);
lean_inc(v_cache_1365_);
lean_inc(v_mctx_1364_);
lean_dec(v___x_1363_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1397_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v_depth_1372_; lean_object* v_levelAssignDepth_1373_; lean_object* v_lmvarCounter_1374_; lean_object* v_mvarCounter_1375_; lean_object* v_lDecls_1376_; lean_object* v_decls_1377_; lean_object* v_userNames_1378_; lean_object* v_lAssignment_1379_; lean_object* v_eAssignment_1380_; lean_object* v_dAssignment_1381_; lean_object* v_instanceTypedMVars_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1396_; 
v_depth_1372_ = lean_ctor_get(v_mctx_1364_, 0);
v_levelAssignDepth_1373_ = lean_ctor_get(v_mctx_1364_, 1);
v_lmvarCounter_1374_ = lean_ctor_get(v_mctx_1364_, 2);
v_mvarCounter_1375_ = lean_ctor_get(v_mctx_1364_, 3);
v_lDecls_1376_ = lean_ctor_get(v_mctx_1364_, 4);
v_decls_1377_ = lean_ctor_get(v_mctx_1364_, 5);
v_userNames_1378_ = lean_ctor_get(v_mctx_1364_, 6);
v_lAssignment_1379_ = lean_ctor_get(v_mctx_1364_, 7);
v_eAssignment_1380_ = lean_ctor_get(v_mctx_1364_, 8);
v_dAssignment_1381_ = lean_ctor_get(v_mctx_1364_, 9);
v_instanceTypedMVars_1382_ = lean_ctor_get(v_mctx_1364_, 10);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_mctx_1364_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1384_ = v_mctx_1364_;
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_instanceTypedMVars_1382_);
lean_inc(v_dAssignment_1381_);
lean_inc(v_eAssignment_1380_);
lean_inc(v_lAssignment_1379_);
lean_inc(v_userNames_1378_);
lean_inc(v_decls_1377_);
lean_inc(v_lDecls_1376_);
lean_inc(v_mvarCounter_1375_);
lean_inc(v_lmvarCounter_1374_);
lean_inc(v_levelAssignDepth_1373_);
lean_inc(v_depth_1372_);
lean_dec(v_mctx_1364_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_1380_, v_mvarId_1359_, v_val_1360_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 8, v___x_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_depth_1372_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_levelAssignDepth_1373_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_lmvarCounter_1374_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_mvarCounter_1375_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_lDecls_1376_);
lean_ctor_set(v_reuseFailAlloc_1395_, 5, v_decls_1377_);
lean_ctor_set(v_reuseFailAlloc_1395_, 6, v_userNames_1378_);
lean_ctor_set(v_reuseFailAlloc_1395_, 7, v_lAssignment_1379_);
lean_ctor_set(v_reuseFailAlloc_1395_, 8, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1395_, 9, v_dAssignment_1381_);
lean_ctor_set(v_reuseFailAlloc_1395_, 10, v_instanceTypedMVars_1382_);
v___x_1388_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1388_);
v___x_1390_ = v___x_1370_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_cache_1365_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_zetaDeltaFVarIds_1366_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_postponed_1367_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_diag_1368_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_st_ref_put(v___y_1361_, v___x_1390_);
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_1398_, lean_object* v_val_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_1398_, v_val_1399_, v___y_1400_);
lean_dec(v___y_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0(uint8_t v___y_1411_, uint8_t v_suppressElabErrors_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 1)
{
lean_object* v_pre_1414_; 
v_pre_1414_ = lean_ctor_get(v_x_1413_, 0);
switch(lean_obj_tag(v_pre_1414_))
{
case 1:
{
lean_object* v_pre_1415_; 
v_pre_1415_ = lean_ctor_get(v_pre_1414_, 0);
switch(lean_obj_tag(v_pre_1415_))
{
case 0:
{
lean_object* v_str_1416_; lean_object* v_str_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_str_1416_ = lean_ctor_get(v_x_1413_, 1);
v_str_1417_ = lean_ctor_get(v_pre_1414_, 1);
v___x_1418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__0));
v___x_1419_ = lean_string_dec_eq(v_str_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1));
v___x_1421_ = lean_string_dec_eq(v_str_1417_, v___x_1420_);
if (v___x_1421_ == 0)
{
return v___y_1411_;
}
else
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__2));
v___x_1423_ = lean_string_dec_eq(v_str_1416_, v___x_1422_);
if (v___x_1423_ == 0)
{
return v___y_1411_;
}
else
{
return v_suppressElabErrors_1412_;
}
}
}
else
{
lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__3));
v___x_1425_ = lean_string_dec_eq(v_str_1416_, v___x_1424_);
if (v___x_1425_ == 0)
{
return v___y_1411_;
}
else
{
return v_suppressElabErrors_1412_;
}
}
}
case 1:
{
lean_object* v_pre_1426_; 
v_pre_1426_ = lean_ctor_get(v_pre_1415_, 0);
if (lean_obj_tag(v_pre_1426_) == 0)
{
lean_object* v_str_1427_; lean_object* v_str_1428_; lean_object* v_str_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_str_1427_ = lean_ctor_get(v_x_1413_, 1);
v_str_1428_ = lean_ctor_get(v_pre_1414_, 1);
v_str_1429_ = lean_ctor_get(v_pre_1415_, 1);
v___x_1430_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__4));
v___x_1431_ = lean_string_dec_eq(v_str_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
return v___y_1411_;
}
else
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__5));
v___x_1433_ = lean_string_dec_eq(v_str_1428_, v___x_1432_);
if (v___x_1433_ == 0)
{
return v___y_1411_;
}
else
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__6));
v___x_1435_ = lean_string_dec_eq(v_str_1427_, v___x_1434_);
if (v___x_1435_ == 0)
{
return v___y_1411_;
}
else
{
return v_suppressElabErrors_1412_;
}
}
}
}
else
{
return v___y_1411_;
}
}
default: 
{
return v___y_1411_;
}
}
}
case 0:
{
lean_object* v_str_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_str_1436_ = lean_ctor_get(v_x_1413_, 1);
v___x_1437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__7));
v___x_1438_ = lean_string_dec_eq(v_str_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
return v___y_1411_;
}
else
{
return v_suppressElabErrors_1412_;
}
}
default: 
{
return v___y_1411_;
}
}
}
else
{
return v___y_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___boxed(lean_object* v___y_1439_, lean_object* v_suppressElabErrors_1440_, lean_object* v_x_1441_){
_start:
{
uint8_t v___y_94732__boxed_1442_; uint8_t v_suppressElabErrors_boxed_1443_; uint8_t v_res_1444_; lean_object* v_r_1445_; 
v___y_94732__boxed_1442_ = lean_unbox(v___y_1439_);
v_suppressElabErrors_boxed_1443_ = lean_unbox(v_suppressElabErrors_1440_);
v_res_1444_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0(v___y_94732__boxed_1442_, v_suppressElabErrors_boxed_1443_, v_x_1441_);
lean_dec(v_x_1441_);
v_r_1445_ = lean_box(v_res_1444_);
return v_r_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg(lean_object* v_ref_1447_, lean_object* v_msgData_1448_, uint8_t v_severity_1449_, uint8_t v_isSilent_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; uint8_t v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; uint8_t v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; uint8_t v___y_1496_; uint8_t v___y_1497_; lean_object* v___y_1498_; uint8_t v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1518_; lean_object* v___y_1519_; uint8_t v___y_1520_; uint8_t v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; uint8_t v___y_1532_; uint8_t v___y_1533_; lean_object* v___y_1534_; uint8_t v___y_1535_; uint8_t v___x_1540_; lean_object* v___y_1542_; lean_object* v___y_1543_; uint8_t v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; uint8_t v___y_1547_; uint8_t v___y_1548_; uint8_t v___y_1550_; uint8_t v___x_1565_; 
v___x_1540_ = 2;
v___x_1565_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1449_, v___x_1540_);
if (v___x_1565_ == 0)
{
v___y_1550_ = v___x_1565_;
goto v___jp_1549_;
}
else
{
uint8_t v___x_1566_; 
lean_inc_ref(v_msgData_1448_);
v___x_1566_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1448_);
v___y_1550_ = v___x_1566_;
goto v___jp_1549_;
}
v___jp_1456_:
{
lean_object* v___x_1466_; lean_object* v_currNamespace_1467_; lean_object* v_openDecls_1468_; lean_object* v_env_1469_; lean_object* v_nextMacroScope_1470_; lean_object* v_ngen_1471_; lean_object* v_auxDeclNGen_1472_; lean_object* v_traceState_1473_; lean_object* v_cache_1474_; lean_object* v_messages_1475_; lean_object* v_infoState_1476_; lean_object* v_snapshotTasks_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1491_; 
v___x_1466_ = lean_st_ref_take(v___y_1465_);
v_currNamespace_1467_ = lean_ctor_get(v___y_1464_, 6);
v_openDecls_1468_ = lean_ctor_get(v___y_1464_, 7);
v_env_1469_ = lean_ctor_get(v___x_1466_, 0);
v_nextMacroScope_1470_ = lean_ctor_get(v___x_1466_, 1);
v_ngen_1471_ = lean_ctor_get(v___x_1466_, 2);
v_auxDeclNGen_1472_ = lean_ctor_get(v___x_1466_, 3);
v_traceState_1473_ = lean_ctor_get(v___x_1466_, 4);
v_cache_1474_ = lean_ctor_get(v___x_1466_, 5);
v_messages_1475_ = lean_ctor_get(v___x_1466_, 6);
v_infoState_1476_ = lean_ctor_get(v___x_1466_, 7);
v_snapshotTasks_1477_ = lean_ctor_get(v___x_1466_, 8);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1479_ = v___x_1466_;
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_snapshotTasks_1477_);
lean_inc(v_infoState_1476_);
lean_inc(v_messages_1475_);
lean_inc(v_cache_1474_);
lean_inc(v_traceState_1473_);
lean_inc(v_auxDeclNGen_1472_);
lean_inc(v_ngen_1471_);
lean_inc(v_nextMacroScope_1470_);
lean_inc(v_env_1469_);
lean_dec(v___x_1466_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1491_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_inc(v_openDecls_1468_);
lean_inc(v_currNamespace_1467_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_currNamespace_1467_);
lean_ctor_set(v___x_1481_, 1, v_openDecls_1468_);
v___x_1482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___y_1461_);
lean_inc_ref(v___y_1458_);
lean_inc_ref(v___y_1459_);
v___x_1483_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1483_, 0, v___y_1459_);
lean_ctor_set(v___x_1483_, 1, v___y_1462_);
lean_ctor_set(v___x_1483_, 2, v___y_1457_);
lean_ctor_set(v___x_1483_, 3, v___y_1458_);
lean_ctor_set(v___x_1483_, 4, v___x_1482_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*5, v___y_1460_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*5 + 1, v___y_1463_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*5 + 2, v_isSilent_1450_);
v___x_1484_ = l_Lean_MessageLog_add(v___x_1483_, v_messages_1475_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 6, v___x_1484_);
v___x_1486_ = v___x_1479_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_env_1469_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_nextMacroScope_1470_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_ngen_1471_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_auxDeclNGen_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_traceState_1473_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_cache_1474_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_infoState_1476_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v_snapshotTasks_1477_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_st_ref_put(v___y_1465_, v___x_1486_);
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
}
v___jp_1492_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1516_; 
v___x_1501_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1448_);
v___x_1502_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v___x_1501_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1516_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1516_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_inc_ref_n(v___y_1498_, 2);
v___x_1507_ = l_Lean_FileMap_toPosition(v___y_1498_, v___y_1494_);
lean_dec(v___y_1494_);
v___x_1508_ = l_Lean_FileMap_toPosition(v___y_1498_, v___y_1500_);
lean_dec(v___y_1500_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___closed__0));
if (v___y_1497_ == 0)
{
lean_del_object(v___x_1505_);
lean_dec_ref(v___y_1493_);
v___y_1457_ = v___x_1509_;
v___y_1458_ = v___x_1510_;
v___y_1459_ = v___y_1495_;
v___y_1460_ = v___y_1496_;
v___y_1461_ = v_a_1503_;
v___y_1462_ = v___x_1507_;
v___y_1463_ = v___y_1499_;
v___y_1464_ = v___y_1453_;
v___y_1465_ = v___y_1454_;
goto v___jp_1456_;
}
else
{
uint8_t v___x_1511_; 
lean_inc(v_a_1503_);
v___x_1511_ = l_Lean_MessageData_hasTag(v___y_1493_, v_a_1503_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_dec_ref_known(v___x_1509_, 1);
lean_dec_ref(v___x_1507_);
lean_dec(v_a_1503_);
v___x_1512_ = lean_box(0);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1512_);
v___x_1514_ = v___x_1505_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
else
{
lean_del_object(v___x_1505_);
v___y_1457_ = v___x_1509_;
v___y_1458_ = v___x_1510_;
v___y_1459_ = v___y_1495_;
v___y_1460_ = v___y_1496_;
v___y_1461_ = v_a_1503_;
v___y_1462_ = v___x_1507_;
v___y_1463_ = v___y_1499_;
v___y_1464_ = v___y_1453_;
v___y_1465_ = v___y_1454_;
goto v___jp_1456_;
}
}
}
}
v___jp_1517_:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Syntax_getTailPos_x3f(v___y_1522_, v___y_1520_);
lean_dec(v___y_1522_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_inc(v___y_1525_);
v___y_1493_ = v___y_1518_;
v___y_1494_ = v___y_1525_;
v___y_1495_ = v___y_1519_;
v___y_1496_ = v___y_1520_;
v___y_1497_ = v___y_1521_;
v___y_1498_ = v___y_1523_;
v___y_1499_ = v___y_1524_;
v___y_1500_ = v___y_1525_;
goto v___jp_1492_;
}
else
{
lean_object* v_val_1527_; 
v_val_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___y_1493_ = v___y_1518_;
v___y_1494_ = v___y_1525_;
v___y_1495_ = v___y_1519_;
v___y_1496_ = v___y_1520_;
v___y_1497_ = v___y_1521_;
v___y_1498_ = v___y_1523_;
v___y_1499_ = v___y_1524_;
v___y_1500_ = v_val_1527_;
goto v___jp_1492_;
}
}
v___jp_1528_:
{
lean_object* v_ref_1536_; lean_object* v___x_1537_; 
v_ref_1536_ = l_Lean_replaceRef(v_ref_1447_, v___y_1530_);
v___x_1537_ = l_Lean_Syntax_getPos_x3f(v_ref_1536_, v___y_1532_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_unsigned_to_nat(0u);
v___y_1518_ = v___y_1529_;
v___y_1519_ = v___y_1531_;
v___y_1520_ = v___y_1532_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v_ref_1536_;
v___y_1523_ = v___y_1534_;
v___y_1524_ = v___y_1535_;
v___y_1525_ = v___x_1538_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1539_; 
v_val_1539_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v___x_1537_, 1);
v___y_1518_ = v___y_1529_;
v___y_1519_ = v___y_1531_;
v___y_1520_ = v___y_1532_;
v___y_1521_ = v___y_1533_;
v___y_1522_ = v_ref_1536_;
v___y_1523_ = v___y_1534_;
v___y_1524_ = v___y_1535_;
v___y_1525_ = v_val_1539_;
goto v___jp_1517_;
}
}
v___jp_1541_:
{
if (v___y_1548_ == 0)
{
v___y_1529_ = v___y_1546_;
v___y_1530_ = v___y_1542_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1547_;
v___y_1533_ = v___y_1544_;
v___y_1534_ = v___y_1545_;
v___y_1535_ = v_severity_1449_;
goto v___jp_1528_;
}
else
{
v___y_1529_ = v___y_1546_;
v___y_1530_ = v___y_1542_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1547_;
v___y_1533_ = v___y_1544_;
v___y_1534_ = v___y_1545_;
v___y_1535_ = v___x_1540_;
goto v___jp_1528_;
}
}
v___jp_1549_:
{
if (v___y_1550_ == 0)
{
lean_object* v_fileName_1551_; lean_object* v_fileMap_1552_; lean_object* v_options_1553_; lean_object* v_ref_1554_; uint8_t v_suppressElabErrors_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___f_1558_; uint8_t v___x_1559_; uint8_t v___x_1560_; 
v_fileName_1551_ = lean_ctor_get(v___y_1453_, 0);
v_fileMap_1552_ = lean_ctor_get(v___y_1453_, 1);
v_options_1553_ = lean_ctor_get(v___y_1453_, 2);
v_ref_1554_ = lean_ctor_get(v___y_1453_, 5);
v_suppressElabErrors_1555_ = lean_ctor_get_uint8(v___y_1453_, sizeof(void*)*14 + 1);
v___x_1556_ = lean_box(v___y_1550_);
v___x_1557_ = lean_box(v_suppressElabErrors_1555_);
v___f_1558_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1558_, 0, v___x_1556_);
lean_closure_set(v___f_1558_, 1, v___x_1557_);
v___x_1559_ = 1;
v___x_1560_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1449_, v___x_1559_);
if (v___x_1560_ == 0)
{
v___y_1542_ = v_ref_1554_;
v___y_1543_ = v_fileName_1551_;
v___y_1544_ = v_suppressElabErrors_1555_;
v___y_1545_ = v_fileMap_1552_;
v___y_1546_ = v___f_1558_;
v___y_1547_ = v___y_1550_;
v___y_1548_ = v___x_1560_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = l_Lean_warningAsError;
v___x_1562_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_1553_, v___x_1561_);
v___y_1542_ = v_ref_1554_;
v___y_1543_ = v_fileName_1551_;
v___y_1544_ = v_suppressElabErrors_1555_;
v___y_1545_ = v_fileMap_1552_;
v___y_1546_ = v___f_1558_;
v___y_1547_ = v___y_1550_;
v___y_1548_ = v___x_1562_;
goto v___jp_1541_;
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_msgData_1448_);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1567_, lean_object* v_msgData_1568_, lean_object* v_severity_1569_, lean_object* v_isSilent_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v_severity_boxed_1576_; uint8_t v_isSilent_boxed_1577_; lean_object* v_res_1578_; 
v_severity_boxed_1576_ = lean_unbox(v_severity_1569_);
v_isSilent_boxed_1577_ = lean_unbox(v_isSilent_1570_);
v_res_1578_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg(v_ref_1567_, v_msgData_1568_, v_severity_boxed_1576_, v_isSilent_boxed_1577_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v_ref_1567_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(lean_object* v_ref_1579_, lean_object* v_msgData_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = 1;
v___x_1591_ = 0;
v___x_1592_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg(v_ref_1579_, v_msgData_1580_, v___x_1590_, v___x_1591_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(lean_object* v_ref_1593_, lean_object* v_msgData_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_ref_1593_, v_msgData_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v_ref_1593_);
return v_res_1604_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_linterOption_1611_, lean_object* v_stx_1612_, lean_object* v_msg_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_name_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1641_; 
v_name_1623_ = lean_ctor_get(v_linterOption_1611_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_linterOption_1611_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v_linterOption_1611_, 1);
lean_dec(v_unused_1642_);
v___x_1625_ = v_linterOption_1611_;
v_isShared_1626_ = v_isSharedCheck_1641_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_name_1623_);
lean_dec(v_linterOption_1611_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1641_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1627_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
lean_inc(v_name_1623_);
v___x_1628_ = l_Lean_MessageData_ofName(v_name_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 7);
lean_ctor_set(v___x_1625_, 1, v___x_1628_);
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1630_ = v___x_1625_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_disable_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1631_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v_disable_1633_ = l_Lean_MessageData_note(v___x_1632_);
v___x_1634_ = l_Lean_Linter_linterMessageTag;
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_msg_1613_);
lean_ctor_set(v___x_1635_, 1, v_disable_1633_);
v___x_1636_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_name_1623_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
lean_inc(v_stx_1612_);
v___x_1638_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_stx_1612_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_stx_1612_, v___x_1638_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v_stx_1612_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_linterOption_1643_, lean_object* v_stx_1644_, lean_object* v_msg_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_linterOption_1643_, v_stx_1644_, v_msg_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v_env_1660_; lean_object* v___x_1661_; lean_object* v_toEnvExtension_1662_; lean_object* v_asyncMode_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_merged_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1675_; 
v___x_1659_ = lean_st_ref_get(v___y_1657_);
v_env_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc_ref(v_env_1660_);
lean_dec(v___x_1659_);
v___x_1661_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1662_ = lean_ctor_get(v___x_1661_, 0);
v_asyncMode_1663_ = lean_ctor_get(v_toEnvExtension_1662_, 2);
v___x_1664_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1665_ = lean_box(0);
v___x_1666_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1664_, v___x_1661_, v_env_1660_, v_asyncMode_1663_, v___x_1665_);
v_merged_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1666_, 1);
lean_dec(v_unused_1676_);
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_merged_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 1, v_merged_1667_);
lean_ctor_set(v___x_1669_, 0, v_o_1656_);
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_o_1656_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_merged_1667_);
v___x_1672_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_1677_, v___y_1678_);
lean_dec(v___y_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_options_1690_; lean_object* v___x_1691_; 
v_options_1690_ = lean_ctor_get(v___y_1687_, 2);
lean_inc_ref(v_options_1690_);
v___x_1691_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_1690_, v___y_1688_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object* v___y_1702_, lean_object* v_mkInfoTree_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v_a_1711_, lean_object* v_a_x3f_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v_infoState_1715_; lean_object* v_trees_1716_; lean_object* v___x_1717_; 
v___x_1714_ = lean_st_ref_get(v___y_1702_);
v_infoState_1715_ = lean_ctor_get(v___x_1714_, 7);
lean_inc_ref(v_infoState_1715_);
lean_dec(v___x_1714_);
v_trees_1716_ = lean_ctor_get(v_infoState_1715_, 2);
lean_inc_ref(v_trees_1716_);
lean_dec_ref(v_infoState_1715_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1710_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
v___x_1717_ = lean_apply_10(v_mkInfoTree_1703_, v_trees_1716_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1702_, lean_box(0));
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1756_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1756_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1756_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v_infoState_1723_; lean_object* v_env_1724_; lean_object* v_nextMacroScope_1725_; lean_object* v_ngen_1726_; lean_object* v_auxDeclNGen_1727_; lean_object* v_traceState_1728_; lean_object* v_cache_1729_; lean_object* v_messages_1730_; lean_object* v_snapshotTasks_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1755_; 
v___x_1722_ = lean_st_ref_take(v___y_1702_);
v_infoState_1723_ = lean_ctor_get(v___x_1722_, 7);
v_env_1724_ = lean_ctor_get(v___x_1722_, 0);
v_nextMacroScope_1725_ = lean_ctor_get(v___x_1722_, 1);
v_ngen_1726_ = lean_ctor_get(v___x_1722_, 2);
v_auxDeclNGen_1727_ = lean_ctor_get(v___x_1722_, 3);
v_traceState_1728_ = lean_ctor_get(v___x_1722_, 4);
v_cache_1729_ = lean_ctor_get(v___x_1722_, 5);
v_messages_1730_ = lean_ctor_get(v___x_1722_, 6);
v_snapshotTasks_1731_ = lean_ctor_get(v___x_1722_, 8);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1733_ = v___x_1722_;
v_isShared_1734_ = v_isSharedCheck_1755_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_snapshotTasks_1731_);
lean_inc(v_infoState_1723_);
lean_inc(v_messages_1730_);
lean_inc(v_cache_1729_);
lean_inc(v_traceState_1728_);
lean_inc(v_auxDeclNGen_1727_);
lean_inc(v_ngen_1726_);
lean_inc(v_nextMacroScope_1725_);
lean_inc(v_env_1724_);
lean_dec(v___x_1722_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1755_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
uint8_t v_enabled_1735_; lean_object* v_assignment_1736_; lean_object* v_lazyAssignment_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1753_; 
v_enabled_1735_ = lean_ctor_get_uint8(v_infoState_1723_, sizeof(void*)*3);
v_assignment_1736_ = lean_ctor_get(v_infoState_1723_, 0);
v_lazyAssignment_1737_ = lean_ctor_get(v_infoState_1723_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_infoState_1723_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v_infoState_1723_, 2);
lean_dec(v_unused_1754_);
v___x_1739_ = v_infoState_1723_;
v_isShared_1740_ = v_isSharedCheck_1753_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_lazyAssignment_1737_);
lean_inc(v_assignment_1736_);
lean_dec(v_infoState_1723_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1753_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1741_ = l_Lean_PersistentArray_push___redArg(v_a_1711_, v_a_1718_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 2, v___x_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_assignment_1736_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_lazyAssignment_1737_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v___x_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1752_, sizeof(void*)*3, v_enabled_1735_);
v___x_1743_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 7, v___x_1743_);
v___x_1745_ = v___x_1733_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_env_1724_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_nextMacroScope_1725_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_ngen_1726_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v_auxDeclNGen_1727_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v_traceState_1728_);
lean_ctor_set(v_reuseFailAlloc_1751_, 5, v_cache_1729_);
lean_ctor_set(v_reuseFailAlloc_1751_, 6, v_messages_1730_);
lean_ctor_set(v_reuseFailAlloc_1751_, 7, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1751_, 8, v_snapshotTasks_1731_);
v___x_1745_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = lean_st_ref_put(v___y_1702_, v___x_1745_);
v___x_1747_ = lean_box(0);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1747_);
v___x_1749_ = v___x_1720_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v_a_1711_);
v_a_1757_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1717_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1717_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object* v___y_1765_, lean_object* v_mkInfoTree_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v_a_1774_, lean_object* v_a_x3f_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1765_, v_mkInfoTree_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v_a_1774_, v_a_x3f_1775_);
lean_dec(v_a_x3f_1775_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1765_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object* v_x_1778_, lean_object* v_mkInfoTree_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; lean_object* v_infoState_1790_; uint8_t v_enabled_1791_; 
v___x_1789_ = lean_st_ref_get(v___y_1787_);
v_infoState_1790_ = lean_ctor_get(v___x_1789_, 7);
lean_inc_ref(v_infoState_1790_);
lean_dec(v___x_1789_);
v_enabled_1791_ = lean_ctor_get_uint8(v_infoState_1790_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1790_);
if (v_enabled_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_dec_ref(v_mkInfoTree_1779_);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
v___x_1792_ = lean_apply_9(v_x_1778_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, lean_box(0));
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v_a_1794_; lean_object* v_r_1795_; 
v___x_1793_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1787_);
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1793_);
lean_inc(v___y_1787_);
lean_inc_ref(v___y_1786_);
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
v_r_1795_ = lean_apply_9(v_x_1778_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, lean_box(0));
if (lean_obj_tag(v_r_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1820_; 
v_a_1796_ = lean_ctor_get(v_r_1795_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_r_1795_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1798_ = v_r_1795_;
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v_r_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
lean_inc(v_a_1796_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 1);
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1787_, v_mkInfoTree_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v_a_1794_, v___x_1801_);
lean_dec_ref(v___x_1801_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1802_, 0);
lean_dec(v_unused_1810_);
v___x_1804_ = v___x_1802_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_dec(v___x_1802_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_a_1796_);
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1796_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_a_1796_);
v_a_1811_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1802_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1802_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1821_ = lean_ctor_get(v_r_1795_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v_r_1795_, 1);
v___x_1822_ = lean_box(0);
v___x_1823_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1787_, v_mkInfoTree_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v_a_1794_, v___x_1822_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v___x_1823_, 0);
lean_dec(v_unused_1831_);
v___x_1825_ = v___x_1823_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_dec(v___x_1823_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 1);
lean_ctor_set(v___x_1825_, 0, v_a_1821_);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1821_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1821_);
v_a_1832_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1823_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object* v_x_1840_, lean_object* v_mkInfoTree_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_1840_, v_mkInfoTree_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v_res_1851_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2));
v___x_1857_ = l_Lean_stringToMessageData(v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4));
v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
return v___x_1860_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6));
v___x_1863_ = l_Lean_stringToMessageData(v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8));
v___x_1866_ = l_Lean_stringToMessageData(v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10));
v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_usingArg_1873_, lean_object* v_snd_1874_, uint8_t v___x_1875_, uint8_t v___x_1876_, lean_object* v___x_1877_, uint8_t v_useReducible_1878_, uint8_t v___x_1879_, lean_object* v___x_1880_, lean_object* v___x_1881_, lean_object* v_simprocs_1882_, lean_object* v_discharge_x3f_1883_, lean_object* v_snd_1884_, lean_object* v___x_1885_, lean_object* v___f_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; 
if (lean_obj_tag(v_usingArg_1873_) == 1)
{
lean_object* v_val_2077_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___x_2129_; lean_object* v_infoState_2130_; uint8_t v_enabled_2131_; 
v_val_2077_ = lean_ctor_get(v_usingArg_1873_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v_usingArg_1873_, 1);
v___x_2129_ = lean_st_ref_get(v___y_1894_);
v_infoState_2130_ = lean_ctor_get(v___x_2129_, 7);
lean_inc_ref(v_infoState_2130_);
lean_dec(v___x_2129_);
v_enabled_2131_ = lean_ctor_get_uint8(v_infoState_2130_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2130_);
if (v_enabled_2131_ == 0)
{
lean_dec_ref(v___f_1886_);
v___y_2079_ = v___y_1887_;
v___y_2080_ = v___y_1888_;
v___y_2081_ = v___y_1889_;
v___y_2082_ = v___y_1890_;
v___y_2083_ = v___y_1891_;
v___y_2084_ = v___y_1892_;
v___y_2085_ = v___y_1893_;
v___y_2086_ = v___y_1894_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2132_; lean_object* v_a_2133_; lean_object* v___f_2134_; lean_object* v___x_2135_; 
v___x_2132_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1894_);
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
v___f_2134_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2134_, 0, v_a_2133_);
v___x_2135_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_2134_, v___f_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref_known(v___x_2135_, 1);
v___y_2079_ = v___y_1887_;
v___y_2080_ = v___y_1888_;
v___y_2081_ = v___y_1889_;
v___y_2082_ = v___y_1890_;
v___y_2083_ = v___y_1891_;
v___y_2084_ = v___y_1892_;
v___y_2085_ = v___y_1893_;
v___y_2086_ = v___y_1894_;
goto v___jp_2078_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_val_2077_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
v___jp_2078_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = lean_st_ref_get(v___y_2084_);
v___x_2088_ = lean_box(0);
v___x_2089_ = l_Lean_Elab_Tactic_elabTerm(v_val_2077_, v___x_2088_, v___x_1875_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc_n(v_a_2090_, 2);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_1874_, v_a_2090_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_mctx_2092_; lean_object* v_a_2093_; uint8_t v___x_2094_; 
v_mctx_2092_ = lean_ctor_get(v___x_2087_, 0);
lean_inc_ref(v_mctx_2092_);
lean_dec(v___x_2087_);
v_a_2093_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2094_ = lean_unbox(v_a_2093_);
lean_dec(v_a_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_mctx_2092_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
v___x_2095_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
v___x_2096_ = l_Lean_indentExpr(v_a_2090_);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
v___x_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = l_Lean_Expr_mvar___override(v_snd_1874_);
v___x_2101_ = l_Lean_MessageData_ofExpr(v___x_2100_);
v___x_2102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2099_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_2102_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_mvarCounter_2112_; 
v_mvarCounter_2112_ = lean_ctor_get(v_mctx_2092_, 3);
lean_inc(v_mvarCounter_2112_);
lean_dec_ref(v_mctx_2092_);
lean_inc(v_a_2090_);
v___y_1961_ = v_a_2090_;
v___y_1962_ = v_mvarCounter_2112_;
v___y_1963_ = v___x_2088_;
v___y_1964_ = v___x_2088_;
v___y_1965_ = v_a_2090_;
v___y_1966_ = v___y_2079_;
v___y_1967_ = v___y_2080_;
v___y_1968_ = v___y_2081_;
v___y_1969_ = v___y_2082_;
v___y_1970_ = v___y_2083_;
v___y_1971_ = v___y_2084_;
v___y_1972_ = v___y_2085_;
v___y_1973_ = v___y_2086_;
goto v___jp_1960_;
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_a_2090_);
lean_dec(v___x_2087_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2113_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2091_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2091_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v___x_2087_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2121_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2089_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2089_);
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
else
{
lean_object* v_lctx_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v___f_1886_);
lean_dec_ref(v___x_1877_);
lean_dec(v_usingArg_1873_);
v_lctx_2144_ = lean_ctor_get(v___y_1891_, 2);
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13));
v___x_2146_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2144_, v___x_2145_);
if (lean_obj_tag(v___x_2146_) == 1)
{
lean_object* v_val_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_val_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_val_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = l_Lean_LocalDecl_fvarId(v_val_2147_);
lean_dec(v_val_2147_);
v___x_2149_ = lean_mk_empty_array_with_capacity(v___x_1880_);
v___x_2150_ = lean_array_push(v___x_2149_, v___x_2148_);
lean_inc_ref(v_snd_1884_);
v___x_2151_ = l_Lean_Meta_simpGoal(v_snd_1874_, v___x_1881_, v_simprocs_1882_, v_discharge_x3f_1883_, v___x_1876_, v___x_2150_, v_snd_1884_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2180_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2180_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2180_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_fst_2156_; 
v_fst_2156_ = lean_ctor_get(v_a_2152_, 0);
if (lean_obj_tag(v_fst_2156_) == 1)
{
lean_object* v_val_2157_; lean_object* v_snd_2158_; lean_object* v_snd_2159_; lean_object* v___x_2160_; 
lean_del_object(v___x_2154_);
lean_dec_ref(v_snd_1884_);
v_val_2157_ = lean_ctor_get(v_fst_2156_, 0);
lean_inc(v_val_2157_);
v_snd_2158_ = lean_ctor_get(v_a_2152_, 1);
lean_inc(v_snd_2158_);
lean_dec(v_a_2152_);
v_snd_2159_ = lean_ctor_get(v_val_2157_, 1);
lean_inc(v_snd_2159_);
lean_dec(v_val_2157_);
v___x_2160_ = l_Lean_MVarId_assumption(v_snd_2159_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; 
v_unused_2168_ = lean_ctor_get(v___x_2160_, 0);
lean_dec(v_unused_2168_);
v___x_2162_ = v___x_2160_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_dec(v___x_2160_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v_snd_2158_);
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_snd_2158_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_snd_2158_);
v_a_2169_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2160_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2160_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v___x_2178_; 
lean_dec(v_a_2152_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v_snd_1884_);
v___x_2178_ = v___x_2154_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_snd_1884_);
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
lean_dec_ref(v_snd_1884_);
v_a_2181_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2151_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2151_);
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
else
{
lean_object* v___x_2189_; 
lean_dec(v___x_2146_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
v___x_2189_ = l_Lean_MVarId_assumption(v_snd_1874_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v___x_2189_, 0);
lean_dec(v_unused_2197_);
v___x_2191_ = v___x_2189_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v___x_2189_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v_snd_1884_);
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_snd_1884_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_snd_1884_);
v_a_2198_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2189_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2189_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
v___jp_1896_:
{
lean_object* v___x_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v___x_1900_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_1874_, v___y_1898_, v___y_1899_);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1907_ == 0)
{
lean_object* v_unused_1908_; 
v_unused_1908_ = lean_ctor_get(v___x_1900_, 0);
lean_dec(v_unused_1908_);
v___x_1902_ = v___x_1900_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v___x_1900_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___y_1897_);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___y_1897_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
v___jp_1909_:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_Core_mkFreshUserName(v___y_1919_, v___y_1915_, v___y_1917_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_n(v_a_1927_, 2);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1928_ = l_Lean_MVarId_rename(v___y_1923_, v___y_1925_, v_a_1927_, v___y_1922_, v___y_1913_, v___y_1915_, v___y_1917_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_n(v_a_1929_, 2);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = lean_box(v___x_1875_);
v___x_1931_ = lean_box(v___x_1876_);
v___x_1932_ = lean_box(v_useReducible_1878_);
v___x_1933_ = lean_box(v___x_1879_);
v___f_1934_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 19, 10);
lean_closure_set(v___f_1934_, 0, v_a_1929_);
lean_closure_set(v___f_1934_, 1, v_a_1927_);
lean_closure_set(v___f_1934_, 2, v___x_1930_);
lean_closure_set(v___f_1934_, 3, v___x_1931_);
lean_closure_set(v___f_1934_, 4, v___y_1910_);
lean_closure_set(v___f_1934_, 5, v___y_1912_);
lean_closure_set(v___f_1934_, 6, v___x_1877_);
lean_closure_set(v___f_1934_, 7, v___y_1911_);
lean_closure_set(v___f_1934_, 8, v___x_1932_);
lean_closure_set(v___f_1934_, 9, v___x_1933_);
v___x_1935_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1929_, v___f_1934_, v___y_1920_, v___y_1918_, v___y_1916_, v___y_1924_, v___y_1922_, v___y_1913_, v___y_1915_, v___y_1917_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v___y_1897_ = v___y_1914_;
v___y_1898_ = v___y_1921_;
v___y_1899_ = v___y_1913_;
goto v___jp_1896_;
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v___y_1921_);
lean_dec_ref(v___y_1914_);
lean_dec(v_snd_1874_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
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
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_a_1927_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_1944_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1928_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1928_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v___y_1925_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_1952_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1926_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1926_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
v___jp_1960_:
{
lean_object* v___x_1974_; 
lean_inc(v_snd_1874_);
v___x_1974_ = l_Lean_MVarId_getType(v_snd_1874_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
lean_inc(v_snd_1874_);
v___x_1976_ = l_Lean_MVarId_getTag(v_snd_1874_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1975_, v_a_1977_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l_Lean_Expr_mvarId_x21(v_a_1979_);
v___x_1981_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1));
lean_inc_ref(v___y_1965_);
v___x_1982_ = l_Lean_MVarId_note(v___x_1980_, v___x_1981_, v___y_1965_, v___y_1964_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2044_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v_fst_1984_ = lean_ctor_get(v_a_1983_, 0);
v_snd_1985_ = lean_ctor_get(v_a_1983_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_1987_ = v_a_1983_;
v_isShared_1988_ = v_isSharedCheck_2044_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snd_1985_);
lean_inc(v_fst_1984_);
lean_dec(v_a_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2044_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_mk_empty_array_with_capacity(v___x_1880_);
lean_inc(v_fst_1984_);
v___x_1990_ = lean_array_push(v___x_1989_, v_fst_1984_);
v___x_1991_ = l_Lean_Meta_simpGoal(v_snd_1985_, v___x_1881_, v_simprocs_1882_, v_discharge_x3f_1883_, v___x_1876_, v___x_1990_, v_snd_1884_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v_fst_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v_fst_1993_ = lean_ctor_get(v_a_1992_, 0);
if (lean_obj_tag(v_fst_1993_) == 0)
{
lean_object* v_snd_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_fst_1984_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec_ref(v___x_1877_);
v_snd_1994_ = lean_ctor_get(v_a_1992_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v_a_1992_, 0);
lean_dec(v_unused_2028_);
v___x_1996_ = v_a_1992_;
v_isShared_1997_ = v_isSharedCheck_2027_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_snd_1994_);
lean_dec(v_a_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2027_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v_a_1999_; uint8_t v___x_2000_; 
v___x_1998_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1999_);
lean_dec(v_a_1999_);
if (v___x_2000_ == 0)
{
lean_del_object(v___x_1996_);
lean_del_object(v___x_1987_);
lean_dec_ref(v___y_1965_);
v___y_1897_ = v_snd_1994_;
v___y_1898_ = v_a_1979_;
v___y_1899_ = v___y_1971_;
goto v___jp_1896_;
}
else
{
if (lean_obj_tag(v___y_1965_) == 1)
{
lean_object* v_fvarId_2001_; lean_object* v_lctx_2002_; lean_object* v___x_2003_; 
v_fvarId_2001_ = lean_ctor_get(v___y_1965_, 0);
v_lctx_2002_ = lean_ctor_get(v___y_1970_, 2);
lean_inc(v_fvarId_2001_);
lean_inc_ref(v_lctx_2002_);
v___x_2003_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2002_, v_fvarId_2001_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_dec_ref_known(v___y_1965_, 1);
lean_del_object(v___x_1996_);
lean_del_object(v___x_1987_);
v___y_1897_ = v_snd_1994_;
v___y_1898_ = v_a_1979_;
v___y_1899_ = v___y_1971_;
goto v___jp_1896_;
}
else
{
lean_dec_ref_known(v___x_2003_, 1);
if (v___x_1879_ == 0)
{
lean_dec_ref_known(v___y_1965_, 1);
lean_del_object(v___x_1996_);
lean_del_object(v___x_1987_);
v___y_1897_ = v_snd_1994_;
v___y_1898_ = v_a_1979_;
v___y_1899_ = v___y_1971_;
goto v___jp_1896_;
}
else
{
lean_object* v_ref_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v_ref_2004_ = lean_ctor_get(v___y_1972_, 5);
v___x_2005_ = l_Lean_linter_unnecessarySimpa;
v___x_2006_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_2007_ = l_Lean_MessageData_ofExpr(v___y_1965_);
lean_inc_ref(v___x_2007_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 7);
lean_ctor_set(v___x_1996_, 1, v___x_2007_);
lean_ctor_set(v___x_1996_, 0, v___x_2006_);
v___x_2009_ = v___x_1996_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 7);
lean_ctor_set(v___x_1987_, 1, v___x_2010_);
lean_ctor_set(v___x_1987_, 0, v___x_2009_);
v___x_2012_ = v___x_1987_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v___x_2007_);
v___x_2014_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
v___x_2015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
lean_inc(v_ref_2004_);
v___x_2016_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2005_, v_ref_2004_, v___x_2015_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_dec_ref_known(v___x_2016_, 1);
v___y_1897_ = v_snd_1994_;
v___y_1898_ = v_a_1979_;
v___y_1899_ = v___y_1971_;
goto v___jp_1896_;
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_snd_1994_);
lean_dec(v_a_1979_);
lean_dec(v_snd_1874_);
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
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
}
}
}
else
{
lean_del_object(v___x_1996_);
lean_del_object(v___x_1987_);
lean_dec_ref(v___y_1965_);
v___y_1897_ = v_snd_1994_;
v___y_1898_ = v_a_1979_;
v___y_1899_ = v___y_1971_;
goto v___jp_1896_;
}
}
}
}
else
{
lean_object* v_val_2029_; lean_object* v_snd_2030_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
lean_del_object(v___x_1987_);
lean_dec_ref(v___y_1965_);
v_val_2029_ = lean_ctor_get(v_fst_1993_, 0);
lean_inc(v_val_2029_);
v_snd_2030_ = lean_ctor_get(v_a_1992_, 1);
lean_inc(v_snd_2030_);
lean_dec(v_a_1992_);
v_fst_2031_ = lean_ctor_get(v_val_2029_, 0);
lean_inc(v_fst_2031_);
v_snd_2032_ = lean_ctor_get(v_val_2029_, 1);
lean_inc(v_snd_2032_);
lean_dec(v_val_2029_);
v___x_2033_ = lean_array_get_size(v_fst_2031_);
v___x_2034_ = lean_nat_dec_lt(v___x_1885_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_dec(v_fst_2031_);
v___y_1910_ = v___y_1961_;
v___y_1911_ = v___y_1963_;
v___y_1912_ = v___y_1962_;
v___y_1913_ = v___y_1971_;
v___y_1914_ = v_snd_2030_;
v___y_1915_ = v___y_1972_;
v___y_1916_ = v___y_1968_;
v___y_1917_ = v___y_1973_;
v___y_1918_ = v___y_1967_;
v___y_1919_ = v___x_1981_;
v___y_1920_ = v___y_1966_;
v___y_1921_ = v_a_1979_;
v___y_1922_ = v___y_1970_;
v___y_1923_ = v_snd_2032_;
v___y_1924_ = v___y_1969_;
v___y_1925_ = v_fst_1984_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_2035_; 
lean_dec(v_fst_1984_);
v___x_2035_ = lean_array_fget(v_fst_2031_, v___x_1885_);
lean_dec(v_fst_2031_);
v___y_1910_ = v___y_1961_;
v___y_1911_ = v___y_1963_;
v___y_1912_ = v___y_1962_;
v___y_1913_ = v___y_1971_;
v___y_1914_ = v_snd_2030_;
v___y_1915_ = v___y_1972_;
v___y_1916_ = v___y_1968_;
v___y_1917_ = v___y_1973_;
v___y_1918_ = v___y_1967_;
v___y_1919_ = v___x_1981_;
v___y_1920_ = v___y_1966_;
v___y_1921_ = v_a_1979_;
v___y_1922_ = v___y_1970_;
v___y_1923_ = v_snd_2032_;
v___y_1924_ = v___y_1969_;
v___y_1925_ = v___x_2035_;
goto v___jp_1909_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_del_object(v___x_1987_);
lean_dec(v_fst_1984_);
lean_dec(v_a_1979_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2036_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_1991_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_1991_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_1979_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2045_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_1982_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_1982_);
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
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2053_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_1978_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_1978_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_1975_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2061_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_1976_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_1976_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec_ref(v_snd_1884_);
lean_dec(v_discharge_x3f_1883_);
lean_dec_ref(v_simprocs_1882_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___x_1877_);
lean_dec(v_snd_1874_);
v_a_2069_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_1974_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_1974_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2206_ = _args[0];
lean_object* v_snd_2207_ = _args[1];
lean_object* v___x_2208_ = _args[2];
lean_object* v___x_2209_ = _args[3];
lean_object* v___x_2210_ = _args[4];
lean_object* v_useReducible_2211_ = _args[5];
lean_object* v___x_2212_ = _args[6];
lean_object* v___x_2213_ = _args[7];
lean_object* v___x_2214_ = _args[8];
lean_object* v_simprocs_2215_ = _args[9];
lean_object* v_discharge_x3f_2216_ = _args[10];
lean_object* v_snd_2217_ = _args[11];
lean_object* v___x_2218_ = _args[12];
lean_object* v___f_2219_ = _args[13];
lean_object* v___y_2220_ = _args[14];
lean_object* v___y_2221_ = _args[15];
lean_object* v___y_2222_ = _args[16];
lean_object* v___y_2223_ = _args[17];
lean_object* v___y_2224_ = _args[18];
lean_object* v___y_2225_ = _args[19];
lean_object* v___y_2226_ = _args[20];
lean_object* v___y_2227_ = _args[21];
lean_object* v___y_2228_ = _args[22];
_start:
{
uint8_t v___x_95467__boxed_2229_; uint8_t v___x_95468__boxed_2230_; uint8_t v_useReducible_boxed_2231_; uint8_t v___x_95470__boxed_2232_; lean_object* v_res_2233_; 
v___x_95467__boxed_2229_ = lean_unbox(v___x_2208_);
v___x_95468__boxed_2230_ = lean_unbox(v___x_2209_);
v_useReducible_boxed_2231_ = lean_unbox(v_useReducible_2211_);
v___x_95470__boxed_2232_ = lean_unbox(v___x_2212_);
v_res_2233_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2206_, v_snd_2207_, v___x_95467__boxed_2229_, v___x_95468__boxed_2230_, v___x_2210_, v_useReducible_boxed_2231_, v___x_95470__boxed_2232_, v___x_2213_, v___x_2214_, v_simprocs_2215_, v_discharge_x3f_2216_, v_snd_2217_, v___x_2218_, v___f_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___x_2218_);
lean_dec(v___x_2213_);
return v_res_2233_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2234_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = lean_unsigned_to_nat(32u);
v___x_2238_ = lean_mk_empty_array_with_capacity(v___x_2237_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2244_ = l_Lean_MessageData_ofFormat(v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v___x_2245_, lean_object* v_tk_2246_, lean_object* v___x_2247_, lean_object* v___x_2248_, lean_object* v___x_2249_, lean_object* v_simprocs_2250_, uint8_t v___x_2251_, lean_object* v_usingArg_2252_, uint8_t v___x_2253_, lean_object* v___x_2254_, uint8_t v_useReducible_2255_, uint8_t v___x_2256_, lean_object* v___x_2257_, lean_object* v_usingTk_x3f_2258_, lean_object* v_discharge_x3f_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___y_2270_; 
if (lean_obj_tag(v_usingTk_x3f_2258_) == 0)
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_box(0);
v___y_2270_ = v___x_2375_;
goto v___jp_2269_;
}
else
{
lean_object* v_val_2376_; 
v_val_2376_ = lean_ctor_get(v_usingTk_x3f_2258_, 0);
lean_inc(v_val_2376_);
lean_dec_ref_known(v_usingTk_x3f_2258_, 1);
v___y_2270_ = v_val_2376_;
goto v___jp_2269_;
}
v___jp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2271_ = lean_mk_empty_array_with_capacity(v___x_2245_);
v___x_2272_ = lean_array_push(v___x_2271_, v_tk_2246_);
v___x_2273_ = lean_array_push(v___x_2272_, v___y_2270_);
v___x_2274_ = lean_box(2);
v___x_2275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2247_);
lean_ctor_set(v___x_2275_, 2, v___x_2273_);
v___x_2276_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2275_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2261_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; size_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = lean_mk_empty_array_with_capacity(v___x_2248_);
v___x_2281_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
lean_inc_n(v___x_2248_, 3);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2248_);
v___x_2283_ = lean_unsigned_to_nat(32u);
v___x_2284_ = lean_mk_empty_array_with_capacity(v___x_2283_);
v___x_2285_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
v___x_2286_ = ((size_t)5ULL);
v___x_2287_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2287_, 0, v___x_2285_);
lean_ctor_set(v___x_2287_, 1, v___x_2284_);
lean_ctor_set(v___x_2287_, 2, v___x_2248_);
lean_ctor_set(v___x_2287_, 3, v___x_2248_);
lean_ctor_set_usize(v___x_2287_, 4, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2281_);
lean_ctor_set(v___x_2288_, 1, v___x_2281_);
lean_ctor_set(v___x_2288_, 2, v___x_2281_);
lean_ctor_set(v___x_2288_, 3, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2282_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
lean_inc_ref(v___x_2289_);
lean_inc(v_discharge_x3f_2259_);
lean_inc_ref(v_simprocs_2250_);
lean_inc_ref(v___x_2249_);
v___x_2290_ = l_Lean_Meta_simpGoal(v_a_2279_, v___x_2249_, v_simprocs_2250_, v_discharge_x3f_2259_, v___x_2251_, v___x_2280_, v___x_2289_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v_fst_2292_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v_fst_2292_ = lean_ctor_get(v_a_2291_, 0);
if (lean_obj_tag(v_fst_2292_) == 1)
{
lean_object* v_val_2293_; lean_object* v_snd_2294_; lean_object* v_snd_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref_known(v___x_2289_, 2);
v_val_2293_ = lean_ctor_get(v_fst_2292_, 0);
lean_inc(v_val_2293_);
v_snd_2294_ = lean_ctor_get(v_a_2291_, 1);
lean_inc(v_snd_2294_);
lean_dec(v_a_2291_);
v_snd_2295_ = lean_ctor_get(v_val_2293_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_val_2293_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_val_2293_, 0);
lean_dec(v_unused_2320_);
v___x_2297_ = v_val_2293_;
v_isShared_2298_ = v_isSharedCheck_2319_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_snd_2295_);
lean_dec(v_val_2293_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2319_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2299_ = lean_box(0);
lean_inc(v_snd_2295_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set_tag(v___x_2297_, 1);
lean_ctor_set(v___x_2297_, 1, v___x_2299_);
lean_ctor_set(v___x_2297_, 0, v_snd_2295_);
v___x_2301_ = v___x_2297_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_snd_2295_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2301_, v___y_2261_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___f_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___y_2308_; lean_object* v___x_2309_; 
lean_dec_ref_known(v___x_2302_, 1);
v___f_2303_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2303_, 0, v_a_2277_);
v___x_2304_ = lean_box(v___x_2251_);
v___x_2305_ = lean_box(v___x_2253_);
v___x_2306_ = lean_box(v_useReducible_2255_);
v___x_2307_ = lean_box(v___x_2256_);
lean_inc(v_snd_2295_);
v___y_2308_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 23, 14);
lean_closure_set(v___y_2308_, 0, v_usingArg_2252_);
lean_closure_set(v___y_2308_, 1, v_snd_2295_);
lean_closure_set(v___y_2308_, 2, v___x_2304_);
lean_closure_set(v___y_2308_, 3, v___x_2305_);
lean_closure_set(v___y_2308_, 4, v___x_2254_);
lean_closure_set(v___y_2308_, 5, v___x_2306_);
lean_closure_set(v___y_2308_, 6, v___x_2307_);
lean_closure_set(v___y_2308_, 7, v___x_2257_);
lean_closure_set(v___y_2308_, 8, v___x_2249_);
lean_closure_set(v___y_2308_, 9, v_simprocs_2250_);
lean_closure_set(v___y_2308_, 10, v_discharge_x3f_2259_);
lean_closure_set(v___y_2308_, 11, v_snd_2294_);
lean_closure_set(v___y_2308_, 12, v___x_2248_);
lean_closure_set(v___y_2308_, 13, v___f_2303_);
v___x_2309_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_2295_, v___y_2308_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2309_;
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_snd_2295_);
lean_dec(v_snd_2294_);
lean_dec(v_a_2277_);
lean_dec(v_discharge_x3f_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_usingArg_2252_);
lean_dec_ref(v_simprocs_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2248_);
v_a_2310_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2302_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2302_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
else
{
lean_object* v___x_2321_; lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2291_);
lean_dec(v_a_2277_);
lean_dec(v_discharge_x3f_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_usingArg_2252_);
lean_dec_ref(v_simprocs_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2248_);
v___x_2321_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2350_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2350_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
uint8_t v___x_2326_; 
v___x_2326_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2322_);
lean_dec(v_a_2322_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2328_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2289_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2289_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
else
{
lean_object* v_ref_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_del_object(v___x_2324_);
v_ref_2330_ = lean_ctor_get(v___y_2266_, 5);
v___x_2331_ = l_Lean_linter_unnecessarySimpa;
v___x_2332_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
lean_inc(v_ref_2330_);
v___x_2333_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2331_, v_ref_2330_, v___x_2332_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v___x_2333_, 0);
lean_dec(v_unused_2341_);
v___x_2335_ = v___x_2333_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v___x_2333_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2289_);
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2289_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref_known(v___x_2289_, 2);
v_a_2342_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2333_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2333_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec_ref_known(v___x_2289_, 2);
lean_dec(v_a_2277_);
lean_dec(v_discharge_x3f_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_usingArg_2252_);
lean_dec_ref(v_simprocs_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2248_);
v_a_2351_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2290_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2290_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec(v_a_2277_);
lean_dec(v_discharge_x3f_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_usingArg_2252_);
lean_dec_ref(v_simprocs_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2248_);
v_a_2359_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2278_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2278_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_discharge_x3f_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_usingArg_2252_);
lean_dec_ref(v_simprocs_2250_);
lean_dec_ref(v___x_2249_);
lean_dec(v___x_2248_);
v_a_2367_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2276_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2276_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v___x_2377_ = _args[0];
lean_object* v_tk_2378_ = _args[1];
lean_object* v___x_2379_ = _args[2];
lean_object* v___x_2380_ = _args[3];
lean_object* v___x_2381_ = _args[4];
lean_object* v_simprocs_2382_ = _args[5];
lean_object* v___x_2383_ = _args[6];
lean_object* v_usingArg_2384_ = _args[7];
lean_object* v___x_2385_ = _args[8];
lean_object* v___x_2386_ = _args[9];
lean_object* v_useReducible_2387_ = _args[10];
lean_object* v___x_2388_ = _args[11];
lean_object* v___x_2389_ = _args[12];
lean_object* v_usingTk_x3f_2390_ = _args[13];
lean_object* v_discharge_x3f_2391_ = _args[14];
lean_object* v___y_2392_ = _args[15];
lean_object* v___y_2393_ = _args[16];
lean_object* v___y_2394_ = _args[17];
lean_object* v___y_2395_ = _args[18];
lean_object* v___y_2396_ = _args[19];
lean_object* v___y_2397_ = _args[20];
lean_object* v___y_2398_ = _args[21];
lean_object* v___y_2399_ = _args[22];
lean_object* v___y_2400_ = _args[23];
_start:
{
uint8_t v___x_96191__boxed_2401_; uint8_t v___x_96192__boxed_2402_; uint8_t v_useReducible_boxed_2403_; uint8_t v___x_96194__boxed_2404_; lean_object* v_res_2405_; 
v___x_96191__boxed_2401_ = lean_unbox(v___x_2383_);
v___x_96192__boxed_2402_ = lean_unbox(v___x_2385_);
v_useReducible_boxed_2403_ = lean_unbox(v_useReducible_2387_);
v___x_96194__boxed_2404_ = lean_unbox(v___x_2388_);
v_res_2405_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2377_, v_tk_2378_, v___x_2379_, v___x_2380_, v___x_2381_, v_simprocs_2382_, v___x_96191__boxed_2401_, v_usingArg_2384_, v___x_96192__boxed_2402_, v___x_2386_, v_useReducible_boxed_2403_, v___x_96194__boxed_2404_, v___x_2389_, v_usingTk_x3f_2390_, v_discharge_x3f_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___x_2377_);
return v_res_2405_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2414_ = lean_unsigned_to_nat(38u);
v___x_2415_ = lean_unsigned_to_nat(130u);
v___x_2416_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2418_ = l_mkPanicMessageWithDecl(v___x_2417_, v___x_2416_, v___x_2415_, v___x_2414_, v___x_2413_);
return v___x_2418_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Array_mkArray0(lean_box(0));
return v___x_2423_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2436_ = lean_unsigned_to_nat(15u);
v___x_2437_ = lean_unsigned_to_nat(131u);
v___x_2438_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2440_ = l_mkPanicMessageWithDecl(v___x_2439_, v___x_2438_, v___x_2437_, v___x_2436_, v___x_2435_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2442_, lean_object* v___x_2443_, lean_object* v___x_2444_, lean_object* v___x_2445_, lean_object* v___x_2446_, uint8_t v___x_2447_, lean_object* v___x_2448_, lean_object* v___x_2449_, uint8_t v_useReducible_2450_, lean_object* v___f_2451_, lean_object* v___x_2452_, lean_object* v___x_2453_, lean_object* v___x_2454_, lean_object* v___x_2455_, lean_object* v___x_2456_, lean_object* v___x_2457_, lean_object* v_usingArg_2458_, lean_object* v___x_2459_, uint8_t v___x_2460_, lean_object* v_usingTk_x3f_2461_, lean_object* v_squeeze_2462_, lean_object* v_unfold_2463_, lean_object* v_args_2464_, lean_object* v_only_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___y_2477_; lean_object* v___y_2481_; lean_object* v_stx_2482_; lean_object* v___y_2483_; lean_object* v_ref_2484_; lean_object* v___y_2485_; lean_object* v___y_2504_; lean_object* v_stx_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v_options_2530_; lean_object* v_ref_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; uint8_t v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v___y_2946_; lean_object* v_args_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; uint8_t v___y_2985_; lean_object* v___y_2986_; lean_object* v_only_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_3015_; lean_object* v___y_3016_; uint8_t v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3075_; lean_object* v___y_3076_; uint8_t v___y_3077_; lean_object* v___y_3088_; lean_object* v___y_3089_; uint8_t v___y_3090_; uint8_t v___y_3091_; lean_object* v___y_3093_; lean_object* v___y_3094_; uint8_t v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3165_; 
v_options_2530_ = lean_ctor_get(v___y_2473_, 2);
v_ref_2531_ = lean_ctor_get(v___y_2473_, 5);
v___x_2532_ = 0;
v___x_2533_ = l_Lean_SourceInfo_fromRef(v_ref_2531_, v___x_2532_);
v___x_2534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7));
lean_inc_ref(v___x_2445_);
lean_inc_ref(v___x_2444_);
lean_inc_ref(v___x_2443_);
v___x_2535_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2534_);
lean_inc(v___x_2533_);
v___x_2536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2533_);
lean_ctor_set(v___x_2536_, 1, v___x_2534_);
v___x_2537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_2538_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_2466_) == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_3165_ = v___x_3174_;
goto v___jp_3164_;
}
else
{
lean_object* v_val_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_val_3175_ = lean_ctor_get(v___y_2466_, 0);
lean_inc(v_val_3175_);
lean_dec_ref_known(v___y_2466_, 1);
v___x_3176_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_3177_ = lean_array_push(v___x_3176_, v_val_3175_);
v___y_3165_ = v___x_3177_;
goto v___jp_3164_;
}
v___jp_2476_:
{
lean_object* v_diag_2478_; lean_object* v___x_2479_; 
v_diag_2478_ = lean_ctor_get(v___y_2477_, 1);
lean_inc_ref(v_diag_2478_);
lean_dec_ref(v___y_2477_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v_diag_2478_);
return v___x_2479_;
}
v___jp_2480_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1));
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v_stx_2482_);
v___x_2488_ = lean_box(0);
v___x_2489_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
lean_ctor_set(v___x_2489_, 2, v___x_2488_);
lean_ctor_set(v___x_2489_, 3, v___x_2488_);
lean_ctor_set(v___x_2489_, 4, v___x_2488_);
lean_ctor_set(v___x_2489_, 5, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_ref_2484_);
v___x_2491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2));
v___x_2492_ = 4;
v___x_2493_ = l_Lean_MessageData_nil;
v___x_2494_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2442_, v___x_2489_, v___x_2490_, v___x_2491_, v___x_2488_, v___x_2492_, v___x_2493_, v___y_2483_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2483_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_dec_ref_known(v___x_2494_, 1);
v___y_2477_ = v___y_2481_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v___y_2481_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
v___jp_2503_:
{
lean_object* v_ref_2508_; 
v_ref_2508_ = lean_ctor_get(v___y_2506_, 5);
lean_inc(v_ref_2508_);
v___y_2481_ = v___y_2504_;
v_stx_2482_ = v_stx_2505_;
v___y_2483_ = v___y_2506_;
v_ref_2484_ = v_ref_2508_;
v___y_2485_ = v___y_2507_;
goto v___jp_2480_;
}
v___jp_2509_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
v___x_2520_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2519_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___y_2504_ = v___y_2510_;
v_stx_2505_ = v_a_2521_;
v___y_2506_ = v___y_2517_;
v___y_2507_ = v___y_2518_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___y_2510_);
lean_dec(v_tk_2442_);
v_a_2522_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2520_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2520_);
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
v___jp_2539_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2551_ = l_Array_append___redArg(v___x_2538_, v___y_2550_);
lean_dec_ref(v___y_2550_);
lean_inc_n(v___y_2546_, 2);
v___x_2552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2552_, 0, v___y_2546_);
lean_ctor_set(v___x_2552_, 1, v___x_2537_);
lean_ctor_set(v___x_2552_, 2, v___x_2551_);
v___x_2553_ = l_Lean_Syntax_node5(v___y_2546_, v___x_2448_, v___y_2540_, v___y_2545_, v___y_2542_, v___y_2541_, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node2(v___y_2546_, v___y_2547_, v___y_2544_, v___x_2553_);
v___y_2504_ = v___y_2543_;
v_stx_2505_ = v___x_2554_;
v___y_2506_ = v___y_2548_;
v___y_2507_ = v___y_2549_;
goto v___jp_2503_;
}
v___jp_2555_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = l_Array_append___redArg(v___x_2538_, v___y_2566_);
lean_dec_ref(v___y_2566_);
lean_inc(v___y_2562_);
v___x_2568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2568_, 0, v___y_2562_);
lean_ctor_set(v___x_2568_, 1, v___x_2537_);
lean_ctor_set(v___x_2568_, 2, v___x_2567_);
if (lean_obj_tag(v___y_2559_) == 1)
{
lean_object* v_val_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec(v___x_2446_);
v_val_2569_ = lean_ctor_get(v___y_2559_, 0);
lean_inc(v_val_2569_);
lean_dec_ref_known(v___y_2559_, 1);
v___x_2570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2562_);
v___x_2571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___y_2562_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = l_Array_mkArray2___redArg(v___x_2571_, v_val_2569_);
v___y_2540_ = v___y_2556_;
v___y_2541_ = v___x_2568_;
v___y_2542_ = v___y_2557_;
v___y_2543_ = v___y_2558_;
v___y_2544_ = v___y_2560_;
v___y_2545_ = v___y_2561_;
v___y_2546_ = v___y_2562_;
v___y_2547_ = v___y_2563_;
v___y_2548_ = v___y_2564_;
v___y_2549_ = v___y_2565_;
v___y_2550_ = v___x_2572_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2573_; 
lean_dec(v___y_2559_);
v___x_2573_ = lean_mk_empty_array_with_capacity(v___x_2446_);
lean_dec(v___x_2446_);
v___y_2540_ = v___y_2556_;
v___y_2541_ = v___x_2568_;
v___y_2542_ = v___y_2557_;
v___y_2543_ = v___y_2558_;
v___y_2544_ = v___y_2560_;
v___y_2545_ = v___y_2561_;
v___y_2546_ = v___y_2562_;
v___y_2547_ = v___y_2563_;
v___y_2548_ = v___y_2564_;
v___y_2549_ = v___y_2565_;
v___y_2550_ = v___x_2573_;
goto v___jp_2539_;
}
}
v___jp_2574_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = l_Array_append___redArg(v___x_2538_, v___y_2585_);
lean_dec_ref(v___y_2585_);
lean_inc(v___y_2581_);
v___x_2587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2587_, 0, v___y_2581_);
lean_ctor_set(v___x_2587_, 1, v___x_2537_);
lean_ctor_set(v___x_2587_, 2, v___x_2586_);
if (lean_obj_tag(v___y_2576_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_val_2588_ = lean_ctor_get(v___y_2576_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___y_2576_, 1);
v___x_2589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2590_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2589_);
v___x_2591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2581_, 4);
v___x_2592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___y_2581_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = l_Array_append___redArg(v___x_2538_, v_val_2588_);
lean_dec(v_val_2588_);
v___x_2594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___y_2581_);
lean_ctor_set(v___x_2594_, 1, v___x_2537_);
lean_ctor_set(v___x_2594_, 2, v___x_2593_);
v___x_2595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___y_2581_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = l_Lean_Syntax_node3(v___y_2581_, v___x_2590_, v___x_2592_, v___x_2594_, v___x_2596_);
v___x_2598_ = l_Array_mkArray1___redArg(v___x_2597_);
v___y_2556_ = v___y_2575_;
v___y_2557_ = v___x_2587_;
v___y_2558_ = v___y_2578_;
v___y_2559_ = v___y_2577_;
v___y_2560_ = v___y_2579_;
v___y_2561_ = v___y_2580_;
v___y_2562_ = v___y_2581_;
v___y_2563_ = v___y_2582_;
v___y_2564_ = v___y_2583_;
v___y_2565_ = v___y_2584_;
v___y_2566_ = v___x_2598_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2599_; 
lean_dec(v___y_2576_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2556_ = v___y_2575_;
v___y_2557_ = v___x_2587_;
v___y_2558_ = v___y_2578_;
v___y_2559_ = v___y_2577_;
v___y_2560_ = v___y_2579_;
v___y_2561_ = v___y_2580_;
v___y_2562_ = v___y_2581_;
v___y_2563_ = v___y_2582_;
v___y_2564_ = v___y_2583_;
v___y_2565_ = v___y_2584_;
v___y_2566_ = v___x_2599_;
goto v___jp_2555_;
}
}
v___jp_2600_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = l_Array_append___redArg(v___x_2538_, v___y_2611_);
lean_dec_ref(v___y_2611_);
lean_inc(v___y_2608_);
v___x_2613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2613_, 0, v___y_2608_);
lean_ctor_set(v___x_2613_, 1, v___x_2537_);
lean_ctor_set(v___x_2613_, 2, v___x_2612_);
if (lean_obj_tag(v___y_2605_) == 1)
{
lean_object* v_val_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_val_2614_ = lean_ctor_get(v___y_2605_, 0);
lean_inc(v_val_2614_);
lean_dec_ref_known(v___y_2605_, 1);
v___x_2615_ = l_Lean_SourceInfo_fromRef(v_val_2614_, v___x_2447_);
lean_dec(v_val_2614_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = l_Array_mkArray1___redArg(v___x_2617_);
v___y_2575_ = v___y_2601_;
v___y_2576_ = v___y_2602_;
v___y_2577_ = v___y_2603_;
v___y_2578_ = v___y_2604_;
v___y_2579_ = v___y_2606_;
v___y_2580_ = v___x_2613_;
v___y_2581_ = v___y_2608_;
v___y_2582_ = v___y_2607_;
v___y_2583_ = v___y_2609_;
v___y_2584_ = v___y_2610_;
v___y_2585_ = v___x_2618_;
goto v___jp_2574_;
}
else
{
lean_object* v___x_2619_; 
lean_dec(v___y_2605_);
v___x_2619_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2575_ = v___y_2601_;
v___y_2576_ = v___y_2602_;
v___y_2577_ = v___y_2603_;
v___y_2578_ = v___y_2604_;
v___y_2579_ = v___y_2606_;
v___y_2580_ = v___x_2613_;
v___y_2581_ = v___y_2608_;
v___y_2582_ = v___y_2607_;
v___y_2583_ = v___y_2609_;
v___y_2584_ = v___y_2610_;
v___y_2585_ = v___x_2619_;
goto v___jp_2574_;
}
}
v___jp_2620_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2635_ = l_Array_append___redArg(v___x_2538_, v___y_2634_);
lean_dec_ref(v___y_2634_);
lean_inc_n(v___y_2624_, 3);
v___x_2636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2624_);
lean_ctor_set(v___x_2636_, 1, v___x_2537_);
lean_ctor_set(v___x_2636_, 2, v___x_2635_);
v___x_2637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___y_2624_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = l_Lean_Syntax_node6(v___y_2624_, v___y_2629_, v___y_2621_, v___y_2627_, v___y_2623_, v___x_2636_, v___x_2638_, v___y_2626_);
v___x_2640_ = l_Lean_Syntax_node4(v___y_2624_, v___y_2622_, v___y_2633_, v___y_2628_, v___y_2630_, v___x_2639_);
v___y_2504_ = v___y_2631_;
v_stx_2505_ = v___x_2640_;
v___y_2506_ = v___y_2625_;
v___y_2507_ = v___y_2632_;
goto v___jp_2503_;
}
v___jp_2641_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = l_Array_append___redArg(v___x_2538_, v___y_2655_);
lean_dec_ref(v___y_2655_);
lean_inc(v___y_2644_);
v___x_2657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2644_);
lean_ctor_set(v___x_2657_, 1, v___x_2537_);
lean_ctor_set(v___x_2657_, 2, v___x_2656_);
if (lean_obj_tag(v___y_2650_) == 1)
{
lean_object* v_val_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_dec(v___x_2446_);
v_val_2658_ = lean_ctor_get(v___y_2650_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v___y_2650_, 1);
v___x_2659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2660_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2659_);
v___x_2661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2644_, 4);
v___x_2662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___y_2644_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = l_Array_append___redArg(v___x_2538_, v_val_2658_);
lean_dec(v_val_2658_);
v___x_2664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2664_, 0, v___y_2644_);
lean_ctor_set(v___x_2664_, 1, v___x_2537_);
lean_ctor_set(v___x_2664_, 2, v___x_2663_);
v___x_2665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___y_2644_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_Syntax_node3(v___y_2644_, v___x_2660_, v___x_2662_, v___x_2664_, v___x_2666_);
v___x_2668_ = l_Array_mkArray1___redArg(v___x_2667_);
v___y_2621_ = v___y_2642_;
v___y_2622_ = v___y_2643_;
v___y_2623_ = v___x_2657_;
v___y_2624_ = v___y_2644_;
v___y_2625_ = v___y_2645_;
v___y_2626_ = v___y_2646_;
v___y_2627_ = v___y_2647_;
v___y_2628_ = v___y_2648_;
v___y_2629_ = v___y_2649_;
v___y_2630_ = v___y_2651_;
v___y_2631_ = v___y_2652_;
v___y_2632_ = v___y_2653_;
v___y_2633_ = v___y_2654_;
v___y_2634_ = v___x_2668_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2669_; 
lean_dec(v___y_2650_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_2669_ = lean_mk_empty_array_with_capacity(v___x_2446_);
lean_dec(v___x_2446_);
v___y_2621_ = v___y_2642_;
v___y_2622_ = v___y_2643_;
v___y_2623_ = v___x_2657_;
v___y_2624_ = v___y_2644_;
v___y_2625_ = v___y_2645_;
v___y_2626_ = v___y_2646_;
v___y_2627_ = v___y_2647_;
v___y_2628_ = v___y_2648_;
v___y_2629_ = v___y_2649_;
v___y_2630_ = v___y_2651_;
v___y_2631_ = v___y_2652_;
v___y_2632_ = v___y_2653_;
v___y_2633_ = v___y_2654_;
v___y_2634_ = v___x_2669_;
goto v___jp_2620_;
}
}
v___jp_2670_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = l_Array_append___redArg(v___x_2538_, v___y_2684_);
lean_dec_ref(v___y_2684_);
lean_inc(v___y_2674_);
v___x_2686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2686_, 0, v___y_2674_);
lean_ctor_set(v___x_2686_, 1, v___x_2537_);
lean_ctor_set(v___x_2686_, 2, v___x_2685_);
if (lean_obj_tag(v___y_2673_) == 1)
{
lean_object* v_val_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_val_2687_ = lean_ctor_get(v___y_2673_, 0);
lean_inc(v_val_2687_);
lean_dec_ref_known(v___y_2673_, 1);
v___x_2688_ = l_Lean_SourceInfo_fromRef(v_val_2687_, v___x_2447_);
lean_dec(v_val_2687_);
v___x_2689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = l_Array_mkArray1___redArg(v___x_2690_);
v___y_2642_ = v___y_2671_;
v___y_2643_ = v___y_2672_;
v___y_2644_ = v___y_2674_;
v___y_2645_ = v___y_2675_;
v___y_2646_ = v___y_2676_;
v___y_2647_ = v___x_2686_;
v___y_2648_ = v___y_2677_;
v___y_2649_ = v___y_2678_;
v___y_2650_ = v___y_2679_;
v___y_2651_ = v___y_2680_;
v___y_2652_ = v___y_2681_;
v___y_2653_ = v___y_2682_;
v___y_2654_ = v___y_2683_;
v___y_2655_ = v___x_2691_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2692_; 
lean_dec(v___y_2673_);
v___x_2692_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2642_ = v___y_2671_;
v___y_2643_ = v___y_2672_;
v___y_2644_ = v___y_2674_;
v___y_2645_ = v___y_2675_;
v___y_2646_ = v___y_2676_;
v___y_2647_ = v___x_2686_;
v___y_2648_ = v___y_2677_;
v___y_2649_ = v___y_2678_;
v___y_2650_ = v___y_2679_;
v___y_2651_ = v___y_2680_;
v___y_2652_ = v___y_2681_;
v___y_2653_ = v___y_2682_;
v___y_2654_ = v___y_2683_;
v___y_2655_ = v___x_2692_;
goto v___jp_2641_;
}
}
v___jp_2693_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2705_ = l_Array_append___redArg(v___x_2538_, v___y_2704_);
lean_dec_ref(v___y_2704_);
lean_inc_n(v___y_2700_, 2);
v___x_2706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2706_, 0, v___y_2700_);
lean_ctor_set(v___x_2706_, 1, v___x_2537_);
lean_ctor_set(v___x_2706_, 2, v___x_2705_);
v___x_2707_ = l_Lean_Syntax_node5(v___y_2700_, v___x_2448_, v___y_2694_, v___y_2697_, v___y_2698_, v___y_2695_, v___x_2706_);
lean_inc(v___y_2699_);
v___x_2708_ = l_Lean_Syntax_node4(v___y_2700_, v___x_2449_, v___y_2696_, v___y_2699_, v___y_2699_, v___x_2707_);
v___y_2504_ = v___y_2702_;
v_stx_2505_ = v___x_2708_;
v___y_2506_ = v___y_2703_;
v___y_2507_ = v___y_2701_;
goto v___jp_2503_;
}
v___jp_2709_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = l_Array_append___redArg(v___x_2538_, v___y_2720_);
lean_dec_ref(v___y_2720_);
lean_inc(v___y_2716_);
v___x_2722_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2722_, 0, v___y_2716_);
lean_ctor_set(v___x_2722_, 1, v___x_2537_);
lean_ctor_set(v___x_2722_, 2, v___x_2721_);
if (lean_obj_tag(v___y_2714_) == 1)
{
lean_object* v_val_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec(v___x_2446_);
v_val_2723_ = lean_ctor_get(v___y_2714_, 0);
lean_inc(v_val_2723_);
lean_dec_ref_known(v___y_2714_, 1);
v___x_2724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2716_);
v___x_2725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2716_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Array_mkArray2___redArg(v___x_2725_, v_val_2723_);
v___y_2694_ = v___y_2710_;
v___y_2695_ = v___x_2722_;
v___y_2696_ = v___y_2711_;
v___y_2697_ = v___y_2712_;
v___y_2698_ = v___y_2713_;
v___y_2699_ = v___y_2715_;
v___y_2700_ = v___y_2716_;
v___y_2701_ = v___y_2717_;
v___y_2702_ = v___y_2718_;
v___y_2703_ = v___y_2719_;
v___y_2704_ = v___x_2726_;
goto v___jp_2693_;
}
else
{
lean_object* v___x_2727_; 
lean_dec(v___y_2714_);
v___x_2727_ = lean_mk_empty_array_with_capacity(v___x_2446_);
lean_dec(v___x_2446_);
v___y_2694_ = v___y_2710_;
v___y_2695_ = v___x_2722_;
v___y_2696_ = v___y_2711_;
v___y_2697_ = v___y_2712_;
v___y_2698_ = v___y_2713_;
v___y_2699_ = v___y_2715_;
v___y_2700_ = v___y_2716_;
v___y_2701_ = v___y_2717_;
v___y_2702_ = v___y_2718_;
v___y_2703_ = v___y_2719_;
v___y_2704_ = v___x_2727_;
goto v___jp_2693_;
}
}
v___jp_2728_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = l_Array_append___redArg(v___x_2538_, v___y_2739_);
lean_dec_ref(v___y_2739_);
lean_inc(v___y_2735_);
v___x_2741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2741_, 0, v___y_2735_);
lean_ctor_set(v___x_2741_, 1, v___x_2537_);
lean_ctor_set(v___x_2741_, 2, v___x_2740_);
if (lean_obj_tag(v___y_2732_) == 1)
{
lean_object* v_val_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_val_2742_ = lean_ctor_get(v___y_2732_, 0);
lean_inc(v_val_2742_);
lean_dec_ref_known(v___y_2732_, 1);
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2744_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2743_);
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2735_, 4);
v___x_2746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___y_2735_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = l_Array_append___redArg(v___x_2538_, v_val_2742_);
lean_dec(v_val_2742_);
v___x_2748_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2748_, 0, v___y_2735_);
lean_ctor_set(v___x_2748_, 1, v___x_2537_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___y_2735_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = l_Lean_Syntax_node3(v___y_2735_, v___x_2744_, v___x_2746_, v___x_2748_, v___x_2750_);
v___x_2752_ = l_Array_mkArray1___redArg(v___x_2751_);
v___y_2710_ = v___y_2729_;
v___y_2711_ = v___y_2730_;
v___y_2712_ = v___y_2731_;
v___y_2713_ = v___x_2741_;
v___y_2714_ = v___y_2733_;
v___y_2715_ = v___y_2734_;
v___y_2716_ = v___y_2735_;
v___y_2717_ = v___y_2736_;
v___y_2718_ = v___y_2737_;
v___y_2719_ = v___y_2738_;
v___y_2720_ = v___x_2752_;
goto v___jp_2709_;
}
else
{
lean_object* v___x_2753_; 
lean_dec(v___y_2732_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_2753_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2710_ = v___y_2729_;
v___y_2711_ = v___y_2730_;
v___y_2712_ = v___y_2731_;
v___y_2713_ = v___x_2741_;
v___y_2714_ = v___y_2733_;
v___y_2715_ = v___y_2734_;
v___y_2716_ = v___y_2735_;
v___y_2717_ = v___y_2736_;
v___y_2718_ = v___y_2737_;
v___y_2719_ = v___y_2738_;
v___y_2720_ = v___x_2753_;
goto v___jp_2709_;
}
}
v___jp_2754_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = l_Array_append___redArg(v___x_2538_, v___y_2765_);
lean_dec_ref(v___y_2765_);
lean_inc(v___y_2761_);
v___x_2767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2767_, 0, v___y_2761_);
lean_ctor_set(v___x_2767_, 1, v___x_2537_);
lean_ctor_set(v___x_2767_, 2, v___x_2766_);
if (lean_obj_tag(v___y_2759_) == 1)
{
lean_object* v_val_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_val_2768_ = lean_ctor_get(v___y_2759_, 0);
lean_inc(v_val_2768_);
lean_dec_ref_known(v___y_2759_, 1);
v___x_2769_ = l_Lean_SourceInfo_fromRef(v_val_2768_, v___x_2447_);
lean_dec(v_val_2768_);
v___x_2770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Array_mkArray1___redArg(v___x_2771_);
v___y_2729_ = v___y_2755_;
v___y_2730_ = v___y_2756_;
v___y_2731_ = v___x_2767_;
v___y_2732_ = v___y_2757_;
v___y_2733_ = v___y_2758_;
v___y_2734_ = v___y_2760_;
v___y_2735_ = v___y_2761_;
v___y_2736_ = v___y_2762_;
v___y_2737_ = v___y_2763_;
v___y_2738_ = v___y_2764_;
v___y_2739_ = v___x_2772_;
goto v___jp_2728_;
}
else
{
lean_object* v___x_2773_; 
lean_dec(v___y_2759_);
v___x_2773_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2729_ = v___y_2755_;
v___y_2730_ = v___y_2756_;
v___y_2731_ = v___x_2767_;
v___y_2732_ = v___y_2757_;
v___y_2733_ = v___y_2758_;
v___y_2734_ = v___y_2760_;
v___y_2735_ = v___y_2761_;
v___y_2736_ = v___y_2762_;
v___y_2737_ = v___y_2763_;
v___y_2738_ = v___y_2764_;
v___y_2739_ = v___x_2773_;
goto v___jp_2728_;
}
}
v___jp_2774_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2788_ = l_Array_append___redArg(v___x_2538_, v___y_2787_);
lean_dec_ref(v___y_2787_);
lean_inc_n(v___y_2782_, 3);
v___x_2789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2789_, 0, v___y_2782_);
lean_ctor_set(v___x_2789_, 1, v___x_2537_);
lean_ctor_set(v___x_2789_, 2, v___x_2788_);
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___y_2782_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l_Lean_Syntax_node6(v___y_2782_, v___y_2776_, v___y_2775_, v___y_2778_, v___y_2779_, v___x_2789_, v___x_2791_, v___y_2777_);
lean_inc(v___y_2784_);
v___x_2793_ = l_Lean_Syntax_node4(v___y_2782_, v___y_2783_, v___y_2781_, v___y_2784_, v___y_2784_, v___x_2792_);
v___y_2504_ = v___y_2785_;
v_stx_2505_ = v___x_2793_;
v___y_2506_ = v___y_2780_;
v___y_2507_ = v___y_2786_;
goto v___jp_2503_;
}
v___jp_2794_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = l_Array_append___redArg(v___x_2538_, v___y_2807_);
lean_dec_ref(v___y_2807_);
lean_inc(v___y_2801_);
v___x_2809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2809_, 0, v___y_2801_);
lean_ctor_set(v___x_2809_, 1, v___x_2537_);
lean_ctor_set(v___x_2809_, 2, v___x_2808_);
if (lean_obj_tag(v___y_2803_) == 1)
{
lean_object* v_val_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec(v___x_2446_);
v_val_2810_ = lean_ctor_get(v___y_2803_, 0);
lean_inc(v_val_2810_);
lean_dec_ref_known(v___y_2803_, 1);
v___x_2811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2812_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2811_);
v___x_2813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2801_, 4);
v___x_2814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___y_2801_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = l_Array_append___redArg(v___x_2538_, v_val_2810_);
lean_dec(v_val_2810_);
v___x_2816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2816_, 0, v___y_2801_);
lean_ctor_set(v___x_2816_, 1, v___x_2537_);
lean_ctor_set(v___x_2816_, 2, v___x_2815_);
v___x_2817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___y_2801_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = l_Lean_Syntax_node3(v___y_2801_, v___x_2812_, v___x_2814_, v___x_2816_, v___x_2818_);
v___x_2820_ = l_Array_mkArray1___redArg(v___x_2819_);
v___y_2775_ = v___y_2795_;
v___y_2776_ = v___y_2796_;
v___y_2777_ = v___y_2797_;
v___y_2778_ = v___y_2798_;
v___y_2779_ = v___x_2809_;
v___y_2780_ = v___y_2799_;
v___y_2781_ = v___y_2800_;
v___y_2782_ = v___y_2801_;
v___y_2783_ = v___y_2802_;
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v___y_2786_ = v___y_2806_;
v___y_2787_ = v___x_2820_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2821_; 
lean_dec(v___y_2803_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_2821_ = lean_mk_empty_array_with_capacity(v___x_2446_);
lean_dec(v___x_2446_);
v___y_2775_ = v___y_2795_;
v___y_2776_ = v___y_2796_;
v___y_2777_ = v___y_2797_;
v___y_2778_ = v___y_2798_;
v___y_2779_ = v___x_2809_;
v___y_2780_ = v___y_2799_;
v___y_2781_ = v___y_2800_;
v___y_2782_ = v___y_2801_;
v___y_2783_ = v___y_2802_;
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v___y_2786_ = v___y_2806_;
v___y_2787_ = v___x_2821_;
goto v___jp_2774_;
}
}
v___jp_2822_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = l_Array_append___redArg(v___x_2538_, v___y_2835_);
lean_dec_ref(v___y_2835_);
lean_inc(v___y_2829_);
v___x_2837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2837_, 0, v___y_2829_);
lean_ctor_set(v___x_2837_, 1, v___x_2537_);
lean_ctor_set(v___x_2837_, 2, v___x_2836_);
if (lean_obj_tag(v___y_2826_) == 1)
{
lean_object* v_val_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v_val_2838_ = lean_ctor_get(v___y_2826_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v___y_2826_, 1);
v___x_2839_ = l_Lean_SourceInfo_fromRef(v_val_2838_, v___x_2447_);
lean_dec(v_val_2838_);
v___x_2840_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Array_mkArray1___redArg(v___x_2841_);
v___y_2795_ = v___y_2823_;
v___y_2796_ = v___y_2824_;
v___y_2797_ = v___y_2825_;
v___y_2798_ = v___x_2837_;
v___y_2799_ = v___y_2827_;
v___y_2800_ = v___y_2828_;
v___y_2801_ = v___y_2829_;
v___y_2802_ = v___y_2830_;
v___y_2803_ = v___y_2831_;
v___y_2804_ = v___y_2832_;
v___y_2805_ = v___y_2833_;
v___y_2806_ = v___y_2834_;
v___y_2807_ = v___x_2842_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2843_; 
lean_dec(v___y_2826_);
v___x_2843_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2795_ = v___y_2823_;
v___y_2796_ = v___y_2824_;
v___y_2797_ = v___y_2825_;
v___y_2798_ = v___x_2837_;
v___y_2799_ = v___y_2827_;
v___y_2800_ = v___y_2828_;
v___y_2801_ = v___y_2829_;
v___y_2802_ = v___y_2830_;
v___y_2803_ = v___y_2831_;
v___y_2804_ = v___y_2832_;
v___y_2805_ = v___y_2833_;
v___y_2806_ = v___y_2834_;
v___y_2807_ = v___x_2843_;
goto v___jp_2794_;
}
}
v___jp_2844_:
{
if (v___y_2850_ == 0)
{
if (v_useReducible_2450_ == 0)
{
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
if (lean_obj_tag(v___y_2855_) == 0)
{
lean_dec(v___y_2859_);
lean_dec(v___y_2854_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___y_2510_ = v___y_2856_;
v___y_2511_ = v___y_2852_;
v___y_2512_ = v___y_2847_;
v___y_2513_ = v___y_2845_;
v___y_2514_ = v___y_2849_;
v___y_2515_ = v___y_2853_;
v___y_2516_ = v___y_2857_;
v___y_2517_ = v___y_2851_;
v___y_2518_ = v___y_2858_;
goto v___jp_2509_;
}
else
{
lean_object* v_val_2860_; lean_object* v___x_2861_; 
v_val_2860_ = lean_ctor_get(v___y_2855_, 0);
lean_inc(v_val_2860_);
lean_dec_ref_known(v___y_2855_, 1);
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2851_);
v___x_2861_ = lean_apply_9(v___f_2451_, v___y_2852_, v___y_2847_, v___y_2845_, v___y_2849_, v___y_2853_, v___y_2857_, v___y_2851_, v___y_2858_, lean_box(0));
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc_n(v_a_2862_, 3);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2445_, 2);
lean_inc_ref_n(v___x_2444_, 2);
lean_inc_ref_n(v___x_2443_, 2);
v___x_2864_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_a_2862_);
lean_ctor_set(v___x_2865_, 1, v___x_2452_);
v___x_2866_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2866_, 0, v_a_2862_);
lean_ctor_set(v___x_2866_, 1, v___x_2537_);
lean_ctor_set(v___x_2866_, 2, v___x_2538_);
v___x_2867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2868_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2867_);
if (lean_obj_tag(v___y_2859_) == 0)
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2823_ = v___y_2846_;
v___y_2824_ = v___x_2868_;
v___y_2825_ = v_val_2860_;
v___y_2826_ = v___y_2848_;
v___y_2827_ = v___y_2851_;
v___y_2828_ = v___x_2865_;
v___y_2829_ = v_a_2862_;
v___y_2830_ = v___x_2864_;
v___y_2831_ = v___y_2854_;
v___y_2832_ = v___x_2866_;
v___y_2833_ = v___y_2856_;
v___y_2834_ = v___y_2858_;
v___y_2835_ = v___x_2869_;
goto v___jp_2822_;
}
else
{
lean_object* v_val_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_val_2870_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_val_2870_);
lean_dec_ref_known(v___y_2859_, 1);
v___x_2871_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_2872_ = lean_array_push(v___x_2871_, v_val_2870_);
v___y_2823_ = v___y_2846_;
v___y_2824_ = v___x_2868_;
v___y_2825_ = v_val_2860_;
v___y_2826_ = v___y_2848_;
v___y_2827_ = v___y_2851_;
v___y_2828_ = v___x_2865_;
v___y_2829_ = v_a_2862_;
v___y_2830_ = v___x_2864_;
v___y_2831_ = v___y_2854_;
v___y_2832_ = v___x_2866_;
v___y_2833_ = v___y_2856_;
v___y_2834_ = v___y_2858_;
v___y_2835_ = v___x_2872_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_val_2860_);
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec_ref(v___x_2452_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v_a_2873_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2861_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2861_);
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
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_object* v___x_2881_; 
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2851_);
v___x_2881_ = lean_apply_9(v___f_2451_, v___y_2852_, v___y_2847_, v___y_2845_, v___y_2849_, v___y_2853_, v___y_2857_, v___y_2851_, v___y_2858_, lean_box(0));
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc_n(v_a_2882_, 3);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_a_2882_);
lean_ctor_set(v___x_2883_, 1, v___x_2452_);
v___x_2884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2884_, 0, v_a_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2537_);
lean_ctor_set(v___x_2884_, 2, v___x_2538_);
if (lean_obj_tag(v___y_2859_) == 0)
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2755_ = v___y_2846_;
v___y_2756_ = v___x_2883_;
v___y_2757_ = v___y_2854_;
v___y_2758_ = v___y_2855_;
v___y_2759_ = v___y_2848_;
v___y_2760_ = v___x_2884_;
v___y_2761_ = v_a_2882_;
v___y_2762_ = v___y_2858_;
v___y_2763_ = v___y_2856_;
v___y_2764_ = v___y_2851_;
v___y_2765_ = v___x_2885_;
goto v___jp_2754_;
}
else
{
lean_object* v_val_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_val_2886_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v___y_2859_, 1);
v___x_2887_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_2888_ = lean_array_push(v___x_2887_, v_val_2886_);
v___y_2755_ = v___y_2846_;
v___y_2756_ = v___x_2883_;
v___y_2757_ = v___y_2854_;
v___y_2758_ = v___y_2855_;
v___y_2759_ = v___y_2848_;
v___y_2760_ = v___x_2884_;
v___y_2761_ = v_a_2882_;
v___y_2762_ = v___y_2858_;
v___y_2763_ = v___y_2856_;
v___y_2764_ = v___y_2851_;
v___y_2765_ = v___x_2888_;
goto v___jp_2754_;
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec_ref(v___x_2452_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v_a_2889_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2881_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2881_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
else
{
lean_dec(v___x_2449_);
if (v_useReducible_2450_ == 0)
{
lean_dec(v___x_2448_);
if (lean_obj_tag(v___y_2855_) == 0)
{
lean_dec(v___y_2859_);
lean_dec(v___y_2854_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___y_2510_ = v___y_2856_;
v___y_2511_ = v___y_2852_;
v___y_2512_ = v___y_2847_;
v___y_2513_ = v___y_2845_;
v___y_2514_ = v___y_2849_;
v___y_2515_ = v___y_2853_;
v___y_2516_ = v___y_2857_;
v___y_2517_ = v___y_2851_;
v___y_2518_ = v___y_2858_;
goto v___jp_2509_;
}
else
{
lean_object* v_val_2897_; lean_object* v___x_2898_; 
v_val_2897_ = lean_ctor_get(v___y_2855_, 0);
lean_inc(v_val_2897_);
lean_dec_ref_known(v___y_2855_, 1);
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2851_);
v___x_2898_ = lean_apply_9(v___f_2451_, v___y_2852_, v___y_2847_, v___y_2845_, v___y_2849_, v___y_2853_, v___y_2857_, v___y_2851_, v___y_2858_, lean_box(0));
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_n(v_a_2899_, 5);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2445_, 2);
lean_inc_ref_n(v___x_2444_, 2);
lean_inc_ref_n(v___x_2443_, 2);
v___x_2901_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2902_, 0, v_a_2899_);
lean_ctor_set(v___x_2902_, 1, v___x_2452_);
v___x_2903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2903_, 0, v_a_2899_);
lean_ctor_set(v___x_2903_, 1, v___x_2537_);
lean_ctor_set(v___x_2903_, 2, v___x_2538_);
v___x_2904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_2905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2905_, 0, v_a_2899_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l_Lean_Syntax_node1(v_a_2899_, v___x_2537_, v___x_2905_);
v___x_2907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2908_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2907_);
if (lean_obj_tag(v___y_2859_) == 0)
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2671_ = v___y_2846_;
v___y_2672_ = v___x_2901_;
v___y_2673_ = v___y_2848_;
v___y_2674_ = v_a_2899_;
v___y_2675_ = v___y_2851_;
v___y_2676_ = v_val_2897_;
v___y_2677_ = v___x_2903_;
v___y_2678_ = v___x_2908_;
v___y_2679_ = v___y_2854_;
v___y_2680_ = v___x_2906_;
v___y_2681_ = v___y_2856_;
v___y_2682_ = v___y_2858_;
v___y_2683_ = v___x_2902_;
v___y_2684_ = v___x_2909_;
goto v___jp_2670_;
}
else
{
lean_object* v_val_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_val_2910_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v___y_2859_, 1);
v___x_2911_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_2912_ = lean_array_push(v___x_2911_, v_val_2910_);
v___y_2671_ = v___y_2846_;
v___y_2672_ = v___x_2901_;
v___y_2673_ = v___y_2848_;
v___y_2674_ = v_a_2899_;
v___y_2675_ = v___y_2851_;
v___y_2676_ = v_val_2897_;
v___y_2677_ = v___x_2903_;
v___y_2678_ = v___x_2908_;
v___y_2679_ = v___y_2854_;
v___y_2680_ = v___x_2906_;
v___y_2681_ = v___y_2856_;
v___y_2682_ = v___y_2858_;
v___y_2683_ = v___x_2902_;
v___y_2684_ = v___x_2912_;
goto v___jp_2670_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_val_2897_);
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec_ref(v___x_2452_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v_a_2913_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2898_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2898_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
else
{
lean_object* v___x_2921_; 
lean_dec_ref(v___x_2452_);
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2851_);
v___x_2921_ = lean_apply_9(v___f_2451_, v___y_2852_, v___y_2847_, v___y_2845_, v___y_2849_, v___y_2853_, v___y_2857_, v___y_2851_, v___y_2858_, lean_box(0));
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc_n(v_a_2922_, 2);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20));
lean_inc_ref(v___x_2445_);
lean_inc_ref(v___x_2444_);
lean_inc_ref(v___x_2443_);
v___x_2924_ = l_Lean_Name_mkStr4(v___x_2443_, v___x_2444_, v___x_2445_, v___x_2923_);
v___x_2925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21));
v___x_2926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2926_, 0, v_a_2922_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
if (lean_obj_tag(v___y_2859_) == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_2601_ = v___y_2846_;
v___y_2602_ = v___y_2854_;
v___y_2603_ = v___y_2855_;
v___y_2604_ = v___y_2856_;
v___y_2605_ = v___y_2848_;
v___y_2606_ = v___x_2926_;
v___y_2607_ = v___x_2924_;
v___y_2608_ = v_a_2922_;
v___y_2609_ = v___y_2851_;
v___y_2610_ = v___y_2858_;
v___y_2611_ = v___x_2927_;
goto v___jp_2600_;
}
else
{
lean_object* v_val_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_val_2928_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v___y_2859_, 1);
v___x_2929_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_2930_ = lean_array_push(v___x_2929_, v_val_2928_);
v___y_2601_ = v___y_2846_;
v___y_2602_ = v___y_2854_;
v___y_2603_ = v___y_2855_;
v___y_2604_ = v___y_2856_;
v___y_2605_ = v___y_2848_;
v___y_2606_ = v___x_2926_;
v___y_2607_ = v___x_2924_;
v___y_2608_ = v_a_2922_;
v___y_2609_ = v___y_2851_;
v___y_2610_ = v___y_2858_;
v___y_2611_ = v___x_2930_;
goto v___jp_2600_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2848_);
lean_dec(v___y_2846_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v_a_2931_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2921_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2921_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
}
v___jp_2939_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2956_ = lean_unsigned_to_nat(5u);
v___x_2957_ = l_Lean_Syntax_getArg(v___y_2944_, v___x_2956_);
lean_dec(v___y_2944_);
v___x_2958_ = l_Lean_Syntax_matchesNull(v___x_2957_, v___x_2446_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v_args_2947_);
lean_dec(v___y_2946_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_2959_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2960_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2959_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___y_2504_ = v___y_2943_;
v_stx_2505_ = v_a_2961_;
v___y_2506_ = v___y_2954_;
v___y_2507_ = v___y_2955_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec_ref(v___y_2943_);
lean_dec(v_tk_2442_);
v_a_2962_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2960_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2960_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_Syntax_getOptional_x3f(v___y_2946_);
lean_dec(v___y_2946_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_box(0);
v___y_2845_ = v___y_2950_;
v___y_2846_ = v___y_2940_;
v___y_2847_ = v___y_2949_;
v___y_2848_ = v___y_2942_;
v___y_2849_ = v___y_2951_;
v___y_2850_ = v___y_2945_;
v___y_2851_ = v___y_2954_;
v___y_2852_ = v___y_2948_;
v___y_2853_ = v___y_2952_;
v___y_2854_ = v_args_2947_;
v___y_2855_ = v___y_2941_;
v___y_2856_ = v___y_2943_;
v___y_2857_ = v___y_2953_;
v___y_2858_ = v___y_2955_;
v___y_2859_ = v___x_2971_;
goto v___jp_2844_;
}
else
{
lean_object* v_val_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_val_2972_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2970_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_val_2972_);
lean_dec(v___x_2970_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_val_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
v___y_2845_ = v___y_2950_;
v___y_2846_ = v___y_2940_;
v___y_2847_ = v___y_2949_;
v___y_2848_ = v___y_2942_;
v___y_2849_ = v___y_2951_;
v___y_2850_ = v___y_2945_;
v___y_2851_ = v___y_2954_;
v___y_2852_ = v___y_2948_;
v___y_2853_ = v___y_2952_;
v___y_2854_ = v_args_2947_;
v___y_2855_ = v___y_2941_;
v___y_2856_ = v___y_2943_;
v___y_2857_ = v___y_2953_;
v___y_2858_ = v___y_2955_;
v___y_2859_ = v___x_2977_;
goto v___jp_2844_;
}
}
}
}
}
v___jp_2980_:
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = l_Lean_Syntax_getArg(v___y_2984_, v___x_2453_);
v___x_2997_ = l_Lean_Syntax_isNone(v___x_2996_);
if (v___x_2997_ == 0)
{
uint8_t v___x_2998_; 
lean_inc(v___x_2996_);
v___x_2998_ = l_Lean_Syntax_matchesNull(v___x_2996_, v___x_2454_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec(v___x_2996_);
lean_dec(v_only_2987_);
lean_dec(v___y_2986_);
lean_dec(v___y_2984_);
lean_dec(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_2999_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_3000_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2999_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___y_2504_ = v___y_2983_;
v_stx_2505_ = v_a_3001_;
v___y_2506_ = v___y_2994_;
v___y_2507_ = v___y_2995_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2983_);
lean_dec(v_tk_2442_);
v_a_3002_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_3000_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3000_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = l_Lean_Syntax_getArg(v___x_2996_, v___x_2455_);
lean_dec(v___x_2455_);
lean_dec(v___x_2996_);
v___x_3011_ = l_Lean_Syntax_getArgs(v___x_3010_);
lean_dec(v___x_3010_);
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
v___y_2940_ = v___y_2981_;
v___y_2941_ = v___y_2982_;
v___y_2942_ = v_only_2987_;
v___y_2943_ = v___y_2983_;
v___y_2944_ = v___y_2984_;
v___y_2945_ = v___y_2985_;
v___y_2946_ = v___y_2986_;
v_args_2947_ = v___x_3012_;
v___y_2948_ = v___y_2988_;
v___y_2949_ = v___y_2989_;
v___y_2950_ = v___y_2990_;
v___y_2951_ = v___y_2991_;
v___y_2952_ = v___y_2992_;
v___y_2953_ = v___y_2993_;
v___y_2954_ = v___y_2994_;
v___y_2955_ = v___y_2995_;
goto v___jp_2939_;
}
}
else
{
lean_object* v___x_3013_; 
lean_dec(v___x_2996_);
lean_dec(v___x_2455_);
v___x_3013_ = lean_box(0);
v___y_2940_ = v___y_2981_;
v___y_2941_ = v___y_2982_;
v___y_2942_ = v_only_2987_;
v___y_2943_ = v___y_2983_;
v___y_2944_ = v___y_2984_;
v___y_2945_ = v___y_2985_;
v___y_2946_ = v___y_2986_;
v_args_2947_ = v___x_3013_;
v___y_2948_ = v___y_2988_;
v___y_2949_ = v___y_2989_;
v___y_2950_ = v___y_2990_;
v___y_2951_ = v___y_2991_;
v___y_2952_ = v___y_2992_;
v___y_2953_ = v___y_2993_;
v___y_2954_ = v___y_2994_;
v___y_2955_ = v___y_2995_;
goto v___jp_2939_;
}
}
v___jp_3014_:
{
lean_object* v_usedTheorems_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_usedTheorems_3019_ = lean_ctor_get(v___y_3015_, 0);
v___x_3020_ = l_Lean_Syntax_unsetTrailing(v___y_3016_);
v___x_3021_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3020_, v_usedTheorems_3019_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; uint8_t v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc_n(v_a_3022_, 2);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = l_Lean_Syntax_isOfKind(v_a_3022_, v___x_2535_);
lean_dec(v___x_2535_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_inc(v_ref_2531_);
lean_dec(v_a_3022_);
lean_dec(v___y_3018_);
lean_dec(v___x_2457_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_3024_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_3025_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_3024_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
v___y_2481_ = v___y_3015_;
v_stx_2482_ = v_a_3026_;
v___y_2483_ = v___y_2473_;
v_ref_2484_ = v_ref_2531_;
v___y_2485_ = v___y_2474_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v___y_3015_);
lean_dec(v_ref_2531_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v_tk_2442_);
v_a_3027_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3025_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3025_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = l_Lean_Syntax_getArg(v_a_3022_, v___x_2455_);
lean_inc(v___x_3035_);
v___x_3036_ = l_Lean_Syntax_isOfKind(v___x_3035_, v___x_2456_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_inc(v_ref_2531_);
lean_dec(v___x_3035_);
lean_dec(v_a_3022_);
lean_dec(v___y_3018_);
lean_dec(v___x_2457_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_3037_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_3038_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_3037_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___y_2481_ = v___y_3015_;
v_stx_2482_ = v_a_3039_;
v___y_2483_ = v___y_2473_;
v_ref_2484_ = v_ref_2531_;
v___y_2485_ = v___y_2474_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v___y_3015_);
lean_dec(v_ref_2531_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v_tk_2442_);
v_a_3040_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3038_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3038_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3048_ = l_Lean_Syntax_getArg(v_a_3022_, v___x_2457_);
lean_dec(v___x_2457_);
v___x_3049_ = l_Lean_Syntax_getArg(v_a_3022_, v___x_2454_);
v___x_3050_ = l_Lean_Syntax_isNone(v___x_3049_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
lean_inc(v___x_3049_);
v___x_3051_ = l_Lean_Syntax_matchesNull(v___x_3049_, v___x_2455_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_inc(v_ref_2531_);
lean_dec(v___x_3049_);
lean_dec(v___x_3048_);
lean_dec(v___x_3035_);
lean_dec(v_a_3022_);
lean_dec(v___y_3018_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
v___x_3052_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_3053_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_3052_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___y_2481_ = v___y_3015_;
v_stx_2482_ = v_a_3054_;
v___y_2483_ = v___y_2473_;
v_ref_2484_ = v_ref_2531_;
v___y_2485_ = v___y_2474_;
goto v___jp_2480_;
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v___y_3015_);
lean_dec(v_ref_2531_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v_tk_2442_);
v_a_3055_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3053_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3053_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = l_Lean_Syntax_getArg(v___x_3049_, v___x_2446_);
lean_dec(v___x_3049_);
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
v___y_2981_ = v___x_3035_;
v___y_2982_ = v___y_3018_;
v___y_2983_ = v___y_3015_;
v___y_2984_ = v_a_3022_;
v___y_2985_ = v___y_3017_;
v___y_2986_ = v___x_3048_;
v_only_2987_ = v___x_3064_;
v___y_2988_ = v___y_2467_;
v___y_2989_ = v___y_2468_;
v___y_2990_ = v___y_2469_;
v___y_2991_ = v___y_2470_;
v___y_2992_ = v___y_2471_;
v___y_2993_ = v___y_2472_;
v___y_2994_ = v___y_2473_;
v___y_2995_ = v___y_2474_;
goto v___jp_2980_;
}
}
else
{
lean_object* v___x_3065_; 
lean_dec(v___x_3049_);
v___x_3065_ = lean_box(0);
v___y_2981_ = v___x_3035_;
v___y_2982_ = v___y_3018_;
v___y_2983_ = v___y_3015_;
v___y_2984_ = v_a_3022_;
v___y_2985_ = v___y_3017_;
v___y_2986_ = v___x_3048_;
v_only_2987_ = v___x_3065_;
v___y_2988_ = v___y_2467_;
v___y_2989_ = v___y_2468_;
v___y_2990_ = v___y_2469_;
v___y_2991_ = v___y_2470_;
v___y_2992_ = v___y_2471_;
v___y_2993_ = v___y_2472_;
v___y_2994_ = v___y_2473_;
v___y_2995_ = v___y_2474_;
goto v___jp_2980_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3015_);
lean_dec(v___x_2535_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___x_2457_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v_a_3066_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3021_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3021_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
v___jp_3074_:
{
if (lean_obj_tag(v_usingArg_2458_) == 0)
{
v___y_3015_ = v___y_3075_;
v___y_3016_ = v___y_3076_;
v___y_3017_ = v___y_3077_;
v___y_3018_ = v_usingArg_2458_;
goto v___jp_3014_;
}
else
{
lean_object* v_val_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3086_; 
v_val_3078_ = lean_ctor_get(v_usingArg_2458_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_usingArg_2458_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3080_ = v_usingArg_2458_;
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_val_3078_);
lean_dec(v_usingArg_2458_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = l_Lean_Syntax_unsetTrailing(v_val_3078_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3082_);
v___x_3084_ = v___x_3080_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
v___y_3015_ = v___y_3075_;
v___y_3016_ = v___y_3076_;
v___y_3017_ = v___y_3077_;
v___y_3018_ = v___x_3084_;
goto v___jp_3014_;
}
}
}
}
v___jp_3087_:
{
if (v___y_3091_ == 0)
{
lean_dec(v___y_3089_);
lean_dec(v___x_2535_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v_usingArg_2458_);
lean_dec(v___x_2457_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v___y_2477_ = v___y_3088_;
goto v___jp_2476_;
}
else
{
v___y_3075_ = v___y_3088_;
v___y_3076_ = v___y_3089_;
v___y_3077_ = v___y_3090_;
goto v___jp_3074_;
}
}
v___jp_3092_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; 
v___x_3098_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3097_, v___x_2532_);
v___x_3099_ = lean_box(v___x_2447_);
v___x_3100_ = lean_box(v___x_2532_);
v___x_3101_ = lean_box(v_useReducible_2450_);
v___x_3102_ = lean_box(v___x_2460_);
lean_inc(v___x_2455_);
lean_inc_ref(v___x_2452_);
lean_inc(v_usingArg_2458_);
lean_inc(v___x_2446_);
lean_inc(v_tk_2442_);
lean_inc(v___x_2457_);
v___f_3103_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 24, 14);
lean_closure_set(v___f_3103_, 0, v___x_2457_);
lean_closure_set(v___f_3103_, 1, v_tk_2442_);
lean_closure_set(v___f_3103_, 2, v___x_2537_);
lean_closure_set(v___f_3103_, 3, v___x_2446_);
lean_closure_set(v___f_3103_, 4, v___x_3098_);
lean_closure_set(v___f_3103_, 5, v___y_3093_);
lean_closure_set(v___f_3103_, 6, v___x_3099_);
lean_closure_set(v___f_3103_, 7, v_usingArg_2458_);
lean_closure_set(v___f_3103_, 8, v___x_3100_);
lean_closure_set(v___f_3103_, 9, v___x_2452_);
lean_closure_set(v___f_3103_, 10, v___x_3101_);
lean_closure_set(v___f_3103_, 11, v___x_3102_);
lean_closure_set(v___f_3103_, 12, v___x_2455_);
lean_closure_set(v___f_3103_, 13, v_usingTk_x3f_2461_);
v___x_3104_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3096_, v___f_3103_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_3096_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3107_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_2530_, v___x_3106_);
if (v___x_3107_ == 0)
{
if (lean_obj_tag(v_squeeze_2462_) == 0)
{
v___y_3088_ = v_a_3105_;
v___y_3089_ = v___y_3094_;
v___y_3090_ = v___y_3095_;
v___y_3091_ = v___x_3107_;
goto v___jp_3087_;
}
else
{
v___y_3088_ = v_a_3105_;
v___y_3089_ = v___y_3094_;
v___y_3090_ = v___y_3095_;
v___y_3091_ = v___x_2460_;
goto v___jp_3087_;
}
}
else
{
v___y_3075_ = v_a_3105_;
v___y_3076_ = v___y_3094_;
v___y_3077_ = v___y_3095_;
goto v___jp_3074_;
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v___y_3094_);
lean_dec(v___x_2535_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v_usingArg_2458_);
lean_dec(v___x_2457_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v_a_3108_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3104_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3104_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
v___jp_3116_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3120_ = l_Array_append___redArg(v___x_2538_, v___y_3119_);
lean_dec_ref(v___y_3119_);
lean_inc_n(v___x_2533_, 2);
v___x_3121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3121_, 0, v___x_2533_);
lean_ctor_set(v___x_3121_, 1, v___x_2537_);
lean_ctor_set(v___x_3121_, 2, v___x_3120_);
v___x_3122_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3122_, 0, v___x_2533_);
lean_ctor_set(v___x_3122_, 1, v___x_2537_);
lean_ctor_set(v___x_3122_, 2, v___x_2538_);
lean_inc(v___x_2535_);
v___x_3123_ = l_Lean_Syntax_node6(v___x_2533_, v___x_2535_, v___x_2536_, v___x_2459_, v___y_3117_, v___y_3118_, v___x_3121_, v___x_3122_);
v___x_3124_ = 0;
v___x_3125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23));
v___x_3126_ = lean_box(v___x_2532_);
v___x_3127_ = lean_box(v___x_3124_);
v___x_3128_ = lean_box(v___x_2532_);
lean_inc(v___x_3123_);
v___x_3129_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3129_, 0, v___x_3123_);
lean_closure_set(v___x_3129_, 1, v___x_3126_);
lean_closure_set(v___x_3129_, 2, v___x_3127_);
lean_closure_set(v___x_3129_, 3, v___x_3128_);
lean_closure_set(v___x_3129_, 4, v___x_3125_);
v___x_3130_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3129_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
if (lean_obj_tag(v_unfold_2463_) == 0)
{
lean_object* v_ctx_3132_; lean_object* v_simprocs_3133_; lean_object* v_dischargeWrapper_3134_; 
v_ctx_3132_ = lean_ctor_get(v_a_3131_, 0);
lean_inc_ref(v_ctx_3132_);
v_simprocs_3133_ = lean_ctor_get(v_a_3131_, 1);
lean_inc_ref(v_simprocs_3133_);
v_dischargeWrapper_3134_ = lean_ctor_get(v_a_3131_, 2);
lean_inc(v_dischargeWrapper_3134_);
lean_dec(v_a_3131_);
v___y_3093_ = v_simprocs_3133_;
v___y_3094_ = v___x_3123_;
v___y_3095_ = v___x_2532_;
v___y_3096_ = v_dischargeWrapper_3134_;
v___y_3097_ = v_ctx_3132_;
goto v___jp_3092_;
}
else
{
if (v___x_2460_ == 0)
{
lean_object* v_ctx_3135_; lean_object* v_simprocs_3136_; lean_object* v_dischargeWrapper_3137_; 
v_ctx_3135_ = lean_ctor_get(v_a_3131_, 0);
lean_inc_ref(v_ctx_3135_);
v_simprocs_3136_ = lean_ctor_get(v_a_3131_, 1);
lean_inc_ref(v_simprocs_3136_);
v_dischargeWrapper_3137_ = lean_ctor_get(v_a_3131_, 2);
lean_inc(v_dischargeWrapper_3137_);
lean_dec(v_a_3131_);
v___y_3093_ = v_simprocs_3136_;
v___y_3094_ = v___x_3123_;
v___y_3095_ = v___x_2460_;
v___y_3096_ = v_dischargeWrapper_3137_;
v___y_3097_ = v_ctx_3135_;
goto v___jp_3092_;
}
else
{
lean_object* v_ctx_3138_; lean_object* v_simprocs_3139_; lean_object* v_dischargeWrapper_3140_; lean_object* v___x_3141_; 
v_ctx_3138_ = lean_ctor_get(v_a_3131_, 0);
lean_inc_ref(v_ctx_3138_);
v_simprocs_3139_ = lean_ctor_get(v_a_3131_, 1);
lean_inc_ref(v_simprocs_3139_);
v_dischargeWrapper_3140_ = lean_ctor_get(v_a_3131_, 2);
lean_inc(v_dischargeWrapper_3140_);
lean_dec(v_a_3131_);
v___x_3141_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3138_);
v___y_3093_ = v_simprocs_3139_;
v___y_3094_ = v___x_3123_;
v___y_3095_ = v___x_2460_;
v___y_3096_ = v_dischargeWrapper_3140_;
v___y_3097_ = v___x_3141_;
goto v___jp_3092_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v___x_3123_);
lean_dec(v___x_2535_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v_usingTk_x3f_2461_);
lean_dec(v_usingArg_2458_);
lean_dec(v___x_2457_);
lean_dec(v___x_2455_);
lean_dec_ref(v___x_2452_);
lean_dec_ref(v___f_2451_);
lean_dec(v___x_2449_);
lean_dec(v___x_2448_);
lean_dec(v___x_2446_);
lean_dec_ref(v___x_2445_);
lean_dec_ref(v___x_2444_);
lean_dec_ref(v___x_2443_);
lean_dec(v_tk_2442_);
v_a_3142_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3130_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3130_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
v___jp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = l_Array_append___redArg(v___x_2538_, v___y_3152_);
lean_dec_ref(v___y_3152_);
lean_inc(v___x_2533_);
v___x_3154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3154_, 0, v___x_2533_);
lean_ctor_set(v___x_3154_, 1, v___x_2537_);
lean_ctor_set(v___x_3154_, 2, v___x_3153_);
if (lean_obj_tag(v_args_2464_) == 1)
{
lean_object* v_val_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_val_3155_ = lean_ctor_get(v_args_2464_, 0);
v___x_3156_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___x_2533_, 3);
v___x_3157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_2533_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Array_append___redArg(v___x_2538_, v_val_3155_);
v___x_3159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3159_, 0, v___x_2533_);
lean_ctor_set(v___x_3159_, 1, v___x_2537_);
lean_ctor_set(v___x_3159_, 2, v___x_3158_);
v___x_3160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_2533_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = l_Array_mkArray3___redArg(v___x_3157_, v___x_3159_, v___x_3161_);
v___y_3117_ = v___y_3151_;
v___y_3118_ = v___x_3154_;
v___y_3119_ = v___x_3162_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3163_; 
v___x_3163_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_3117_ = v___y_3151_;
v___y_3118_ = v___x_3154_;
v___y_3119_ = v___x_3163_;
goto v___jp_3116_;
}
}
v___jp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = l_Array_append___redArg(v___x_2538_, v___y_3165_);
lean_dec_ref(v___y_3165_);
lean_inc(v___x_2533_);
v___x_3167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3167_, 0, v___x_2533_);
lean_ctor_set(v___x_3167_, 1, v___x_2537_);
lean_ctor_set(v___x_3167_, 2, v___x_3166_);
if (lean_obj_tag(v_only_2465_) == 1)
{
lean_object* v_val_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_val_3168_ = lean_ctor_get(v_only_2465_, 0);
v___x_3169_ = l_Lean_SourceInfo_fromRef(v_val_3168_, v___x_2447_);
v___x_3170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = l_Array_mkArray1___redArg(v___x_3171_);
v___y_3151_ = v___x_3167_;
v___y_3152_ = v___x_3172_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___y_3151_ = v___x_3167_;
v___y_3152_ = v___x_3173_;
goto v___jp_3150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v_tk_3178_ = _args[0];
lean_object* v___x_3179_ = _args[1];
lean_object* v___x_3180_ = _args[2];
lean_object* v___x_3181_ = _args[3];
lean_object* v___x_3182_ = _args[4];
lean_object* v___x_3183_ = _args[5];
lean_object* v___x_3184_ = _args[6];
lean_object* v___x_3185_ = _args[7];
lean_object* v_useReducible_3186_ = _args[8];
lean_object* v___f_3187_ = _args[9];
lean_object* v___x_3188_ = _args[10];
lean_object* v___x_3189_ = _args[11];
lean_object* v___x_3190_ = _args[12];
lean_object* v___x_3191_ = _args[13];
lean_object* v___x_3192_ = _args[14];
lean_object* v___x_3193_ = _args[15];
lean_object* v_usingArg_3194_ = _args[16];
lean_object* v___x_3195_ = _args[17];
lean_object* v___x_3196_ = _args[18];
lean_object* v_usingTk_x3f_3197_ = _args[19];
lean_object* v_squeeze_3198_ = _args[20];
lean_object* v_unfold_3199_ = _args[21];
lean_object* v_args_3200_ = _args[22];
lean_object* v_only_3201_ = _args[23];
lean_object* v___y_3202_ = _args[24];
lean_object* v___y_3203_ = _args[25];
lean_object* v___y_3204_ = _args[26];
lean_object* v___y_3205_ = _args[27];
lean_object* v___y_3206_ = _args[28];
lean_object* v___y_3207_ = _args[29];
lean_object* v___y_3208_ = _args[30];
lean_object* v___y_3209_ = _args[31];
lean_object* v___y_3210_ = _args[32];
lean_object* v___y_3211_ = _args[33];
_start:
{
uint8_t v___x_96607__boxed_3212_; uint8_t v_useReducible_boxed_3213_; uint8_t v___x_96618__boxed_3214_; lean_object* v_res_3215_; 
v___x_96607__boxed_3212_ = lean_unbox(v___x_3183_);
v_useReducible_boxed_3213_ = lean_unbox(v_useReducible_3186_);
v___x_96618__boxed_3214_ = lean_unbox(v___x_3196_);
v_res_3215_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3178_, v___x_3179_, v___x_3180_, v___x_3181_, v___x_3182_, v___x_96607__boxed_3212_, v___x_3184_, v___x_3185_, v_useReducible_boxed_3213_, v___f_3187_, v___x_3188_, v___x_3189_, v___x_3190_, v___x_3191_, v___x_3192_, v___x_3193_, v_usingArg_3194_, v___x_3195_, v___x_96618__boxed_3214_, v_usingTk_x3f_3197_, v_squeeze_3198_, v_unfold_3199_, v_args_3200_, v_only_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v_only_3201_);
lean_dec(v_args_3200_);
lean_dec(v_unfold_3199_);
lean_dec(v_squeeze_3198_);
lean_dec(v___x_3192_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3241_, lean_object* v_stx_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_3253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3254_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg___lam__0___closed__1));
v___x_3255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3242_);
v___x_3257_ = l_Lean_Syntax_isOfKind(v_stx_3242_, v___x_3256_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
lean_dec(v_stx_3242_);
v___x_3258_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3258_;
}
else
{
lean_object* v___f_3259_; lean_object* v___x_3260_; lean_object* v_tk_3261_; lean_object* v___x_3262_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; uint8_t v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v_usingTk_x3f_3313_; lean_object* v_usingArg_3314_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; uint8_t v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v_args_3346_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; uint8_t v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v_only_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v_unfold_3402_; lean_object* v_squeeze_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___f_3259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3260_ = lean_unsigned_to_nat(0u);
v_tk_3261_ = l_Lean_Syntax_getArg(v_stx_3242_, v___x_3260_);
v___x_3262_ = lean_unsigned_to_nat(1u);
v___x_3438_ = l_Lean_Syntax_getArg(v_stx_3242_, v___x_3262_);
v___x_3439_ = l_Lean_Syntax_isNone(v___x_3438_);
if (v___x_3439_ == 0)
{
uint8_t v___x_3440_; 
lean_inc(v___x_3438_);
v___x_3440_ = l_Lean_Syntax_matchesNull(v___x_3438_, v___x_3262_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec(v___x_3438_);
lean_dec(v_tk_3261_);
lean_dec(v_stx_3242_);
v___x_3441_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3441_;
}
else
{
lean_object* v_squeeze_3442_; lean_object* v___x_3443_; 
v_squeeze_3442_ = l_Lean_Syntax_getArg(v___x_3438_, v___x_3260_);
lean_dec(v___x_3438_);
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_squeeze_3442_);
v_squeeze_3421_ = v___x_3443_;
v___y_3422_ = v_a_3243_;
v___y_3423_ = v_a_3244_;
v___y_3424_ = v_a_3245_;
v___y_3425_ = v_a_3246_;
v___y_3426_ = v_a_3247_;
v___y_3427_ = v_a_3248_;
v___y_3428_ = v_a_3249_;
v___y_3429_ = v_a_3250_;
goto v___jp_3420_;
}
}
else
{
lean_object* v___x_3444_; 
lean_dec(v___x_3438_);
v___x_3444_ = lean_box(0);
v_squeeze_3421_ = v___x_3444_;
v___y_3422_ = v_a_3243_;
v___y_3423_ = v_a_3244_;
v___y_3424_ = v_a_3245_;
v___y_3425_ = v_a_3246_;
v___y_3426_ = v_a_3247_;
v___y_3427_ = v_a_3248_;
v___y_3428_ = v_a_3249_;
v___y_3429_ = v_a_3250_;
goto v___jp_3420_;
}
v___jp_3263_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3286_ = lean_box(v___x_3257_);
v___x_3287_ = lean_box(v_useReducible_3241_);
v___x_3288_ = lean_box(v___y_3275_);
lean_inc(v___y_3265_);
lean_inc(v___y_3280_);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3289_, 0, v_tk_3261_);
lean_closure_set(v___f_3289_, 1, v___x_3252_);
lean_closure_set(v___f_3289_, 2, v___x_3253_);
lean_closure_set(v___f_3289_, 3, v___x_3254_);
lean_closure_set(v___f_3289_, 4, v___x_3260_);
lean_closure_set(v___f_3289_, 5, v___x_3286_);
lean_closure_set(v___f_3289_, 6, v___y_3280_);
lean_closure_set(v___f_3289_, 7, v___x_3256_);
lean_closure_set(v___f_3289_, 8, v___x_3287_);
lean_closure_set(v___f_3289_, 9, v___f_3259_);
lean_closure_set(v___f_3289_, 10, v___x_3255_);
lean_closure_set(v___f_3289_, 11, v___y_3284_);
lean_closure_set(v___f_3289_, 12, v___y_3264_);
lean_closure_set(v___f_3289_, 13, v___x_3262_);
lean_closure_set(v___f_3289_, 14, v___y_3265_);
lean_closure_set(v___f_3289_, 15, v___y_3281_);
lean_closure_set(v___f_3289_, 16, v___y_3267_);
lean_closure_set(v___f_3289_, 17, v___y_3278_);
lean_closure_set(v___f_3289_, 18, v___x_3288_);
lean_closure_set(v___f_3289_, 19, v___y_3272_);
lean_closure_set(v___f_3289_, 20, v___y_3266_);
lean_closure_set(v___f_3289_, 21, v___y_3279_);
lean_closure_set(v___f_3289_, 22, v___y_3283_);
lean_closure_set(v___f_3289_, 23, v___y_3282_);
lean_closure_set(v___f_3289_, 24, v___y_3285_);
v___x_3290_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3290_, 0, v___f_3289_);
v___x_3291_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3290_, v___y_3268_, v___y_3271_, v___y_3276_, v___y_3273_, v___y_3274_, v___y_3269_, v___y_3270_, v___y_3277_);
return v___x_3291_;
}
v___jp_3292_:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_Syntax_getOptional_x3f(v___y_3296_);
lean_dec(v___y_3296_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_box(0);
v___y_3264_ = v___y_3293_;
v___y_3265_ = v___y_3294_;
v___y_3266_ = v___y_3295_;
v___y_3267_ = v_usingArg_3314_;
v___y_3268_ = v___y_3297_;
v___y_3269_ = v___y_3298_;
v___y_3270_ = v___y_3299_;
v___y_3271_ = v___y_3300_;
v___y_3272_ = v_usingTk_x3f_3313_;
v___y_3273_ = v___y_3301_;
v___y_3274_ = v___y_3302_;
v___y_3275_ = v___y_3303_;
v___y_3276_ = v___y_3304_;
v___y_3277_ = v___y_3305_;
v___y_3278_ = v___y_3306_;
v___y_3279_ = v___y_3307_;
v___y_3280_ = v___y_3308_;
v___y_3281_ = v___y_3309_;
v___y_3282_ = v___y_3310_;
v___y_3283_ = v___y_3311_;
v___y_3284_ = v___y_3312_;
v___y_3285_ = v___x_3316_;
goto v___jp_3263_;
}
else
{
lean_object* v_val_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_val_3317_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3315_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_val_3317_);
lean_dec(v___x_3315_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_val_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
v___y_3264_ = v___y_3293_;
v___y_3265_ = v___y_3294_;
v___y_3266_ = v___y_3295_;
v___y_3267_ = v_usingArg_3314_;
v___y_3268_ = v___y_3297_;
v___y_3269_ = v___y_3298_;
v___y_3270_ = v___y_3299_;
v___y_3271_ = v___y_3300_;
v___y_3272_ = v_usingTk_x3f_3313_;
v___y_3273_ = v___y_3301_;
v___y_3274_ = v___y_3302_;
v___y_3275_ = v___y_3303_;
v___y_3276_ = v___y_3304_;
v___y_3277_ = v___y_3305_;
v___y_3278_ = v___y_3306_;
v___y_3279_ = v___y_3307_;
v___y_3280_ = v___y_3308_;
v___y_3281_ = v___y_3309_;
v___y_3282_ = v___y_3310_;
v___y_3283_ = v___y_3311_;
v___y_3284_ = v___y_3312_;
v___y_3285_ = v___x_3322_;
goto v___jp_3263_;
}
}
}
}
v___jp_3325_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3347_ = lean_unsigned_to_nat(4u);
v___x_3348_ = l_Lean_Syntax_getArg(v___y_3337_, v___x_3347_);
lean_dec(v___y_3337_);
v___x_3349_ = l_Lean_Syntax_isNone(v___x_3348_);
if (v___x_3349_ == 0)
{
uint8_t v___x_3350_; 
lean_inc(v___x_3348_);
v___x_3350_ = l_Lean_Syntax_matchesNull(v___x_3348_, v___y_3329_);
lean_dec(v___y_3329_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; 
lean_dec(v___x_3348_);
lean_dec(v_args_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec(v___y_3328_);
lean_dec(v___y_3326_);
lean_dec(v_tk_3261_);
v___x_3351_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3351_;
}
else
{
lean_object* v_usingTk_x3f_3352_; lean_object* v_usingArg_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_usingTk_x3f_3352_ = l_Lean_Syntax_getArg(v___x_3348_, v___x_3260_);
v_usingArg_3353_ = l_Lean_Syntax_getArg(v___x_3348_, v___x_3262_);
lean_dec(v___x_3348_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_usingTk_x3f_3352_);
v___x_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_usingArg_3353_);
v___y_3293_ = v___y_3326_;
v___y_3294_ = v___y_3327_;
v___y_3295_ = v___y_3328_;
v___y_3296_ = v___y_3345_;
v___y_3297_ = v___y_3330_;
v___y_3298_ = v___y_3331_;
v___y_3299_ = v___y_3332_;
v___y_3300_ = v___y_3333_;
v___y_3301_ = v___y_3334_;
v___y_3302_ = v___y_3335_;
v___y_3303_ = v___y_3336_;
v___y_3304_ = v___y_3338_;
v___y_3305_ = v___y_3339_;
v___y_3306_ = v___y_3340_;
v___y_3307_ = v___y_3341_;
v___y_3308_ = v___y_3342_;
v___y_3309_ = v___y_3343_;
v___y_3310_ = v___y_3344_;
v___y_3311_ = v_args_3346_;
v___y_3312_ = v___x_3347_;
v_usingTk_x3f_3313_ = v___x_3354_;
v_usingArg_3314_ = v___x_3355_;
goto v___jp_3292_;
}
}
else
{
lean_object* v___x_3356_; 
lean_dec(v___x_3348_);
lean_dec(v___y_3329_);
v___x_3356_ = lean_box(0);
v___y_3293_ = v___y_3326_;
v___y_3294_ = v___y_3327_;
v___y_3295_ = v___y_3328_;
v___y_3296_ = v___y_3345_;
v___y_3297_ = v___y_3330_;
v___y_3298_ = v___y_3331_;
v___y_3299_ = v___y_3332_;
v___y_3300_ = v___y_3333_;
v___y_3301_ = v___y_3334_;
v___y_3302_ = v___y_3335_;
v___y_3303_ = v___y_3336_;
v___y_3304_ = v___y_3338_;
v___y_3305_ = v___y_3339_;
v___y_3306_ = v___y_3340_;
v___y_3307_ = v___y_3341_;
v___y_3308_ = v___y_3342_;
v___y_3309_ = v___y_3343_;
v___y_3310_ = v___y_3344_;
v___y_3311_ = v_args_3346_;
v___y_3312_ = v___x_3347_;
v_usingTk_x3f_3313_ = v___x_3356_;
v_usingArg_3314_ = v___x_3356_;
goto v___jp_3292_;
}
}
v___jp_3357_:
{
lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3379_ = l_Lean_Syntax_getArg(v___y_3367_, v___y_3366_);
lean_dec(v___y_3366_);
v___x_3380_ = l_Lean_Syntax_isNone(v___x_3379_);
if (v___x_3380_ == 0)
{
uint8_t v___x_3381_; 
lean_inc(v___x_3379_);
v___x_3381_ = l_Lean_Syntax_matchesNull(v___x_3379_, v___x_3262_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; 
lean_dec(v___x_3379_);
lean_dec(v_only_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3365_);
lean_dec(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec(v___y_3360_);
lean_dec(v___y_3358_);
lean_dec(v_tk_3261_);
v___x_3382_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3382_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3383_ = l_Lean_Syntax_getArg(v___x_3379_, v___x_3260_);
lean_dec(v___x_3379_);
v___x_3384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3383_);
v___x_3385_ = l_Lean_Syntax_isOfKind(v___x_3383_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; 
lean_dec(v___x_3383_);
lean_dec(v_only_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3365_);
lean_dec(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec(v___y_3360_);
lean_dec(v___y_3358_);
lean_dec(v_tk_3261_);
v___x_3386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; lean_object* v_args_3388_; lean_object* v___x_3389_; 
v___x_3387_ = l_Lean_Syntax_getArg(v___x_3383_, v___x_3262_);
lean_dec(v___x_3383_);
v_args_3388_ = l_Lean_Syntax_getArgs(v___x_3387_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_args_3388_);
v___y_3326_ = v___y_3358_;
v___y_3327_ = v___y_3359_;
v___y_3328_ = v___y_3360_;
v___y_3329_ = v___y_3369_;
v___y_3330_ = v___y_3371_;
v___y_3331_ = v___y_3376_;
v___y_3332_ = v___y_3377_;
v___y_3333_ = v___y_3372_;
v___y_3334_ = v___y_3374_;
v___y_3335_ = v___y_3375_;
v___y_3336_ = v___y_3361_;
v___y_3337_ = v___y_3367_;
v___y_3338_ = v___y_3373_;
v___y_3339_ = v___y_3378_;
v___y_3340_ = v___y_3362_;
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3365_;
v___y_3344_ = v_only_3370_;
v___y_3345_ = v___y_3368_;
v_args_3346_ = v___x_3389_;
goto v___jp_3325_;
}
}
}
else
{
lean_object* v___x_3390_; 
lean_dec(v___x_3379_);
v___x_3390_ = lean_box(0);
v___y_3326_ = v___y_3358_;
v___y_3327_ = v___y_3359_;
v___y_3328_ = v___y_3360_;
v___y_3329_ = v___y_3369_;
v___y_3330_ = v___y_3371_;
v___y_3331_ = v___y_3376_;
v___y_3332_ = v___y_3377_;
v___y_3333_ = v___y_3372_;
v___y_3334_ = v___y_3374_;
v___y_3335_ = v___y_3375_;
v___y_3336_ = v___y_3361_;
v___y_3337_ = v___y_3367_;
v___y_3338_ = v___y_3373_;
v___y_3339_ = v___y_3378_;
v___y_3340_ = v___y_3362_;
v___y_3341_ = v___y_3363_;
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3365_;
v___y_3344_ = v_only_3370_;
v___y_3345_ = v___y_3368_;
v_args_3346_ = v___x_3390_;
goto v___jp_3325_;
}
}
v___jp_3391_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3403_ = lean_unsigned_to_nat(3u);
v___x_3404_ = l_Lean_Syntax_getArg(v_stx_3242_, v___x_3403_);
lean_dec(v_stx_3242_);
v___x_3405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3404_);
v___x_3406_ = l_Lean_Syntax_isOfKind(v___x_3404_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; 
lean_dec(v___x_3404_);
lean_dec(v_unfold_3402_);
lean_dec(v___y_3398_);
lean_dec(v___y_3392_);
lean_dec(v_tk_3261_);
v___x_3407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3407_;
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3408_ = l_Lean_Syntax_getArg(v___x_3404_, v___x_3260_);
v___x_3409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3408_);
v___x_3410_ = l_Lean_Syntax_isOfKind(v___x_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
lean_dec(v___x_3408_);
lean_dec(v___x_3404_);
lean_dec(v_unfold_3402_);
lean_dec(v___y_3398_);
lean_dec(v___y_3392_);
lean_dec(v_tk_3261_);
v___x_3411_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3411_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = l_Lean_Syntax_getArg(v___x_3404_, v___x_3262_);
v___x_3413_ = l_Lean_Syntax_getArg(v___x_3404_, v___y_3398_);
v___x_3414_ = l_Lean_Syntax_isNone(v___x_3413_);
if (v___x_3414_ == 0)
{
uint8_t v___x_3415_; 
lean_inc(v___x_3413_);
v___x_3415_ = l_Lean_Syntax_matchesNull(v___x_3413_, v___x_3262_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
lean_dec(v___x_3413_);
lean_dec(v___x_3412_);
lean_dec(v___x_3408_);
lean_dec(v___x_3404_);
lean_dec(v_unfold_3402_);
lean_dec(v___y_3398_);
lean_dec(v___y_3392_);
lean_dec(v_tk_3261_);
v___x_3416_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3416_;
}
else
{
lean_object* v_only_3417_; lean_object* v___x_3418_; 
v_only_3417_ = l_Lean_Syntax_getArg(v___x_3413_, v___x_3260_);
lean_dec(v___x_3413_);
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_only_3417_);
lean_inc(v___y_3398_);
v___y_3358_ = v___x_3403_;
v___y_3359_ = v___x_3409_;
v___y_3360_ = v___y_3392_;
v___y_3361_ = v___x_3410_;
v___y_3362_ = v___x_3408_;
v___y_3363_ = v_unfold_3402_;
v___y_3364_ = v___x_3405_;
v___y_3365_ = v___y_3398_;
v___y_3366_ = v___x_3403_;
v___y_3367_ = v___x_3404_;
v___y_3368_ = v___x_3412_;
v___y_3369_ = v___y_3398_;
v_only_3370_ = v___x_3418_;
v___y_3371_ = v___y_3397_;
v___y_3372_ = v___y_3396_;
v___y_3373_ = v___y_3401_;
v___y_3374_ = v___y_3393_;
v___y_3375_ = v___y_3400_;
v___y_3376_ = v___y_3394_;
v___y_3377_ = v___y_3395_;
v___y_3378_ = v___y_3399_;
goto v___jp_3357_;
}
}
else
{
lean_object* v___x_3419_; 
lean_dec(v___x_3413_);
v___x_3419_ = lean_box(0);
lean_inc(v___y_3398_);
v___y_3358_ = v___x_3403_;
v___y_3359_ = v___x_3409_;
v___y_3360_ = v___y_3392_;
v___y_3361_ = v___x_3410_;
v___y_3362_ = v___x_3408_;
v___y_3363_ = v_unfold_3402_;
v___y_3364_ = v___x_3405_;
v___y_3365_ = v___y_3398_;
v___y_3366_ = v___x_3403_;
v___y_3367_ = v___x_3404_;
v___y_3368_ = v___x_3412_;
v___y_3369_ = v___y_3398_;
v_only_3370_ = v___x_3419_;
v___y_3371_ = v___y_3397_;
v___y_3372_ = v___y_3396_;
v___y_3373_ = v___y_3401_;
v___y_3374_ = v___y_3393_;
v___y_3375_ = v___y_3400_;
v___y_3376_ = v___y_3394_;
v___y_3377_ = v___y_3395_;
v___y_3378_ = v___y_3399_;
goto v___jp_3357_;
}
}
}
}
v___jp_3420_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3430_ = lean_unsigned_to_nat(2u);
v___x_3431_ = l_Lean_Syntax_getArg(v_stx_3242_, v___x_3430_);
v___x_3432_ = l_Lean_Syntax_isNone(v___x_3431_);
if (v___x_3432_ == 0)
{
uint8_t v___x_3433_; 
lean_inc(v___x_3431_);
v___x_3433_ = l_Lean_Syntax_matchesNull(v___x_3431_, v___x_3262_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; 
lean_dec(v___x_3431_);
lean_dec(v_squeeze_3421_);
lean_dec(v_tk_3261_);
lean_dec(v_stx_3242_);
v___x_3434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3434_;
}
else
{
lean_object* v_unfold_3435_; lean_object* v___x_3436_; 
v_unfold_3435_ = l_Lean_Syntax_getArg(v___x_3431_, v___x_3260_);
lean_dec(v___x_3431_);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v_unfold_3435_);
v___y_3392_ = v_squeeze_3421_;
v___y_3393_ = v___y_3425_;
v___y_3394_ = v___y_3427_;
v___y_3395_ = v___y_3428_;
v___y_3396_ = v___y_3423_;
v___y_3397_ = v___y_3422_;
v___y_3398_ = v___x_3430_;
v___y_3399_ = v___y_3429_;
v___y_3400_ = v___y_3426_;
v___y_3401_ = v___y_3424_;
v_unfold_3402_ = v___x_3436_;
goto v___jp_3391_;
}
}
else
{
lean_object* v___x_3437_; 
lean_dec(v___x_3431_);
v___x_3437_ = lean_box(0);
v___y_3392_ = v_squeeze_3421_;
v___y_3393_ = v___y_3425_;
v___y_3394_ = v___y_3427_;
v___y_3395_ = v___y_3428_;
v___y_3396_ = v___y_3423_;
v___y_3397_ = v___y_3422_;
v___y_3398_ = v___x_3430_;
v___y_3399_ = v___y_3429_;
v___y_3400_ = v___y_3426_;
v___y_3401_ = v___y_3424_;
v_unfold_3402_ = v___x_3437_;
goto v___jp_3391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3445_, lean_object* v_stx_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
uint8_t v_useReducible_boxed_3456_; lean_object* v_res_3457_; 
v_useReducible_boxed_3456_ = lean_unbox(v_useReducible_3445_);
v_res_3457_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3456_, v_stx_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3458_, lean_object* v_val_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3458_, v_val_3459_, v___y_3465_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3470_, lean_object* v_val_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3470_, v_val_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3482_, v___y_3490_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v_00_u03b1_3504_, lean_object* v_msg_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_3505_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v_00_u03b1_3516_, lean_object* v_msg_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_3516_, v_msg_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_00_u03b1_3528_, lean_object* v_x_3529_, lean_object* v_mkInfoTree_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_3529_, v_mkInfoTree_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_00_u03b1_3541_, lean_object* v_x_3542_, lean_object* v_mkInfoTree_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_3541_, v_x_3542_, v_mkInfoTree_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3554_, lean_object* v_x_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3555_, v_x_3556_, v_x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3559_, lean_object* v_m_3560_, lean_object* v_a_3561_){
_start:
{
uint8_t v___x_3562_; 
v___x_3562_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3560_, v_a_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3563_, lean_object* v_m_3564_, lean_object* v_a_3565_){
_start:
{
uint8_t v_res_3566_; lean_object* v_r_3567_; 
v_res_3566_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_3563_, v_m_3564_, v_a_3565_);
lean_dec_ref(v_a_3565_);
lean_dec_ref(v_m_3564_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_mvarId_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_3568_, v___y_3569_, v___y_3575_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___boxed(lean_object* v_mvarId_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(v_mvarId_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v_mvarId_3580_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17(lean_object* v_mvarId_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___redArg(v_mvarId_3592_, v___y_3593_, v___y_3599_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17___boxed(lean_object* v_mvarId_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__17(v_mvarId_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v_mvarId_3604_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_3616_, lean_object* v_m_3617_, lean_object* v_query_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___redArg(v_m_3617_, v_query_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object* v_00_u03b2_3620_, lean_object* v_m_3621_, lean_object* v_query_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_00_u03b2_3620_, v_m_3621_, v_query_3622_);
lean_dec_ref(v_query_3622_);
lean_dec_ref(v_m_3621_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9(lean_object* v_00_u03b2_3624_, lean_object* v_m_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___redArg(v_m_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3627_, lean_object* v_m_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9(v_00_u03b2_3627_, v_m_3628_);
lean_dec_ref(v_m_3628_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12(lean_object* v_00_u03b2_3630_, lean_object* v_x_3631_, size_t v_x_3632_, size_t v_x_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___redArg(v_x_3631_, v_x_3632_, v_x_3633_, v_x_3634_, v_x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12___boxed(lean_object* v_00_u03b2_3637_, lean_object* v_x_3638_, lean_object* v_x_3639_, lean_object* v_x_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_){
_start:
{
size_t v_x_98822__boxed_3643_; size_t v_x_98823__boxed_3644_; lean_object* v_res_3645_; 
v_x_98822__boxed_3643_ = lean_unbox_usize(v_x_3639_);
lean_dec(v_x_3639_);
v_x_98823__boxed_3644_ = lean_unbox_usize(v_x_3640_);
lean_dec(v_x_3640_);
v_res_3645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12(v_00_u03b2_3637_, v_x_3638_, v_x_98822__boxed_3643_, v_x_98823__boxed_3644_, v_x_3641_, v_x_3642_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17(lean_object* v_ref_3646_, lean_object* v_msgData_3647_, uint8_t v_severity_3648_, uint8_t v_isSilent_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___redArg(v_ref_3646_, v_msgData_3647_, v_severity_3648_, v_isSilent_3649_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17___boxed(lean_object* v_ref_3660_, lean_object* v_msgData_3661_, lean_object* v_severity_3662_, lean_object* v_isSilent_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v_severity_boxed_3673_; uint8_t v_isSilent_boxed_3674_; lean_object* v_res_3675_; 
v_severity_boxed_3673_ = lean_unbox(v_severity_3662_);
v_isSilent_boxed_3674_ = lean_unbox(v_isSilent_3663_);
v_res_3675_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__17(v_ref_3660_, v_msgData_3661_, v_severity_boxed_3673_, v_isSilent_boxed_3674_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v_ref_3660_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3676_, lean_object* v_m_3677_, lean_object* v_query_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_m_3677_, v_query_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3680_, lean_object* v_m_3681_, lean_object* v_query_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3680_, v_m_3681_, v_query_3682_);
lean_dec_ref(v_query_3682_);
lean_dec_ref(v_m_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object* v_00_u03b2_3684_, lean_object* v_m_3685_, lean_object* v_query_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_x_3689_, lean_object* v_x_3690_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_m_3685_, v_query_3686_, v_x_3687_, v_x_3688_, v_x_3689_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_00_u03b2_3692_, lean_object* v_m_3693_, lean_object* v_query_3694_, lean_object* v_x_3695_, lean_object* v_x_3696_, lean_object* v_x_3697_, lean_object* v_x_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_00_u03b2_3692_, v_m_3693_, v_query_3694_, v_x_3695_, v_x_3696_, v_x_3697_, v_x_3698_);
lean_dec_ref(v_query_3694_);
lean_dec_ref(v_m_3693_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21(lean_object* v_00_u03b2_3700_, lean_object* v_init_3701_, lean_object* v_b_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___redArg(v_init_3701_, v_b_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21___boxed(lean_object* v_00_u03b2_3704_, lean_object* v_init_3705_, lean_object* v_b_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21(v_00_u03b2_3704_, v_init_3705_, v_b_3706_);
lean_dec_ref(v_b_3706_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24(lean_object* v_00_u03b2_3708_, lean_object* v_n_3709_, lean_object* v_k_3710_, lean_object* v_v_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24___redArg(v_n_3709_, v_k_3710_, v_v_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25(lean_object* v_00_u03b2_3713_, size_t v_depth_3714_, lean_object* v_keys_3715_, lean_object* v_vals_3716_, lean_object* v_heq_3717_, lean_object* v_i_3718_, lean_object* v_entries_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___redArg(v_depth_3714_, v_keys_3715_, v_vals_3716_, v_i_3718_, v_entries_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25___boxed(lean_object* v_00_u03b2_3721_, lean_object* v_depth_3722_, lean_object* v_keys_3723_, lean_object* v_vals_3724_, lean_object* v_heq_3725_, lean_object* v_i_3726_, lean_object* v_entries_3727_){
_start:
{
size_t v_depth_boxed_3728_; lean_object* v_res_3729_; 
v_depth_boxed_3728_ = lean_unbox_usize(v_depth_3722_);
lean_dec(v_depth_3722_);
v_res_3729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__25(v_00_u03b2_3721_, v_depth_boxed_3728_, v_keys_3723_, v_vals_3724_, v_heq_3725_, v_i_3726_, v_entries_3727_);
lean_dec_ref(v_vals_3724_);
lean_dec_ref(v_keys_3723_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24(lean_object* v_00_u03b2_3730_, lean_object* v_b_3731_, lean_object* v_acc_3732_, lean_object* v_i_3733_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___redArg(v_b_3731_, v_acc_3732_, v_i_3733_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24___boxed(lean_object* v_00_u03b2_3735_, lean_object* v_b_3736_, lean_object* v_acc_3737_, lean_object* v_i_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__9_spec__21_spec__24(v_00_u03b2_3735_, v_b_3736_, v_acc_3737_, v_i_3738_);
lean_dec_ref(v_b_3736_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24_spec__27(lean_object* v_00_u03b2_3740_, lean_object* v_x_3741_, lean_object* v_x_3742_, lean_object* v_x_3743_, lean_object* v_x_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__12_spec__24_spec__27___redArg(v_x_3741_, v_x_3742_, v_x_3743_, v_x_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
uint8_t v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = 1;
v___x_3757_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_3756_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3778_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3781_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3782_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3778_, v___x_3779_, v___x_3780_, v___x_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3813_ = l_Lean_addBuiltinDeclarationRanges(v___x_3811_, v___x_3812_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_3818_){
_start:
{
lean_object* v___x_3819_; 
v___x_3819_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_3820_);
lean_dec(v_x_3820_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; uint8_t v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___x_3874_; uint8_t v___x_3875_; 
v___x_3874_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_3833_);
v___x_3875_ = l_Lean_Syntax_isOfKind(v_stx_3833_, v___x_3874_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; 
lean_dec(v_stx_3833_);
v___x_3876_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3876_;
}
else
{
lean_object* v___x_3877_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; uint8_t v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; uint8_t v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; uint8_t v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; uint8_t v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v_tk_4004_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v_args_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___x_4064_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v_only_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v_unfold_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v_squeeze_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_3877_ = lean_unsigned_to_nat(0u);
v_tk_4004_ = l_Lean_Syntax_getArg(v_stx_3833_, v___x_3877_);
v___x_4064_ = lean_unsigned_to_nat(1u);
v___x_4140_ = l_Lean_Syntax_getArg(v_stx_3833_, v___x_4064_);
v___x_4141_ = l_Lean_Syntax_isNone(v___x_4140_);
if (v___x_4141_ == 0)
{
uint8_t v___x_4142_; 
lean_inc(v___x_4140_);
v___x_4142_ = l_Lean_Syntax_matchesNull(v___x_4140_, v___x_4064_);
if (v___x_4142_ == 0)
{
lean_object* v___x_4143_; 
lean_dec(v___x_4140_);
lean_dec(v_tk_4004_);
lean_dec(v_stx_3833_);
v___x_4143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4143_;
}
else
{
lean_object* v_squeeze_4144_; lean_object* v___x_4145_; 
v_squeeze_4144_ = l_Lean_Syntax_getArg(v___x_4140_, v___x_3877_);
lean_dec(v___x_4140_);
v___x_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4145_, 0, v_squeeze_4144_);
v_squeeze_4123_ = v___x_4145_;
v___y_4124_ = v_a_3834_;
v___y_4125_ = v_a_3835_;
v___y_4126_ = v_a_3836_;
v___y_4127_ = v_a_3837_;
v___y_4128_ = v_a_3838_;
v___y_4129_ = v_a_3839_;
v___y_4130_ = v_a_3840_;
v___y_4131_ = v_a_3841_;
goto v___jp_4122_;
}
}
else
{
lean_object* v___x_4146_; 
lean_dec(v___x_4140_);
v___x_4146_ = lean_box(0);
v_squeeze_4123_ = v___x_4146_;
v___y_4124_ = v_a_3834_;
v___y_4125_ = v_a_3835_;
v___y_4126_ = v_a_3836_;
v___y_4127_ = v_a_3837_;
v___y_4128_ = v_a_3838_;
v___y_4129_ = v_a_3839_;
v___y_4130_ = v_a_3840_;
v___y_4131_ = v_a_3841_;
goto v___jp_4122_;
}
v___jp_3878_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
lean_inc_ref(v___y_3881_);
v___x_3901_ = l_Array_append___redArg(v___y_3881_, v___y_3900_);
lean_dec_ref(v___y_3900_);
lean_inc(v___y_3880_);
lean_inc(v___y_3890_);
v___x_3902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3902_, 0, v___y_3890_);
lean_ctor_set(v___x_3902_, 1, v___y_3880_);
lean_ctor_set(v___x_3902_, 2, v___x_3901_);
if (lean_obj_tag(v___y_3888_) == 1)
{
lean_object* v_val_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_val_3903_ = lean_ctor_get(v___y_3888_, 0);
lean_inc(v_val_3903_);
lean_dec_ref_known(v___y_3888_, 1);
v___x_3904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3890_, 4);
v___x_3906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___y_3890_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
lean_inc_ref(v___y_3881_);
v___x_3907_ = l_Array_append___redArg(v___y_3881_, v_val_3903_);
lean_dec(v_val_3903_);
lean_inc(v___y_3880_);
v___x_3908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3908_, 0, v___y_3890_);
lean_ctor_set(v___x_3908_, 1, v___y_3880_);
lean_ctor_set(v___x_3908_, 2, v___x_3907_);
v___x_3909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___y_3890_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = l_Lean_Syntax_node3(v___y_3890_, v___x_3904_, v___x_3906_, v___x_3908_, v___x_3910_);
v___x_3912_ = l_Array_mkArray1___redArg(v___x_3911_);
v___y_3844_ = v___y_3896_;
v___y_3845_ = v___y_3880_;
v___y_3846_ = v___y_3881_;
v___y_3847_ = v___y_3882_;
v___y_3848_ = v___y_3883_;
v___y_3849_ = v___y_3884_;
v___y_3850_ = v___y_3885_;
v___y_3851_ = v___y_3886_;
v___y_3852_ = v___y_3887_;
v___y_3853_ = v___y_3889_;
v___y_3854_ = v___y_3890_;
v___y_3855_ = v___y_3891_;
v___y_3856_ = v___y_3892_;
v___y_3857_ = v___x_3902_;
v___y_3858_ = v___y_3893_;
v___y_3859_ = v___y_3894_;
v___y_3860_ = v___y_3895_;
v___y_3861_ = v___y_3897_;
v___y_3862_ = v___y_3898_;
v___y_3863_ = v___y_3899_;
v___y_3864_ = v___y_3879_;
v___y_3865_ = v___x_3912_;
goto v___jp_3843_;
}
else
{
lean_object* v___x_3913_; 
lean_dec(v___y_3888_);
v___x_3913_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3844_ = v___y_3896_;
v___y_3845_ = v___y_3880_;
v___y_3846_ = v___y_3881_;
v___y_3847_ = v___y_3882_;
v___y_3848_ = v___y_3883_;
v___y_3849_ = v___y_3884_;
v___y_3850_ = v___y_3885_;
v___y_3851_ = v___y_3886_;
v___y_3852_ = v___y_3887_;
v___y_3853_ = v___y_3889_;
v___y_3854_ = v___y_3890_;
v___y_3855_ = v___y_3891_;
v___y_3856_ = v___y_3892_;
v___y_3857_ = v___x_3902_;
v___y_3858_ = v___y_3893_;
v___y_3859_ = v___y_3894_;
v___y_3860_ = v___y_3895_;
v___y_3861_ = v___y_3897_;
v___y_3862_ = v___y_3898_;
v___y_3863_ = v___y_3899_;
v___y_3864_ = v___y_3879_;
v___y_3865_ = v___x_3913_;
goto v___jp_3843_;
}
}
v___jp_3914_:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_inc_ref(v___y_3917_);
v___x_3937_ = l_Array_append___redArg(v___y_3917_, v___y_3936_);
lean_dec_ref(v___y_3936_);
lean_inc(v___y_3916_);
lean_inc(v___y_3926_);
v___x_3938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3938_, 0, v___y_3926_);
lean_ctor_set(v___x_3938_, 1, v___y_3916_);
lean_ctor_set(v___x_3938_, 2, v___x_3937_);
if (lean_obj_tag(v___y_3921_) == 1)
{
lean_object* v_val_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_val_3939_ = lean_ctor_get(v___y_3921_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v___y_3921_, 1);
v___x_3940_ = l_Lean_SourceInfo_fromRef(v_val_3939_, v___x_3875_);
lean_dec(v_val_3939_);
v___x_3941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
v___x_3943_ = l_Array_mkArray1___redArg(v___x_3942_);
v___y_3879_ = v___y_3935_;
v___y_3880_ = v___y_3916_;
v___y_3881_ = v___y_3917_;
v___y_3882_ = v___y_3918_;
v___y_3883_ = v___y_3919_;
v___y_3884_ = v___y_3920_;
v___y_3885_ = v___y_3922_;
v___y_3886_ = v___x_3938_;
v___y_3887_ = v___y_3924_;
v___y_3888_ = v___y_3923_;
v___y_3889_ = v___y_3925_;
v___y_3890_ = v___y_3926_;
v___y_3891_ = v___y_3927_;
v___y_3892_ = v___y_3928_;
v___y_3893_ = v___y_3929_;
v___y_3894_ = v___y_3930_;
v___y_3895_ = v___y_3931_;
v___y_3896_ = v___y_3932_;
v___y_3897_ = v___y_3933_;
v___y_3898_ = v___y_3934_;
v___y_3899_ = v___y_3915_;
v___y_3900_ = v___x_3943_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3921_);
lean_dec(v___y_3921_);
v___y_3879_ = v___y_3935_;
v___y_3880_ = v___y_3916_;
v___y_3881_ = v___y_3917_;
v___y_3882_ = v___y_3918_;
v___y_3883_ = v___y_3919_;
v___y_3884_ = v___y_3920_;
v___y_3885_ = v___y_3922_;
v___y_3886_ = v___x_3938_;
v___y_3887_ = v___y_3924_;
v___y_3888_ = v___y_3923_;
v___y_3889_ = v___y_3925_;
v___y_3890_ = v___y_3926_;
v___y_3891_ = v___y_3927_;
v___y_3892_ = v___y_3928_;
v___y_3893_ = v___y_3929_;
v___y_3894_ = v___y_3930_;
v___y_3895_ = v___y_3931_;
v___y_3896_ = v___y_3932_;
v___y_3897_ = v___y_3933_;
v___y_3898_ = v___y_3934_;
v___y_3899_ = v___y_3915_;
v___y_3900_ = v___x_3944_;
goto v___jp_3878_;
}
}
v___jp_3945_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_inc_ref(v___y_3948_);
v___x_3967_ = l_Array_append___redArg(v___y_3948_, v___y_3966_);
lean_dec_ref(v___y_3966_);
lean_inc(v___y_3947_);
lean_inc(v___y_3957_);
v___x_3968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3968_, 0, v___y_3957_);
lean_ctor_set(v___x_3968_, 1, v___y_3947_);
lean_ctor_set(v___x_3968_, 2, v___x_3967_);
v___x_3969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_3951_) == 0)
{
lean_object* v___x_3970_; 
v___x_3970_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3915_ = v___y_3964_;
v___y_3916_ = v___y_3947_;
v___y_3917_ = v___y_3948_;
v___y_3918_ = v___y_3949_;
v___y_3919_ = v___y_3950_;
v___y_3920_ = v___x_3968_;
v___y_3921_ = v___y_3952_;
v___y_3922_ = v___y_3953_;
v___y_3923_ = v___y_3954_;
v___y_3924_ = v___y_3955_;
v___y_3925_ = v___y_3956_;
v___y_3926_ = v___y_3957_;
v___y_3927_ = v___y_3958_;
v___y_3928_ = v___y_3959_;
v___y_3929_ = v___y_3960_;
v___y_3930_ = v___x_3969_;
v___y_3931_ = v___y_3961_;
v___y_3932_ = v___y_3962_;
v___y_3933_ = v___y_3963_;
v___y_3934_ = v___y_3965_;
v___y_3935_ = v___y_3946_;
v___y_3936_ = v___x_3970_;
goto v___jp_3914_;
}
else
{
lean_object* v_val_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_val_3971_ = lean_ctor_get(v___y_3951_, 0);
lean_inc(v_val_3971_);
lean_dec_ref_known(v___y_3951_, 1);
v___x_3972_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3973_ = lean_array_push(v___x_3972_, v_val_3971_);
v___y_3915_ = v___y_3964_;
v___y_3916_ = v___y_3947_;
v___y_3917_ = v___y_3948_;
v___y_3918_ = v___y_3949_;
v___y_3919_ = v___y_3950_;
v___y_3920_ = v___x_3968_;
v___y_3921_ = v___y_3952_;
v___y_3922_ = v___y_3953_;
v___y_3923_ = v___y_3954_;
v___y_3924_ = v___y_3955_;
v___y_3925_ = v___y_3956_;
v___y_3926_ = v___y_3957_;
v___y_3927_ = v___y_3958_;
v___y_3928_ = v___y_3959_;
v___y_3929_ = v___y_3960_;
v___y_3930_ = v___x_3969_;
v___y_3931_ = v___y_3961_;
v___y_3932_ = v___y_3962_;
v___y_3933_ = v___y_3963_;
v___y_3934_ = v___y_3965_;
v___y_3935_ = v___y_3946_;
v___y_3936_ = v___x_3973_;
goto v___jp_3914_;
}
}
v___jp_3974_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
lean_inc_ref(v___y_3978_);
v___x_3996_ = l_Array_append___redArg(v___y_3978_, v___y_3995_);
lean_dec_ref(v___y_3995_);
lean_inc(v___y_3976_);
lean_inc(v___y_3986_);
v___x_3997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3997_, 0, v___y_3986_);
lean_ctor_set(v___x_3997_, 1, v___y_3976_);
lean_ctor_set(v___x_3997_, 2, v___x_3996_);
if (lean_obj_tag(v___y_3977_) == 1)
{
lean_object* v_val_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v_val_3998_ = lean_ctor_get(v___y_3977_, 0);
lean_inc(v_val_3998_);
lean_dec_ref_known(v___y_3977_, 1);
v___x_3999_ = l_Lean_SourceInfo_fromRef(v_val_3998_, v___x_3875_);
lean_dec(v_val_3998_);
v___x_4000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_4001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3999_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = l_Array_mkArray1___redArg(v___x_4001_);
v___y_3946_ = v___y_3994_;
v___y_3947_ = v___y_3976_;
v___y_3948_ = v___y_3978_;
v___y_3949_ = v___y_3979_;
v___y_3950_ = v___y_3980_;
v___y_3951_ = v___y_3981_;
v___y_3952_ = v___y_3982_;
v___y_3953_ = v___x_3997_;
v___y_3954_ = v___y_3983_;
v___y_3955_ = v___y_3984_;
v___y_3956_ = v___y_3985_;
v___y_3957_ = v___y_3986_;
v___y_3958_ = v___y_3987_;
v___y_3959_ = v___y_3988_;
v___y_3960_ = v___y_3989_;
v___y_3961_ = v___y_3990_;
v___y_3962_ = v___y_3991_;
v___y_3963_ = v___y_3992_;
v___y_3964_ = v___y_3993_;
v___y_3965_ = v___y_3975_;
v___y_3966_ = v___x_4002_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3977_);
lean_dec(v___y_3977_);
v___y_3946_ = v___y_3994_;
v___y_3947_ = v___y_3976_;
v___y_3948_ = v___y_3978_;
v___y_3949_ = v___y_3979_;
v___y_3950_ = v___y_3980_;
v___y_3951_ = v___y_3981_;
v___y_3952_ = v___y_3982_;
v___y_3953_ = v___x_3997_;
v___y_3954_ = v___y_3983_;
v___y_3955_ = v___y_3984_;
v___y_3956_ = v___y_3985_;
v___y_3957_ = v___y_3986_;
v___y_3958_ = v___y_3987_;
v___y_3959_ = v___y_3988_;
v___y_3960_ = v___y_3989_;
v___y_3961_ = v___y_3990_;
v___y_3962_ = v___y_3991_;
v___y_3963_ = v___y_3992_;
v___y_3964_ = v___y_3993_;
v___y_3965_ = v___y_3975_;
v___y_3966_ = v___x_4003_;
goto v___jp_3945_;
}
}
v___jp_4005_:
{
lean_object* v_ref_4021_; uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_ref_4021_ = lean_ctor_get(v___y_4012_, 5);
v___x_4022_ = 0;
v___x_4023_ = l_Lean_SourceInfo_fromRef(v_ref_4021_, v___x_4022_);
v___x_4024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4025_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4026_ = l_Lean_SourceInfo_fromRef(v_tk_4004_, v___x_3875_);
lean_dec(v_tk_4004_);
v___x_4027_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
lean_ctor_set(v___x_4027_, 1, v___x_4024_);
v___x_4028_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_4029_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_4015_) == 1)
{
lean_object* v_val_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_val_4030_ = lean_ctor_get(v___y_4015_, 0);
lean_inc(v_val_4030_);
lean_dec_ref_known(v___y_4015_, 1);
v___x_4031_ = l_Lean_SourceInfo_fromRef(v_val_4030_, v___x_3875_);
lean_dec(v_val_4030_);
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = l_Array_mkArray1___redArg(v___x_4033_);
v___y_3975_ = v___y_4016_;
v___y_3976_ = v___x_4028_;
v___y_3977_ = v___y_4006_;
v___y_3978_ = v___x_4029_;
v___y_3979_ = v___y_4007_;
v___y_3980_ = v___y_4008_;
v___y_3981_ = v___y_4020_;
v___y_3982_ = v___y_4009_;
v___y_3983_ = v___y_4010_;
v___y_3984_ = v___x_4022_;
v___y_3985_ = v___x_4025_;
v___y_3986_ = v___x_4023_;
v___y_3987_ = v___y_4011_;
v___y_3988_ = v___y_4012_;
v___y_3989_ = v___y_4013_;
v___y_3990_ = v___y_4014_;
v___y_3991_ = v___y_4017_;
v___y_3992_ = v___x_4027_;
v___y_3993_ = v___y_4018_;
v___y_3994_ = v___y_4019_;
v___y_3995_ = v___x_4034_;
goto v___jp_3974_;
}
else
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4015_);
lean_dec(v___y_4015_);
v___y_3975_ = v___y_4016_;
v___y_3976_ = v___x_4028_;
v___y_3977_ = v___y_4006_;
v___y_3978_ = v___x_4029_;
v___y_3979_ = v___y_4007_;
v___y_3980_ = v___y_4008_;
v___y_3981_ = v___y_4020_;
v___y_3982_ = v___y_4009_;
v___y_3983_ = v___y_4010_;
v___y_3984_ = v___x_4022_;
v___y_3985_ = v___x_4025_;
v___y_3986_ = v___x_4023_;
v___y_3987_ = v___y_4011_;
v___y_3988_ = v___y_4012_;
v___y_3989_ = v___y_4013_;
v___y_3990_ = v___y_4014_;
v___y_3991_ = v___y_4017_;
v___y_3992_ = v___x_4027_;
v___y_3993_ = v___y_4018_;
v___y_3994_ = v___y_4019_;
v___y_3995_ = v___x_4035_;
goto v___jp_3974_;
}
}
v___jp_4036_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = lean_unsigned_to_nat(5u);
v___x_4053_ = l_Lean_Syntax_getArg(v___y_4038_, v___x_4052_);
lean_dec(v___y_4038_);
v___x_4054_ = l_Lean_Syntax_getOptional_x3f(v___y_4040_);
lean_dec(v___y_4040_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v___x_4055_; 
v___x_4055_ = lean_box(0);
v___y_4006_ = v___y_4037_;
v___y_4007_ = v___y_4047_;
v___y_4008_ = v___y_4046_;
v___y_4009_ = v___y_4041_;
v___y_4010_ = v_args_4043_;
v___y_4011_ = v___x_4053_;
v___y_4012_ = v___y_4050_;
v___y_4013_ = v___y_4051_;
v___y_4014_ = v___y_4049_;
v___y_4015_ = v___y_4039_;
v___y_4016_ = v___y_4045_;
v___y_4017_ = v___y_4048_;
v___y_4018_ = v___y_4044_;
v___y_4019_ = v___y_4042_;
v___y_4020_ = v___x_4055_;
goto v___jp_4005_;
}
else
{
lean_object* v_val_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
v_val_4056_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4054_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_val_4056_);
lean_dec(v___x_4054_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_val_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
v___y_4006_ = v___y_4037_;
v___y_4007_ = v___y_4047_;
v___y_4008_ = v___y_4046_;
v___y_4009_ = v___y_4041_;
v___y_4010_ = v_args_4043_;
v___y_4011_ = v___x_4053_;
v___y_4012_ = v___y_4050_;
v___y_4013_ = v___y_4051_;
v___y_4014_ = v___y_4049_;
v___y_4015_ = v___y_4039_;
v___y_4016_ = v___y_4045_;
v___y_4017_ = v___y_4048_;
v___y_4018_ = v___y_4044_;
v___y_4019_ = v___y_4042_;
v___y_4020_ = v___x_4061_;
goto v___jp_4005_;
}
}
}
}
v___jp_4065_:
{
lean_object* v___x_4081_; uint8_t v___x_4082_; 
v___x_4081_ = l_Lean_Syntax_getArg(v___y_4067_, v___y_4070_);
v___x_4082_ = l_Lean_Syntax_isNone(v___x_4081_);
if (v___x_4082_ == 0)
{
uint8_t v___x_4083_; 
lean_inc(v___x_4081_);
v___x_4083_ = l_Lean_Syntax_matchesNull(v___x_4081_, v___x_4064_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4084_; 
lean_dec(v___x_4081_);
lean_dec(v_only_4072_);
lean_dec(v___y_4071_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v_tk_4004_);
v___x_4084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4084_;
}
else
{
lean_object* v___x_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; 
v___x_4085_ = l_Lean_Syntax_getArg(v___x_4081_, v___x_3877_);
lean_dec(v___x_4081_);
v___x_4086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4085_);
v___x_4087_ = l_Lean_Syntax_isOfKind(v___x_4085_, v___x_4086_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4088_; 
lean_dec(v___x_4085_);
lean_dec(v_only_4072_);
lean_dec(v___y_4071_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec(v_tk_4004_);
v___x_4088_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4088_;
}
else
{
lean_object* v___x_4089_; lean_object* v_args_4090_; lean_object* v___x_4091_; 
v___x_4089_ = l_Lean_Syntax_getArg(v___x_4085_, v___x_4064_);
lean_dec(v___x_4085_);
v_args_4090_ = l_Lean_Syntax_getArgs(v___x_4089_);
lean_dec(v___x_4089_);
v___x_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_args_4090_);
v___y_4037_ = v___y_4066_;
v___y_4038_ = v___y_4067_;
v___y_4039_ = v___y_4068_;
v___y_4040_ = v___y_4069_;
v___y_4041_ = v_only_4072_;
v___y_4042_ = v___y_4071_;
v_args_4043_ = v___x_4091_;
v___y_4044_ = v___y_4073_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4075_;
v___y_4047_ = v___y_4076_;
v___y_4048_ = v___y_4077_;
v___y_4049_ = v___y_4078_;
v___y_4050_ = v___y_4079_;
v___y_4051_ = v___y_4080_;
goto v___jp_4036_;
}
}
}
else
{
lean_object* v___x_4092_; 
lean_dec(v___x_4081_);
v___x_4092_ = lean_box(0);
v___y_4037_ = v___y_4066_;
v___y_4038_ = v___y_4067_;
v___y_4039_ = v___y_4068_;
v___y_4040_ = v___y_4069_;
v___y_4041_ = v_only_4072_;
v___y_4042_ = v___y_4071_;
v_args_4043_ = v___x_4092_;
v___y_4044_ = v___y_4073_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4075_;
v___y_4047_ = v___y_4076_;
v___y_4048_ = v___y_4077_;
v___y_4049_ = v___y_4078_;
v___y_4050_ = v___y_4079_;
v___y_4051_ = v___y_4080_;
goto v___jp_4036_;
}
}
v___jp_4093_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; 
v___x_4105_ = lean_unsigned_to_nat(3u);
v___x_4106_ = l_Lean_Syntax_getArg(v_stx_3833_, v___x_4105_);
lean_dec(v_stx_3833_);
v___x_4107_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4106_);
v___x_4108_ = l_Lean_Syntax_isOfKind(v___x_4106_, v___x_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; 
lean_dec(v___x_4106_);
lean_dec(v_unfold_4096_);
lean_dec(v___y_4095_);
lean_dec(v_tk_4004_);
v___x_4109_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4109_;
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4110_ = l_Lean_Syntax_getArg(v___x_4106_, v___x_3877_);
v___x_4111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4110_);
v___x_4112_ = l_Lean_Syntax_isOfKind(v___x_4110_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; 
lean_dec(v___x_4110_);
lean_dec(v___x_4106_);
lean_dec(v_unfold_4096_);
lean_dec(v___y_4095_);
lean_dec(v_tk_4004_);
v___x_4113_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4113_;
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4114_ = l_Lean_Syntax_getArg(v___x_4106_, v___x_4064_);
v___x_4115_ = l_Lean_Syntax_getArg(v___x_4106_, v___y_4094_);
v___x_4116_ = l_Lean_Syntax_isNone(v___x_4115_);
if (v___x_4116_ == 0)
{
uint8_t v___x_4117_; 
lean_inc(v___x_4115_);
v___x_4117_ = l_Lean_Syntax_matchesNull(v___x_4115_, v___x_4064_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; 
lean_dec(v___x_4115_);
lean_dec(v___x_4114_);
lean_dec(v___x_4110_);
lean_dec(v___x_4106_);
lean_dec(v_unfold_4096_);
lean_dec(v___y_4095_);
lean_dec(v_tk_4004_);
v___x_4118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4118_;
}
else
{
lean_object* v_only_4119_; lean_object* v___x_4120_; 
v_only_4119_ = l_Lean_Syntax_getArg(v___x_4115_, v___x_3877_);
lean_dec(v___x_4115_);
v___x_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4120_, 0, v_only_4119_);
v___y_4066_ = v_unfold_4096_;
v___y_4067_ = v___x_4106_;
v___y_4068_ = v___y_4095_;
v___y_4069_ = v___x_4114_;
v___y_4070_ = v___x_4105_;
v___y_4071_ = v___x_4110_;
v_only_4072_ = v___x_4120_;
v___y_4073_ = v___y_4097_;
v___y_4074_ = v___y_4098_;
v___y_4075_ = v___y_4099_;
v___y_4076_ = v___y_4100_;
v___y_4077_ = v___y_4101_;
v___y_4078_ = v___y_4102_;
v___y_4079_ = v___y_4103_;
v___y_4080_ = v___y_4104_;
goto v___jp_4065_;
}
}
else
{
lean_object* v___x_4121_; 
lean_dec(v___x_4115_);
v___x_4121_ = lean_box(0);
v___y_4066_ = v_unfold_4096_;
v___y_4067_ = v___x_4106_;
v___y_4068_ = v___y_4095_;
v___y_4069_ = v___x_4114_;
v___y_4070_ = v___x_4105_;
v___y_4071_ = v___x_4110_;
v_only_4072_ = v___x_4121_;
v___y_4073_ = v___y_4097_;
v___y_4074_ = v___y_4098_;
v___y_4075_ = v___y_4099_;
v___y_4076_ = v___y_4100_;
v___y_4077_ = v___y_4101_;
v___y_4078_ = v___y_4102_;
v___y_4079_ = v___y_4103_;
v___y_4080_ = v___y_4104_;
goto v___jp_4065_;
}
}
}
}
v___jp_4122_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4132_ = lean_unsigned_to_nat(2u);
v___x_4133_ = l_Lean_Syntax_getArg(v_stx_3833_, v___x_4132_);
v___x_4134_ = l_Lean_Syntax_isNone(v___x_4133_);
if (v___x_4134_ == 0)
{
uint8_t v___x_4135_; 
lean_inc(v___x_4133_);
v___x_4135_ = l_Lean_Syntax_matchesNull(v___x_4133_, v___x_4064_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; 
lean_dec(v___x_4133_);
lean_dec(v_squeeze_4123_);
lean_dec(v_tk_4004_);
lean_dec(v_stx_3833_);
v___x_4136_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4136_;
}
else
{
lean_object* v_unfold_4137_; lean_object* v___x_4138_; 
v_unfold_4137_ = l_Lean_Syntax_getArg(v___x_4133_, v___x_3877_);
lean_dec(v___x_4133_);
v___x_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4138_, 0, v_unfold_4137_);
v___y_4094_ = v___x_4132_;
v___y_4095_ = v_squeeze_4123_;
v_unfold_4096_ = v___x_4138_;
v___y_4097_ = v___y_4124_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
goto v___jp_4093_;
}
}
else
{
lean_object* v___x_4139_; 
lean_dec(v___x_4133_);
v___x_4139_ = lean_box(0);
v___y_4094_ = v___x_4132_;
v___y_4095_ = v_squeeze_4123_;
v_unfold_4096_ = v___x_4139_;
v___y_4097_ = v___y_4124_;
v___y_4098_ = v___y_4125_;
v___y_4099_ = v___y_4126_;
v___y_4100_ = v___y_4127_;
v___y_4101_ = v___y_4128_;
v___y_4102_ = v___y_4129_;
v___y_4103_ = v___y_4130_;
v___y_4104_ = v___y_4131_;
goto v___jp_4093_;
}
}
}
v___jp_3843_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_inc_ref(v___y_3846_);
v___x_3866_ = l_Array_append___redArg(v___y_3846_, v___y_3865_);
lean_dec_ref(v___y_3865_);
lean_inc_n(v___y_3845_, 2);
lean_inc_n(v___y_3854_, 4);
v___x_3867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3867_, 0, v___y_3854_);
lean_ctor_set(v___x_3867_, 1, v___y_3845_);
lean_ctor_set(v___x_3867_, 2, v___x_3866_);
v___x_3868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___y_3854_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = l_Lean_Syntax_node2(v___y_3854_, v___y_3845_, v___x_3869_, v___y_3855_);
lean_inc(v___y_3859_);
v___x_3871_ = l_Lean_Syntax_node5(v___y_3854_, v___y_3859_, v___y_3864_, v___y_3851_, v___y_3857_, v___x_3867_, v___x_3870_);
lean_inc(v___y_3853_);
v___x_3872_ = l_Lean_Syntax_node4(v___y_3854_, v___y_3853_, v___y_3861_, v___y_3850_, v___y_3849_, v___x_3871_);
v___x_3873_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3852_, v___x_3872_, v___y_3863_, v___y_3862_, v___y_3848_, v___y_3847_, v___y_3844_, v___y_3860_, v___y_3856_, v___y_3858_);
return v___x_3873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4166_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4169_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4170_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4166_, v___x_4167_, v___x_4168_, v___x_4169_);
return v___x_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4172_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_linter_unnecessarySimpa = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_linter_unnecessarySimpa);
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
