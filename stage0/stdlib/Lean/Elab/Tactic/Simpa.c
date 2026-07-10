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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 186, 141, 63, 66, 208, 56, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value),LEAN_SCALAR_PTR_LITERAL(158, 198, 190, 154, 66, 126, 242, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpaArgsRest"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 133, 181, 17, 86, 74, 251, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value),LEAN_SCALAR_PTR_LITERAL(207, 241, 251, 37, 131, 174, 231, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value),LEAN_SCALAR_PTR_LITERAL(8, 141, 117, 125, 176, 67, 228, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "evalSimpaUsingBang"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
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
v___x_212_ = lean_st_ref_set(v___y_183_, v___x_211_);
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
lean_object* v___f_253_; lean_object* v___x_81824__overap_254_; lean_object* v___x_255_; 
v___f_253_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0));
v___x_81824__overap_254_ = lean_panic_fn_borrowed(v___f_253_, v_msg_243_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_255_ = lean_apply_9(v___x_81824__overap_254_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, lean_box(0));
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
static uint64_t _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4(void){
_start:
{
uint8_t v___x_351_; uint64_t v___x_352_; 
v___x_351_ = 2;
v___x_352_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_353_, lean_object* v_a_354_, uint8_t v___x_355_, uint8_t v___x_356_, lean_object* v_a_357_, lean_object* v_mvarCounter_358_, lean_object* v___x_359_, lean_object* v___x_360_, uint8_t v_useReducible_361_, uint8_t v___x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
lean_inc(v_a_353_);
v___x_372_ = l_Lean_MVarId_getType(v_a_353_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_n(v_a_373_, 2);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = l_Lean_mkIdent(v_a_354_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v_a_373_);
v___x_376_ = l_Lean_Elab_Term_elabTerm(v___x_374_, v___x_375_, v___x_355_, v___x_355_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___x_411_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v___x_411_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_356_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_581_; 
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v___x_411_, 0);
lean_dec(v_unused_582_);
v___x_413_ = v___x_411_;
v_isShared_414_ = v_isSharedCheck_581_;
goto v_resetjp_412_;
}
else
{
lean_dec(v___x_411_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_581_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; 
lean_inc(v___y_370_);
lean_inc_ref(v___y_369_);
lean_inc(v___y_368_);
lean_inc_ref(v___y_367_);
lean_inc(v_a_377_);
v___x_415_ = lean_infer_type(v_a_377_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; uint8_t v_____do__lift_418_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v___x_415_, 1);
if (v_useReducible_361_ == 0)
{
lean_object* v___x_436_; uint8_t v_foApprox_437_; uint8_t v_ctxApprox_438_; uint8_t v_quasiPatternApprox_439_; uint8_t v_constApprox_440_; uint8_t v_isDefEqStuckEx_441_; uint8_t v_unificationHints_442_; uint8_t v_proofIrrelevance_443_; uint8_t v_offsetCnstrs_444_; uint8_t v_transparency_445_; uint8_t v_etaStruct_446_; uint8_t v_univApprox_447_; uint8_t v_iota_448_; uint8_t v_beta_449_; uint8_t v_proj_450_; uint8_t v_zeta_451_; uint8_t v_zetaDelta_452_; uint8_t v_zetaUnused_453_; uint8_t v_zetaHave_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_485_; 
v___x_436_ = l_Lean_Meta_Context_config(v___y_367_);
v_foApprox_437_ = lean_ctor_get_uint8(v___x_436_, 0);
v_ctxApprox_438_ = lean_ctor_get_uint8(v___x_436_, 1);
v_quasiPatternApprox_439_ = lean_ctor_get_uint8(v___x_436_, 2);
v_constApprox_440_ = lean_ctor_get_uint8(v___x_436_, 3);
v_isDefEqStuckEx_441_ = lean_ctor_get_uint8(v___x_436_, 4);
v_unificationHints_442_ = lean_ctor_get_uint8(v___x_436_, 5);
v_proofIrrelevance_443_ = lean_ctor_get_uint8(v___x_436_, 6);
v_offsetCnstrs_444_ = lean_ctor_get_uint8(v___x_436_, 8);
v_transparency_445_ = lean_ctor_get_uint8(v___x_436_, 9);
v_etaStruct_446_ = lean_ctor_get_uint8(v___x_436_, 10);
v_univApprox_447_ = lean_ctor_get_uint8(v___x_436_, 11);
v_iota_448_ = lean_ctor_get_uint8(v___x_436_, 12);
v_beta_449_ = lean_ctor_get_uint8(v___x_436_, 13);
v_proj_450_ = lean_ctor_get_uint8(v___x_436_, 14);
v_zeta_451_ = lean_ctor_get_uint8(v___x_436_, 15);
v_zetaDelta_452_ = lean_ctor_get_uint8(v___x_436_, 16);
v_zetaUnused_453_ = lean_ctor_get_uint8(v___x_436_, 17);
v_zetaHave_454_ = lean_ctor_get_uint8(v___x_436_, 18);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_485_ == 0)
{
v___x_456_ = v___x_436_;
v_isShared_457_ = v_isSharedCheck_485_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_436_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_485_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint8_t v_trackZetaDelta_458_; lean_object* v_zetaDeltaSet_459_; lean_object* v_lctx_460_; lean_object* v_localInstances_461_; lean_object* v_defEqCtx_x3f_462_; lean_object* v_synthPendingDepth_463_; lean_object* v_canUnfold_x3f_464_; uint8_t v_univApprox_465_; uint8_t v_inTypeClassResolution_466_; uint8_t v_cacheInferType_467_; lean_object* v___x_469_; 
v_trackZetaDelta_458_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7);
v_zetaDeltaSet_459_ = lean_ctor_get(v___y_367_, 1);
v_lctx_460_ = lean_ctor_get(v___y_367_, 2);
v_localInstances_461_ = lean_ctor_get(v___y_367_, 3);
v_defEqCtx_x3f_462_ = lean_ctor_get(v___y_367_, 4);
v_synthPendingDepth_463_ = lean_ctor_get(v___y_367_, 5);
v_canUnfold_x3f_464_ = lean_ctor_get(v___y_367_, 6);
v_univApprox_465_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_466_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7 + 2);
v_cacheInferType_467_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7 + 3);
if (v_isShared_457_ == 0)
{
v___x_469_ = v___x_456_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 0, v_foApprox_437_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 1, v_ctxApprox_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 2, v_quasiPatternApprox_439_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 3, v_constApprox_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 4, v_isDefEqStuckEx_441_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 5, v_unificationHints_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 6, v_proofIrrelevance_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 8, v_offsetCnstrs_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 9, v_transparency_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 10, v_etaStruct_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 11, v_univApprox_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 12, v_iota_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 13, v_beta_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 14, v_proj_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 15, v_zeta_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 16, v_zetaDelta_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 17, v_zetaUnused_453_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, 18, v_zetaHave_454_);
v___x_469_ = v_reuseFailAlloc_484_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
uint64_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_ctor_set_uint8(v___x_469_, 7, v___x_362_);
v___x_470_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set_uint64(v___x_471_, sizeof(void*)*1, v___x_470_);
lean_inc(v_canUnfold_x3f_464_);
lean_inc(v_synthPendingDepth_463_);
lean_inc(v_defEqCtx_x3f_462_);
lean_inc_ref(v_localInstances_461_);
lean_inc_ref(v_lctx_460_);
lean_inc(v_zetaDeltaSet_459_);
v___x_472_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_zetaDeltaSet_459_);
lean_ctor_set(v___x_472_, 2, v_lctx_460_);
lean_ctor_set(v___x_472_, 3, v_localInstances_461_);
lean_ctor_set(v___x_472_, 4, v_defEqCtx_x3f_462_);
lean_ctor_set(v___x_472_, 5, v_synthPendingDepth_463_);
lean_ctor_set(v___x_472_, 6, v_canUnfold_x3f_464_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*7, v_trackZetaDelta_458_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*7 + 1, v_univApprox_465_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*7 + 2, v_inTypeClassResolution_466_);
lean_ctor_set_uint8(v___x_472_, sizeof(void*)*7 + 3, v_cacheInferType_467_);
lean_inc(v_a_416_);
lean_inc(v_a_373_);
v___x_473_ = l_Lean_Meta_isExprDefEq(v_a_373_, v_a_416_, v___x_472_, v___y_368_, v___y_369_, v___y_370_);
lean_dec_ref_known(v___x_472_, 7);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; uint8_t v___x_475_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
v___x_475_ = lean_unbox(v_a_474_);
lean_dec(v_a_474_);
v_____do__lift_418_ = v___x_475_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
v___y_421_ = v___y_365_;
v___y_422_ = v___y_366_;
v___y_423_ = v___y_367_;
v___y_424_ = v___y_368_;
v___y_425_ = v___y_369_;
v___y_426_ = v___y_370_;
goto v___jp_417_;
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_a_416_);
lean_del_object(v___x_413_);
lean_dec(v_a_377_);
lean_dec(v_a_373_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_353_);
v_a_476_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_473_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_473_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
else
{
lean_object* v___x_486_; uint8_t v_foApprox_487_; uint8_t v_ctxApprox_488_; uint8_t v_quasiPatternApprox_489_; uint8_t v_constApprox_490_; uint8_t v_isDefEqStuckEx_491_; uint8_t v_unificationHints_492_; uint8_t v_proofIrrelevance_493_; uint8_t v_assignSyntheticOpaque_494_; uint8_t v_offsetCnstrs_495_; uint8_t v_etaStruct_496_; uint8_t v_univApprox_497_; uint8_t v_iota_498_; uint8_t v_beta_499_; uint8_t v_proj_500_; uint8_t v_zeta_501_; uint8_t v_zetaDelta_502_; uint8_t v_zetaUnused_503_; uint8_t v_zetaHave_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_572_; 
v___x_486_ = l_Lean_Meta_Context_config(v___y_367_);
v_foApprox_487_ = lean_ctor_get_uint8(v___x_486_, 0);
v_ctxApprox_488_ = lean_ctor_get_uint8(v___x_486_, 1);
v_quasiPatternApprox_489_ = lean_ctor_get_uint8(v___x_486_, 2);
v_constApprox_490_ = lean_ctor_get_uint8(v___x_486_, 3);
v_isDefEqStuckEx_491_ = lean_ctor_get_uint8(v___x_486_, 4);
v_unificationHints_492_ = lean_ctor_get_uint8(v___x_486_, 5);
v_proofIrrelevance_493_ = lean_ctor_get_uint8(v___x_486_, 6);
v_assignSyntheticOpaque_494_ = lean_ctor_get_uint8(v___x_486_, 7);
v_offsetCnstrs_495_ = lean_ctor_get_uint8(v___x_486_, 8);
v_etaStruct_496_ = lean_ctor_get_uint8(v___x_486_, 10);
v_univApprox_497_ = lean_ctor_get_uint8(v___x_486_, 11);
v_iota_498_ = lean_ctor_get_uint8(v___x_486_, 12);
v_beta_499_ = lean_ctor_get_uint8(v___x_486_, 13);
v_proj_500_ = lean_ctor_get_uint8(v___x_486_, 14);
v_zeta_501_ = lean_ctor_get_uint8(v___x_486_, 15);
v_zetaDelta_502_ = lean_ctor_get_uint8(v___x_486_, 16);
v_zetaUnused_503_ = lean_ctor_get_uint8(v___x_486_, 17);
v_zetaHave_504_ = lean_ctor_get_uint8(v___x_486_, 18);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_572_ == 0)
{
v___x_506_ = v___x_486_;
v_isShared_507_ = v_isSharedCheck_572_;
goto v_resetjp_505_;
}
else
{
lean_dec(v___x_486_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_572_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v_trackZetaDelta_508_; lean_object* v_zetaDeltaSet_509_; lean_object* v_lctx_510_; lean_object* v_localInstances_511_; lean_object* v_defEqCtx_x3f_512_; lean_object* v_synthPendingDepth_513_; lean_object* v_canUnfold_x3f_514_; uint8_t v_univApprox_515_; uint8_t v_inTypeClassResolution_516_; uint8_t v_cacheInferType_517_; uint8_t v___x_518_; lean_object* v_config_520_; 
v_trackZetaDelta_508_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7);
v_zetaDeltaSet_509_ = lean_ctor_get(v___y_367_, 1);
v_lctx_510_ = lean_ctor_get(v___y_367_, 2);
v_localInstances_511_ = lean_ctor_get(v___y_367_, 3);
v_defEqCtx_x3f_512_ = lean_ctor_get(v___y_367_, 4);
v_synthPendingDepth_513_ = lean_ctor_get(v___y_367_, 5);
v_canUnfold_x3f_514_ = lean_ctor_get(v___y_367_, 6);
v_univApprox_515_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_516_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7 + 2);
v_cacheInferType_517_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*7 + 3);
v___x_518_ = 2;
if (v_isShared_507_ == 0)
{
v_config_520_ = v___x_506_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 0, v_foApprox_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 1, v_ctxApprox_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 2, v_quasiPatternApprox_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 3, v_constApprox_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 4, v_isDefEqStuckEx_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 5, v_unificationHints_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 6, v_proofIrrelevance_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 7, v_assignSyntheticOpaque_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 8, v_offsetCnstrs_495_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 10, v_etaStruct_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 11, v_univApprox_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 12, v_iota_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 13, v_beta_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 14, v_proj_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 15, v_zeta_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 16, v_zetaDelta_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 17, v_zetaUnused_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, 18, v_zetaHave_504_);
v_config_520_ = v_reuseFailAlloc_571_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
uint64_t v___x_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v_key_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v_foApprox_530_; uint8_t v_ctxApprox_531_; uint8_t v_quasiPatternApprox_532_; uint8_t v_constApprox_533_; uint8_t v_isDefEqStuckEx_534_; uint8_t v_unificationHints_535_; uint8_t v_proofIrrelevance_536_; uint8_t v_offsetCnstrs_537_; uint8_t v_transparency_538_; uint8_t v_etaStruct_539_; uint8_t v_univApprox_540_; uint8_t v_iota_541_; uint8_t v_beta_542_; uint8_t v_proj_543_; uint8_t v_zeta_544_; uint8_t v_zetaDelta_545_; uint8_t v_zetaUnused_546_; uint8_t v_zetaHave_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_570_; 
lean_ctor_set_uint8(v_config_520_, 9, v___x_518_);
v___x_521_ = l_Lean_Meta_Context_configKey(v___y_367_);
v___x_522_ = 3ULL;
v___x_523_ = lean_uint64_shift_right(v___x_521_, v___x_522_);
v___x_524_ = lean_uint64_shift_left(v___x_523_, v___x_522_);
v___x_525_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4);
v_key_526_ = lean_uint64_lor(v___x_524_, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_527_, 0, v_config_520_);
lean_ctor_set_uint64(v___x_527_, sizeof(void*)*1, v_key_526_);
lean_inc(v_canUnfold_x3f_514_);
lean_inc(v_synthPendingDepth_513_);
lean_inc(v_defEqCtx_x3f_512_);
lean_inc_ref(v_localInstances_511_);
lean_inc_ref(v_lctx_510_);
lean_inc(v_zetaDeltaSet_509_);
v___x_528_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_zetaDeltaSet_509_);
lean_ctor_set(v___x_528_, 2, v_lctx_510_);
lean_ctor_set(v___x_528_, 3, v_localInstances_511_);
lean_ctor_set(v___x_528_, 4, v_defEqCtx_x3f_512_);
lean_ctor_set(v___x_528_, 5, v_synthPendingDepth_513_);
lean_ctor_set(v___x_528_, 6, v_canUnfold_x3f_514_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*7, v_trackZetaDelta_508_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*7 + 1, v_univApprox_515_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*7 + 2, v_inTypeClassResolution_516_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*7 + 3, v_cacheInferType_517_);
v___x_529_ = l_Lean_Meta_Context_config(v___x_528_);
lean_dec_ref_known(v___x_528_, 7);
v_foApprox_530_ = lean_ctor_get_uint8(v___x_529_, 0);
v_ctxApprox_531_ = lean_ctor_get_uint8(v___x_529_, 1);
v_quasiPatternApprox_532_ = lean_ctor_get_uint8(v___x_529_, 2);
v_constApprox_533_ = lean_ctor_get_uint8(v___x_529_, 3);
v_isDefEqStuckEx_534_ = lean_ctor_get_uint8(v___x_529_, 4);
v_unificationHints_535_ = lean_ctor_get_uint8(v___x_529_, 5);
v_proofIrrelevance_536_ = lean_ctor_get_uint8(v___x_529_, 6);
v_offsetCnstrs_537_ = lean_ctor_get_uint8(v___x_529_, 8);
v_transparency_538_ = lean_ctor_get_uint8(v___x_529_, 9);
v_etaStruct_539_ = lean_ctor_get_uint8(v___x_529_, 10);
v_univApprox_540_ = lean_ctor_get_uint8(v___x_529_, 11);
v_iota_541_ = lean_ctor_get_uint8(v___x_529_, 12);
v_beta_542_ = lean_ctor_get_uint8(v___x_529_, 13);
v_proj_543_ = lean_ctor_get_uint8(v___x_529_, 14);
v_zeta_544_ = lean_ctor_get_uint8(v___x_529_, 15);
v_zetaDelta_545_ = lean_ctor_get_uint8(v___x_529_, 16);
v_zetaUnused_546_ = lean_ctor_get_uint8(v___x_529_, 17);
v_zetaHave_547_ = lean_ctor_get_uint8(v___x_529_, 18);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_570_ == 0)
{
v___x_549_ = v___x_529_;
v_isShared_550_ = v_isSharedCheck_570_;
goto v_resetjp_548_;
}
else
{
lean_dec(v___x_529_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_570_;
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
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 0, v_foApprox_530_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 1, v_ctxApprox_531_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 2, v_quasiPatternApprox_532_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 3, v_constApprox_533_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 4, v_isDefEqStuckEx_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 5, v_unificationHints_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 6, v_proofIrrelevance_536_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 8, v_offsetCnstrs_537_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 9, v_transparency_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 10, v_etaStruct_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 11, v_univApprox_540_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 12, v_iota_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 13, v_beta_542_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 14, v_proj_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 15, v_zeta_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 16, v_zetaDelta_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 17, v_zetaUnused_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, 18, v_zetaHave_547_);
v___x_552_ = v_reuseFailAlloc_569_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
uint64_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_ctor_set_uint8(v___x_552_, 7, v___x_362_);
v___x_553_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set_uint64(v___x_554_, sizeof(void*)*1, v___x_553_);
lean_inc(v_canUnfold_x3f_514_);
lean_inc(v_synthPendingDepth_513_);
lean_inc(v_defEqCtx_x3f_512_);
lean_inc_ref(v_localInstances_511_);
lean_inc_ref(v_lctx_510_);
lean_inc(v_zetaDeltaSet_509_);
v___x_555_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_zetaDeltaSet_509_);
lean_ctor_set(v___x_555_, 2, v_lctx_510_);
lean_ctor_set(v___x_555_, 3, v_localInstances_511_);
lean_ctor_set(v___x_555_, 4, v_defEqCtx_x3f_512_);
lean_ctor_set(v___x_555_, 5, v_synthPendingDepth_513_);
lean_ctor_set(v___x_555_, 6, v_canUnfold_x3f_514_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*7, v_trackZetaDelta_508_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*7 + 1, v_univApprox_515_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*7 + 2, v_inTypeClassResolution_516_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*7 + 3, v_cacheInferType_517_);
lean_inc(v_a_416_);
lean_inc(v_a_373_);
v___x_556_ = l_Lean_Meta_isExprDefEq(v_a_373_, v_a_416_, v___x_555_, v___y_368_, v___y_369_, v___y_370_);
lean_dec_ref_known(v___x_555_, 7);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; uint8_t v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = lean_unbox(v_a_557_);
lean_dec(v_a_557_);
v_____do__lift_418_ = v___x_558_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
v___y_421_ = v___y_365_;
v___y_422_ = v___y_366_;
v___y_423_ = v___y_367_;
v___y_424_ = v___y_368_;
v___y_425_ = v___y_369_;
v___y_426_ = v___y_370_;
goto v___jp_417_;
}
else
{
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_559_; uint8_t v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_556_, 1);
v___x_560_ = lean_unbox(v_a_559_);
lean_dec(v_a_559_);
v_____do__lift_418_ = v___x_560_;
v___y_419_ = v___y_363_;
v___y_420_ = v___y_364_;
v___y_421_ = v___y_365_;
v___y_422_ = v___y_366_;
v___y_423_ = v___y_367_;
v___y_424_ = v___y_368_;
v___y_425_ = v___y_369_;
v___y_426_ = v___y_370_;
goto v___jp_417_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_a_416_);
lean_del_object(v___x_413_);
lean_dec(v_a_377_);
lean_dec(v_a_373_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_353_);
v_a_561_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_556_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_556_);
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
}
}
}
}
}
v___jp_417_:
{
if (v_____do__lift_418_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_427_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1);
lean_inc_ref(v_a_357_);
v___x_428_ = l_Lean_indentExpr(v_a_357_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 1);
lean_ctor_set(v___x_413_, 0, v___x_431_);
v___x_433_ = v___x_413_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
lean_inc(v_a_377_);
v___x_434_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_433_, v_a_373_, v_a_416_, v_a_377_, v___x_360_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec_ref(v___x_433_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_dec_ref_known(v___x_434_, 1);
v___y_379_ = v___y_419_;
v___y_380_ = v___y_420_;
v___y_381_ = v___y_421_;
v___y_382_ = v___y_422_;
v___y_383_ = v___y_423_;
v___y_384_ = v___y_424_;
v___y_385_ = v___y_425_;
v___y_386_ = v___y_426_;
goto v___jp_378_;
}
else
{
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v_a_377_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_353_);
return v___x_434_;
}
}
}
else
{
lean_dec(v_a_416_);
lean_del_object(v___x_413_);
lean_dec(v_a_373_);
lean_dec(v___x_360_);
v___y_379_ = v___y_419_;
v___y_380_ = v___y_420_;
v___y_381_ = v___y_421_;
v___y_382_ = v___y_422_;
v___y_383_ = v___y_423_;
v___y_384_ = v___y_424_;
v___y_385_ = v___y_425_;
v___y_386_ = v___y_426_;
goto v___jp_378_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_del_object(v___x_413_);
lean_dec(v_a_377_);
lean_dec(v_a_373_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_353_);
v_a_573_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_415_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_415_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
else
{
lean_dec(v_a_377_);
lean_dec(v_a_373_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_353_);
return v___x_411_;
}
v___jp_378_:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_getMVars(v_a_357_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_388_, v_mvarCounter_358_, v___y_384_);
lean_dec(v_a_388_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_391_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_390_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v_a_390_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v___x_392_; 
lean_dec_ref_known(v___x_391_, 1);
v___x_392_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_353_, v___y_380_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref_known(v___x_392_, 1);
v___x_393_ = l_Lean_Name_mkStr1(v___x_359_);
v___x_394_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_393_, v_a_377_, v___x_356_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v___x_394_;
}
else
{
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v_a_377_);
lean_dec_ref(v___x_359_);
return v___x_392_;
}
}
else
{
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v_a_377_);
lean_dec_ref(v___x_359_);
lean_dec(v_a_353_);
return v___x_391_;
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v_a_377_);
lean_dec_ref(v___x_359_);
lean_dec(v_a_353_);
v_a_395_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_389_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_389_);
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
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v_a_377_);
lean_dec_ref(v___x_359_);
lean_dec(v_a_353_);
v_a_403_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_387_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_387_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_a_373_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_353_);
v_a_583_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_376_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_376_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___x_360_);
lean_dec_ref(v___x_359_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_354_);
lean_dec(v_a_353_);
v_a_591_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_372_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_372_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object** _args){
lean_object* v_a_599_ = _args[0];
lean_object* v_a_600_ = _args[1];
lean_object* v___x_601_ = _args[2];
lean_object* v___x_602_ = _args[3];
lean_object* v_a_603_ = _args[4];
lean_object* v_mvarCounter_604_ = _args[5];
lean_object* v___x_605_ = _args[6];
lean_object* v___x_606_ = _args[7];
lean_object* v_useReducible_607_ = _args[8];
lean_object* v___x_608_ = _args[9];
lean_object* v___y_609_ = _args[10];
lean_object* v___y_610_ = _args[11];
lean_object* v___y_611_ = _args[12];
lean_object* v___y_612_ = _args[13];
lean_object* v___y_613_ = _args[14];
lean_object* v___y_614_ = _args[15];
lean_object* v___y_615_ = _args[16];
lean_object* v___y_616_ = _args[17];
lean_object* v___y_617_ = _args[18];
_start:
{
uint8_t v___x_94441__boxed_618_; uint8_t v___x_94442__boxed_619_; uint8_t v_useReducible_boxed_620_; uint8_t v___x_94446__boxed_621_; lean_object* v_res_622_; 
v___x_94441__boxed_618_ = lean_unbox(v___x_601_);
v___x_94442__boxed_619_ = lean_unbox(v___x_602_);
v_useReducible_boxed_620_ = lean_unbox(v_useReducible_607_);
v___x_94446__boxed_621_ = lean_unbox(v___x_608_);
v_res_622_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_599_, v_a_600_, v___x_94441__boxed_618_, v___x_94442__boxed_619_, v_a_603_, v_mvarCounter_604_, v___x_605_, v___x_606_, v_useReducible_boxed_620_, v___x_94446__boxed_621_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v_mvarCounter_604_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_infoState_634_; lean_object* v_env_635_; lean_object* v_nextMacroScope_636_; lean_object* v_ngen_637_; lean_object* v_auxDeclNGen_638_; lean_object* v_traceState_639_; lean_object* v_cache_640_; lean_object* v_messages_641_; lean_object* v_snapshotTasks_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_663_; 
v___x_633_ = lean_st_ref_take(v___y_631_);
v_infoState_634_ = lean_ctor_get(v___x_633_, 7);
v_env_635_ = lean_ctor_get(v___x_633_, 0);
v_nextMacroScope_636_ = lean_ctor_get(v___x_633_, 1);
v_ngen_637_ = lean_ctor_get(v___x_633_, 2);
v_auxDeclNGen_638_ = lean_ctor_get(v___x_633_, 3);
v_traceState_639_ = lean_ctor_get(v___x_633_, 4);
v_cache_640_ = lean_ctor_get(v___x_633_, 5);
v_messages_641_ = lean_ctor_get(v___x_633_, 6);
v_snapshotTasks_642_ = lean_ctor_get(v___x_633_, 8);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_663_ == 0)
{
v___x_644_ = v___x_633_;
v_isShared_645_ = v_isSharedCheck_663_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_snapshotTasks_642_);
lean_inc(v_infoState_634_);
lean_inc(v_messages_641_);
lean_inc(v_cache_640_);
lean_inc(v_traceState_639_);
lean_inc(v_auxDeclNGen_638_);
lean_inc(v_ngen_637_);
lean_inc(v_nextMacroScope_636_);
lean_inc(v_env_635_);
lean_dec(v___x_633_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_663_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v_enabled_646_; lean_object* v_assignment_647_; lean_object* v_lazyAssignment_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_661_; 
v_enabled_646_ = lean_ctor_get_uint8(v_infoState_634_, sizeof(void*)*3);
v_assignment_647_ = lean_ctor_get(v_infoState_634_, 0);
v_lazyAssignment_648_ = lean_ctor_get(v_infoState_634_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_infoState_634_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_infoState_634_, 2);
lean_dec(v_unused_662_);
v___x_650_ = v_infoState_634_;
v_isShared_651_ = v_isSharedCheck_661_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_lazyAssignment_648_);
lean_inc(v_assignment_647_);
lean_dec(v_infoState_634_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_661_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 2, v_a_623_);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_assignment_647_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_lazyAssignment_648_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_a_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_660_, sizeof(void*)*3, v_enabled_646_);
v___x_653_ = v_reuseFailAlloc_660_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 7, v___x_653_);
v___x_655_ = v___x_644_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_env_635_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_nextMacroScope_636_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_ngen_637_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_auxDeclNGen_638_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_traceState_639_);
lean_ctor_set(v_reuseFailAlloc_659_, 5, v_cache_640_);
lean_ctor_set(v_reuseFailAlloc_659_, 6, v_messages_641_);
lean_ctor_set(v_reuseFailAlloc_659_, 7, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_659_, 8, v_snapshotTasks_642_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_st_ref_set(v___y_631_, v___x_655_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object* v_a_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
return v_x_675_;
}
else
{
lean_object* v_key_677_; lean_object* v_value_678_; lean_object* v_tail_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_702_; 
v_key_677_ = lean_ctor_get(v_x_676_, 0);
v_value_678_ = lean_ctor_get(v_x_676_, 1);
v_tail_679_ = lean_ctor_get(v_x_676_, 2);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_702_ == 0)
{
v___x_681_ = v_x_676_;
v_isShared_682_ = v_isSharedCheck_702_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_tail_679_);
lean_inc(v_value_678_);
lean_inc(v_key_677_);
lean_dec(v_x_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_702_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; uint64_t v_fold_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; size_t v___x_691_; size_t v___x_692_; size_t v___x_693_; size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_683_ = lean_array_get_size(v_x_675_);
v___x_684_ = l_Lean_Expr_hash(v_key_677_);
v___x_685_ = 32ULL;
v___x_686_ = lean_uint64_shift_right(v___x_684_, v___x_685_);
v_fold_687_ = lean_uint64_xor(v___x_684_, v___x_686_);
v___x_688_ = 16ULL;
v___x_689_ = lean_uint64_shift_right(v_fold_687_, v___x_688_);
v___x_690_ = lean_uint64_xor(v_fold_687_, v___x_689_);
v___x_691_ = lean_uint64_to_usize(v___x_690_);
v___x_692_ = lean_usize_of_nat(v___x_683_);
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_sub(v___x_692_, v___x_693_);
v___x_695_ = lean_usize_land(v___x_691_, v___x_694_);
v___x_696_ = lean_array_uget_borrowed(v_x_675_, v___x_695_);
lean_inc(v___x_696_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v___x_696_);
v___x_698_ = v___x_681_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_key_677_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_value_678_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_696_);
v___x_698_ = v_reuseFailAlloc_701_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_array_uset(v_x_675_, v___x_695_, v___x_698_);
v_x_675_ = v___x_699_;
v_x_676_ = v_tail_679_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object* v_i_703_, lean_object* v_source_704_, lean_object* v_target_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_array_get_size(v_source_704_);
v___x_707_ = lean_nat_dec_lt(v_i_703_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec_ref(v_source_704_);
lean_dec(v_i_703_);
return v_target_705_;
}
else
{
lean_object* v_es_708_; lean_object* v___x_709_; lean_object* v_source_710_; lean_object* v_target_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_es_708_ = lean_array_fget(v_source_704_, v_i_703_);
v___x_709_ = lean_box(0);
v_source_710_ = lean_array_fset(v_source_704_, v_i_703_, v___x_709_);
v_target_711_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_705_, v_es_708_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_i_703_, v___x_712_);
lean_dec(v_i_703_);
v_i_703_ = v___x_713_;
v_source_704_ = v_source_710_;
v_target_705_ = v_target_711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_data_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_nbuckets_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_716_ = lean_array_get_size(v_data_715_);
v___x_717_ = lean_unsigned_to_nat(2u);
v_nbuckets_718_ = lean_nat_mul(v___x_716_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_box(0);
v___x_721_ = lean_mk_array(v_nbuckets_718_, v___x_720_);
v___x_722_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_719_, v_data_715_, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_a_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
uint8_t v___x_725_; 
v___x_725_ = 0;
return v___x_725_;
}
else
{
lean_object* v_key_726_; lean_object* v_tail_727_; uint8_t v___x_728_; 
v_key_726_ = lean_ctor_get(v_x_724_, 0);
v_tail_727_ = lean_ctor_get(v_x_724_, 2);
v___x_728_ = lean_expr_eqv(v_key_726_, v_a_723_);
if (v___x_728_ == 0)
{
v_x_724_ = v_tail_727_;
goto _start;
}
else
{
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_a_730_, lean_object* v_x_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_730_, v_x_731_);
lean_dec(v_x_731_);
lean_dec_ref(v_a_730_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(lean_object* v_m_734_, lean_object* v_a_735_, lean_object* v_b_736_){
_start:
{
lean_object* v_size_737_; lean_object* v_buckets_738_; lean_object* v___x_739_; uint64_t v___x_740_; uint64_t v___x_741_; uint64_t v___x_742_; uint64_t v_fold_743_; uint64_t v___x_744_; uint64_t v___x_745_; uint64_t v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; lean_object* v_bkt_752_; uint8_t v___x_753_; 
v_size_737_ = lean_ctor_get(v_m_734_, 0);
v_buckets_738_ = lean_ctor_get(v_m_734_, 1);
v___x_739_ = lean_array_get_size(v_buckets_738_);
v___x_740_ = l_Lean_Expr_hash(v_a_735_);
v___x_741_ = 32ULL;
v___x_742_ = lean_uint64_shift_right(v___x_740_, v___x_741_);
v_fold_743_ = lean_uint64_xor(v___x_740_, v___x_742_);
v___x_744_ = 16ULL;
v___x_745_ = lean_uint64_shift_right(v_fold_743_, v___x_744_);
v___x_746_ = lean_uint64_xor(v_fold_743_, v___x_745_);
v___x_747_ = lean_uint64_to_usize(v___x_746_);
v___x_748_ = lean_usize_of_nat(v___x_739_);
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_sub(v___x_748_, v___x_749_);
v___x_751_ = lean_usize_land(v___x_747_, v___x_750_);
v_bkt_752_ = lean_array_uget_borrowed(v_buckets_738_, v___x_751_);
v___x_753_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_735_, v_bkt_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_774_; 
lean_inc_ref(v_buckets_738_);
lean_inc(v_size_737_);
v_isSharedCheck_774_ = !lean_is_exclusive(v_m_734_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_775_ = lean_ctor_get(v_m_734_, 1);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_m_734_, 0);
lean_dec(v_unused_776_);
v___x_755_ = v_m_734_;
v_isShared_756_ = v_isSharedCheck_774_;
goto v_resetjp_754_;
}
else
{
lean_dec(v_m_734_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_774_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v_size_x27_758_; lean_object* v___x_759_; lean_object* v_buckets_x27_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_757_ = lean_unsigned_to_nat(1u);
v_size_x27_758_ = lean_nat_add(v_size_737_, v___x_757_);
lean_dec(v_size_737_);
lean_inc(v_bkt_752_);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v_a_735_);
lean_ctor_set(v___x_759_, 1, v_b_736_);
lean_ctor_set(v___x_759_, 2, v_bkt_752_);
v_buckets_x27_760_ = lean_array_uset(v_buckets_738_, v___x_751_, v___x_759_);
v___x_761_ = lean_unsigned_to_nat(4u);
v___x_762_ = lean_nat_mul(v_size_x27_758_, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(3u);
v___x_764_ = lean_nat_div(v___x_762_, v___x_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_array_get_size(v_buckets_x27_760_);
v___x_766_ = lean_nat_dec_le(v___x_764_, v___x_765_);
lean_dec(v___x_764_);
if (v___x_766_ == 0)
{
lean_object* v_val_767_; lean_object* v___x_769_; 
v_val_767_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_760_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_val_767_);
lean_ctor_set(v___x_755_, 0, v_size_x27_758_);
v___x_769_ = v___x_755_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_size_x27_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_val_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
else
{
lean_object* v___x_772_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_buckets_x27_760_);
lean_ctor_set(v___x_755_, 0, v_size_x27_758_);
v___x_772_ = v___x_755_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_size_x27_758_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_buckets_x27_760_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_dec(v_b_736_);
lean_dec_ref(v_a_735_);
return v_m_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(lean_object* v_mvarId_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; lean_object* v_mctx_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_781_ = lean_st_ref_get(v___y_779_);
v_mctx_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc_ref(v_mctx_782_);
lean_dec(v___x_781_);
v___x_783_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_782_, v_mvarId_777_);
lean_dec_ref(v_mctx_782_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___y_778_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object* v_mvarId_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec(v_mvarId_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_mvarId_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v_mctx_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_796_ = lean_st_ref_get(v___y_794_);
v_mctx_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref(v_mctx_797_);
lean_dec(v___x_796_);
v___x_798_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_797_, v_mvarId_792_);
lean_dec_ref(v_mctx_797_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___y_793_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_mvarId_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec(v_mvarId_802_);
return v_res_806_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_buckets_809_; lean_object* v___x_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; uint64_t v_fold_814_; uint64_t v___x_815_; uint64_t v___x_816_; uint64_t v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_buckets_809_ = lean_ctor_get(v_m_807_, 1);
v___x_810_ = lean_array_get_size(v_buckets_809_);
v___x_811_ = l_Lean_Expr_hash(v_a_808_);
v___x_812_ = 32ULL;
v___x_813_ = lean_uint64_shift_right(v___x_811_, v___x_812_);
v_fold_814_ = lean_uint64_xor(v___x_811_, v___x_813_);
v___x_815_ = 16ULL;
v___x_816_ = lean_uint64_shift_right(v_fold_814_, v___x_815_);
v___x_817_ = lean_uint64_xor(v_fold_814_, v___x_816_);
v___x_818_ = lean_uint64_to_usize(v___x_817_);
v___x_819_ = lean_usize_of_nat(v___x_810_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_sub(v___x_819_, v___x_820_);
v___x_822_ = lean_usize_land(v___x_818_, v___x_821_);
v___x_823_ = lean_array_uget_borrowed(v_buckets_809_, v___x_822_);
v___x_824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_808_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_825_, lean_object* v_a_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_825_, v_a_826_);
lean_dec_ref(v_a_826_);
lean_dec_ref(v_m_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_833_, lean_object* v_e_834_, lean_object* v_a_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_d_846_; lean_object* v_b_847_; lean_object* v___y_848_; uint8_t v___x_854_; uint8_t v___x_855_; 
v___x_854_ = l_Lean_Expr_hasExprMVar(v_e_834_);
v___x_855_ = lean_bool_not(v___x_854_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_835_, v_e_834_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_box(0);
lean_inc_ref(v_e_834_);
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_a_835_, v_e_834_, v___x_857_);
switch(lean_obj_tag(v_e_834_))
{
case 11:
{
lean_object* v_struct_859_; 
v_struct_859_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_struct_859_);
lean_dec_ref_known(v_e_834_, 3);
v_e_834_ = v_struct_859_;
v_a_835_ = v___x_858_;
goto _start;
}
case 7:
{
lean_object* v_binderType_861_; lean_object* v_body_862_; 
v_binderType_861_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_binderType_861_);
v_body_862_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_body_862_);
lean_dec_ref_known(v_e_834_, 3);
v_d_846_ = v_binderType_861_;
v_b_847_ = v_body_862_;
v___y_848_ = v___x_858_;
goto v___jp_845_;
}
case 6:
{
lean_object* v_binderType_863_; lean_object* v_body_864_; 
v_binderType_863_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_binderType_863_);
v_body_864_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_body_864_);
lean_dec_ref_known(v_e_834_, 3);
v_d_846_ = v_binderType_863_;
v_b_847_ = v_body_864_;
v___y_848_ = v___x_858_;
goto v___jp_845_;
}
case 8:
{
lean_object* v_type_865_; lean_object* v_value_866_; lean_object* v_body_867_; lean_object* v___x_868_; 
v_type_865_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_type_865_);
v_value_866_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_value_866_);
v_body_867_ = lean_ctor_get(v_e_834_, 3);
lean_inc_ref(v_body_867_);
lean_dec_ref_known(v_e_834_, 4);
v___x_868_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_833_, v_type_865_, v___x_858_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v_fst_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
v_fst_870_ = lean_ctor_get(v_a_869_, 0);
if (lean_obj_tag(v_fst_870_) == 0)
{
lean_dec(v_a_869_);
lean_dec_ref(v_body_867_);
lean_dec_ref(v_value_866_);
return v___x_868_;
}
else
{
lean_object* v_snd_871_; lean_object* v___x_872_; 
lean_dec_ref_known(v___x_868_, 1);
v_snd_871_ = lean_ctor_get(v_a_869_, 1);
lean_inc(v_snd_871_);
lean_dec(v_a_869_);
v___x_872_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_833_, v_value_866_, v_snd_871_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v_fst_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
v_fst_874_ = lean_ctor_get(v_a_873_, 0);
if (lean_obj_tag(v_fst_874_) == 0)
{
lean_dec(v_a_873_);
lean_dec_ref(v_body_867_);
return v___x_872_;
}
else
{
lean_object* v_snd_875_; 
lean_dec_ref_known(v___x_872_, 1);
v_snd_875_ = lean_ctor_get(v_a_873_, 1);
lean_inc(v_snd_875_);
lean_dec(v_a_873_);
v_e_834_ = v_body_867_;
v_a_835_ = v_snd_875_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_867_);
return v___x_872_;
}
}
}
else
{
lean_dec_ref(v_body_867_);
lean_dec_ref(v_value_866_);
return v___x_868_;
}
}
case 10:
{
lean_object* v_expr_877_; 
v_expr_877_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_expr_877_);
lean_dec_ref_known(v_e_834_, 2);
v_e_834_ = v_expr_877_;
v_a_835_ = v___x_858_;
goto _start;
}
case 5:
{
lean_object* v_fn_879_; lean_object* v_arg_880_; lean_object* v___x_881_; 
v_fn_879_ = lean_ctor_get(v_e_834_, 0);
lean_inc_ref(v_fn_879_);
v_arg_880_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_arg_880_);
lean_dec_ref_known(v_e_834_, 2);
v___x_881_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_833_, v_fn_879_, v___x_858_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v_fst_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
v_fst_883_ = lean_ctor_get(v_a_882_, 0);
if (lean_obj_tag(v_fst_883_) == 0)
{
lean_dec(v_a_882_);
lean_dec_ref(v_arg_880_);
return v___x_881_;
}
else
{
lean_object* v_snd_884_; 
lean_dec_ref_known(v___x_881_, 1);
v_snd_884_ = lean_ctor_get(v_a_882_, 1);
lean_inc(v_snd_884_);
lean_dec(v_a_882_);
v_e_834_ = v_arg_880_;
v_a_835_ = v_snd_884_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_880_);
return v___x_881_;
}
}
case 2:
{
lean_object* v_mvarId_886_; lean_object* v___x_887_; 
v_mvarId_886_ = lean_ctor_get(v_e_834_, 0);
lean_inc(v_mvarId_886_);
lean_dec_ref_known(v_e_834_, 1);
v___x_887_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_833_, v_mvarId_886_, v___x_858_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_887_;
}
default: 
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref(v_e_834_);
v___x_888_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_858_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v_e_834_);
v___x_891_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
lean_ctor_set(v___x_892_, 1, v_a_835_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_e_834_);
v___x_894_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v_a_835_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
v___jp_845_:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_833_, v_d_846_, v___y_848_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v_fst_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
v_fst_851_ = lean_ctor_get(v_a_850_, 0);
if (lean_obj_tag(v_fst_851_) == 0)
{
lean_dec(v_a_850_);
lean_dec_ref(v_b_847_);
return v___x_849_;
}
else
{
lean_object* v_snd_852_; 
lean_dec_ref_known(v___x_849_, 1);
v_snd_852_ = lean_ctor_get(v_a_850_, 1);
lean_inc(v_snd_852_);
lean_dec(v_a_850_);
v_e_834_ = v_b_847_;
v_a_835_ = v_snd_852_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_847_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object* v_mvarId_897_, lean_object* v_mvarId_x27_898_, lean_object* v_a_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = l_Lean_instBEqMVarId_beq(v_mvarId_897_, v_mvarId_x27_898_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_898_, v_a_899_, v___y_905_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_994_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_994_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_994_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_994_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_fst_915_; 
v_fst_915_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v_fst_915_);
if (lean_obj_tag(v_fst_915_) == 0)
{
lean_object* v_snd_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_mvarId_x27_898_);
v_snd_916_ = lean_ctor_get(v_a_911_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_911_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_a_911_, 0);
lean_dec(v_unused_935_);
v___x_918_ = v_a_911_;
v_isShared_919_ = v_isSharedCheck_934_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snd_916_);
lean_dec(v_a_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_934_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_933_; 
v_a_920_ = lean_ctor_get(v_fst_915_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_fst_915_);
if (v_isSharedCheck_933_ == 0)
{
v___x_922_ = v_fst_915_;
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v_fst_915_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_932_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_925_);
v___x_927_ = v___x_918_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_snd_916_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_927_);
v___x_929_ = v___x_913_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
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
}
}
else
{
lean_object* v_a_936_; 
lean_del_object(v___x_913_);
v_a_936_ = lean_ctor_get(v_fst_915_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v_fst_915_, 1);
if (lean_obj_tag(v_a_936_) == 0)
{
lean_object* v_snd_937_; lean_object* v___x_938_; 
v_snd_937_ = lean_ctor_get(v_a_911_, 1);
lean_inc(v_snd_937_);
lean_dec(v_a_911_);
v___x_938_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_898_, v_snd_937_, v___y_905_);
lean_dec(v_mvarId_x27_898_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_982_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_982_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_982_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_982_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; 
v_fst_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_fst_943_);
if (lean_obj_tag(v_fst_943_) == 0)
{
lean_object* v_snd_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_962_; 
v_snd_944_ = lean_ctor_get(v_a_939_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_a_939_, 0);
lean_dec(v_unused_963_);
v___x_946_ = v_a_939_;
v_isShared_947_ = v_isSharedCheck_962_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_944_);
lean_dec(v_a_939_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_962_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_961_; 
v_a_948_ = lean_ctor_get(v_fst_943_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_fst_943_);
if (v_isSharedCheck_961_ == 0)
{
v___x_950_ = v_fst_943_;
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v_fst_943_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_960_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_953_);
v___x_955_ = v___x_946_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_snd_944_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_955_);
v___x_957_ = v___x_941_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
else
{
lean_object* v_a_964_; 
v_a_964_ = lean_ctor_get(v_fst_943_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v_fst_943_, 1);
if (lean_obj_tag(v_a_964_) == 0)
{
lean_object* v_snd_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_976_; 
v_snd_965_ = lean_ctor_get(v_a_939_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_a_939_, 0);
lean_dec(v_unused_977_);
v___x_967_ = v_a_939_;
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_snd_965_);
lean_dec(v_a_939_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_976_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_snd_965_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_971_);
v___x_973_ = v___x_941_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v_val_978_; lean_object* v_snd_979_; lean_object* v_mvarIdPending_980_; 
lean_del_object(v___x_941_);
v_val_978_ = lean_ctor_get(v_a_964_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_a_964_, 1);
v_snd_979_ = lean_ctor_get(v_a_939_, 1);
lean_inc(v_snd_979_);
lean_dec(v_a_939_);
v_mvarIdPending_980_ = lean_ctor_get(v_val_978_, 1);
lean_inc(v_mvarIdPending_980_);
lean_dec(v_val_978_);
v_mvarId_x27_898_ = v_mvarIdPending_980_;
v_a_899_ = v_snd_979_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
v_a_983_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_938_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_938_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_snd_991_; lean_object* v_val_992_; lean_object* v___x_993_; 
lean_dec(v_mvarId_x27_898_);
v_snd_991_ = lean_ctor_get(v_a_911_, 1);
lean_inc(v_snd_991_);
lean_dec(v_a_911_);
v_val_992_ = lean_ctor_get(v_a_936_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_a_936_, 1);
v___x_993_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_897_, v_val_992_, v_snd_991_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_mvarId_x27_898_);
v_a_995_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_910_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_910_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_mvarId_x27_898_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1));
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_a_899_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_1006_, lean_object* v_mvarId_x27_1007_, lean_object* v_a_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_1006_, v_mvarId_x27_1007_, v_a_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v_mvarId_1006_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_1019_, lean_object* v_e_1020_, lean_object* v_a_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1019_, v_e_1020_, v_a_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v_mvarId_1019_);
return v_res_1031_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_unsigned_to_nat(16u);
v___x_1034_ = lean_mk_array(v___x_1033_, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1038_, lean_object* v_e_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
uint8_t v___x_1049_; uint8_t v___x_1050_; uint8_t v___x_1051_; 
v___x_1049_ = l_Lean_Expr_hasExprMVar(v_e_1039_);
v___x_1050_ = lean_bool_not(v___x_1049_);
v___x_1051_ = 1;
if (v___x_1050_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1053_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1038_, v_e_1039_, v___x_1052_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1067_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1067_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1067_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_fst_1058_; 
v_fst_1058_ = lean_ctor_get(v_a_1054_, 0);
lean_inc(v_fst_1058_);
lean_dec(v_a_1054_);
if (lean_obj_tag(v_fst_1058_) == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_dec_ref_known(v_fst_1058_, 1);
v___x_1059_ = lean_box(v___x_1050_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_dec_ref_known(v_fst_1058_, 1);
v___x_1063_ = lean_box(v___x_1051_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1063_);
v___x_1065_ = v___x_1056_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_a_1068_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1053_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1053_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec_ref(v_e_1039_);
v___x_1076_ = lean_box(v___x_1051_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1078_, lean_object* v_e_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1078_, v_e_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v_mvarId_1078_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object* v_msgData_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v_env_1097_; lean_object* v___x_1098_; lean_object* v_mctx_1099_; lean_object* v_lctx_1100_; lean_object* v_options_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1096_ = lean_st_ref_get(v___y_1094_);
v_env_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref(v_env_1097_);
lean_dec(v___x_1096_);
v___x_1098_ = lean_st_ref_get(v___y_1092_);
v_mctx_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_ref(v_mctx_1099_);
lean_dec(v___x_1098_);
v_lctx_1100_ = lean_ctor_get(v___y_1091_, 2);
v_options_1101_ = lean_ctor_get(v___y_1093_, 2);
lean_inc_ref(v_options_1101_);
lean_inc_ref(v_lctx_1100_);
v___x_1102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1102_, 0, v_env_1097_);
lean_ctor_set(v___x_1102_, 1, v_mctx_1099_);
lean_ctor_set(v___x_1102_, 2, v_lctx_1100_);
lean_ctor_set(v___x_1102_, 3, v_options_1101_);
v___x_1103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_msgData_1090_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object* v_msgData_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msgData_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v_msg_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_ref_1118_; lean_object* v___x_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_ref_1118_ = lean_ctor_get(v___y_1115_, 5);
v___x_1119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msg_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v_ref_1118_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_ref_1118_);
lean_ctor_set(v___x_1124_, 1, v_a_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v_msg_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v_ks_1140_; lean_object* v_vs_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1165_; 
v_ks_1140_ = lean_ctor_get(v_x_1136_, 0);
v_vs_1141_ = lean_ctor_get(v_x_1136_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1136_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1143_ = v_x_1136_;
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_vs_1141_);
lean_inc(v_ks_1140_);
lean_dec(v_x_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_array_get_size(v_ks_1140_);
v___x_1146_ = lean_nat_dec_lt(v_x_1137_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_dec(v_x_1137_);
v___x_1147_ = lean_array_push(v_ks_1140_, v_x_1138_);
v___x_1148_ = lean_array_push(v_vs_1141_, v_x_1139_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1148_);
lean_ctor_set(v___x_1143_, 0, v___x_1147_);
v___x_1150_ = v___x_1143_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v_k_x27_1152_; uint8_t v___x_1153_; 
v_k_x27_1152_ = lean_array_fget_borrowed(v_ks_1140_, v_x_1137_);
v___x_1153_ = l_Lean_instBEqMVarId_beq(v_x_1138_, v_k_x27_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1155_; 
if (v_isShared_1144_ == 0)
{
v___x_1155_ = v___x_1143_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_ks_1140_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_vs_1141_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_add(v_x_1137_, v___x_1156_);
lean_dec(v_x_1137_);
v_x_1136_ = v___x_1155_;
v_x_1137_ = v___x_1157_;
goto _start;
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1160_ = lean_array_fset(v_ks_1140_, v_x_1137_, v_x_1138_);
v___x_1161_ = lean_array_fset(v_vs_1141_, v_x_1137_, v_x_1139_);
lean_dec(v_x_1137_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1161_);
lean_ctor_set(v___x_1143_, 0, v___x_1160_);
v___x_1163_ = v___x_1143_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1166_, lean_object* v_k_1167_, lean_object* v_v_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1166_, v___x_1169_, v_k_1167_, v_v_1168_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(lean_object* v_x_1172_, size_t v_x_1173_, size_t v_x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v_es_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v_j_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_es_1177_ = lean_ctor_get(v_x_1172_, 0);
v___x_1178_ = ((size_t)31ULL);
v___x_1179_ = lean_usize_land(v_x_1173_, v___x_1178_);
v_j_1180_ = lean_usize_to_nat(v___x_1179_);
v___x_1181_ = lean_array_get_size(v_es_1177_);
v___x_1182_ = lean_nat_dec_lt(v_j_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_dec(v_j_1180_);
lean_dec(v_x_1176_);
lean_dec(v_x_1175_);
return v_x_1172_;
}
else
{
lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1221_; 
lean_inc_ref(v_es_1177_);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_x_1172_, 0);
lean_dec(v_unused_1222_);
v___x_1184_ = v_x_1172_;
v_isShared_1185_ = v_isSharedCheck_1221_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v_x_1172_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1221_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_v_1186_; lean_object* v___x_1187_; lean_object* v_xs_x27_1188_; lean_object* v___y_1190_; 
v_v_1186_ = lean_array_fget(v_es_1177_, v_j_1180_);
v___x_1187_ = lean_box(0);
v_xs_x27_1188_ = lean_array_fset(v_es_1177_, v_j_1180_, v___x_1187_);
switch(lean_obj_tag(v_v_1186_))
{
case 0:
{
lean_object* v_key_1195_; lean_object* v_val_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1206_; 
v_key_1195_ = lean_ctor_get(v_v_1186_, 0);
v_val_1196_ = lean_ctor_get(v_v_1186_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_v_1186_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1198_ = v_v_1186_;
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_val_1196_);
lean_inc(v_key_1195_);
lean_dec(v_v_1186_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_instBEqMVarId_beq(v_x_1175_, v_key_1195_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_del_object(v___x_1198_);
v___x_1201_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1195_, v_val_1196_, v_x_1175_, v_x_1176_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
v___y_1190_ = v___x_1202_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1204_; 
lean_dec(v_val_1196_);
lean_dec(v_key_1195_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v_x_1176_);
lean_ctor_set(v___x_1198_, 0, v_x_1175_);
v___x_1204_ = v___x_1198_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_x_1175_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_x_1176_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
v___y_1190_ = v___x_1204_;
goto v___jp_1189_;
}
}
}
}
case 1:
{
lean_object* v_node_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1219_; 
v_node_1207_ = lean_ctor_get(v_v_1186_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_v_1186_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1209_ = v_v_1186_;
v_isShared_1210_ = v_isSharedCheck_1219_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_node_1207_);
lean_dec(v_v_1186_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1219_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1211_ = ((size_t)5ULL);
v___x_1212_ = lean_usize_shift_right(v_x_1173_, v___x_1211_);
v___x_1213_ = ((size_t)1ULL);
v___x_1214_ = lean_usize_add(v_x_1174_, v___x_1213_);
v___x_1215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_node_1207_, v___x_1212_, v___x_1214_, v_x_1175_, v_x_1176_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1215_);
v___x_1217_ = v___x_1209_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
v___y_1190_ = v___x_1217_;
goto v___jp_1189_;
}
}
}
default: 
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_x_1175_);
lean_ctor_set(v___x_1220_, 1, v_x_1176_);
v___y_1190_ = v___x_1220_;
goto v___jp_1189_;
}
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_array_fset(v_xs_x27_1188_, v_j_1180_, v___y_1190_);
lean_dec(v_j_1180_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1191_);
v___x_1193_ = v___x_1184_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
else
{
lean_object* v_ks_1223_; lean_object* v_vs_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1244_; 
v_ks_1223_ = lean_ctor_get(v_x_1172_, 0);
v_vs_1224_ = lean_ctor_get(v_x_1172_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1226_ = v_x_1172_;
v_isShared_1227_ = v_isSharedCheck_1244_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_vs_1224_);
lean_inc(v_ks_1223_);
lean_dec(v_x_1172_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1244_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_ks_1223_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_vs_1224_);
v___x_1229_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v_newNode_1230_; uint8_t v___y_1232_; size_t v___x_1238_; uint8_t v___x_1239_; 
v_newNode_1230_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1229_, v_x_1175_, v_x_1176_);
v___x_1238_ = ((size_t)7ULL);
v___x_1239_ = lean_usize_dec_le(v___x_1238_, v_x_1174_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1240_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1230_);
v___x_1241_ = lean_unsigned_to_nat(4u);
v___x_1242_ = lean_nat_dec_lt(v___x_1240_, v___x_1241_);
lean_dec(v___x_1240_);
v___y_1232_ = v___x_1242_;
goto v___jp_1231_;
}
else
{
v___y_1232_ = v___x_1239_;
goto v___jp_1231_;
}
v___jp_1231_:
{
if (v___y_1232_ == 0)
{
lean_object* v_ks_1233_; lean_object* v_vs_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_ks_1233_ = lean_ctor_get(v_newNode_1230_, 0);
lean_inc_ref(v_ks_1233_);
v_vs_1234_ = lean_ctor_get(v_newNode_1230_, 1);
lean_inc_ref(v_vs_1234_);
lean_dec_ref(v_newNode_1230_);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1174_, v_ks_1233_, v_vs_1234_, v___x_1235_, v___x_1236_);
lean_dec_ref(v_vs_1234_);
lean_dec_ref(v_ks_1233_);
return v___x_1237_;
}
else
{
return v_newNode_1230_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1245_, lean_object* v_keys_1246_, lean_object* v_vals_1247_, lean_object* v_i_1248_, lean_object* v_entries_1249_){
_start:
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = lean_array_get_size(v_keys_1246_);
v___x_1251_ = lean_nat_dec_lt(v_i_1248_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v_i_1248_);
return v_entries_1249_;
}
else
{
lean_object* v_k_1252_; lean_object* v_v_1253_; uint64_t v___x_1254_; size_t v_h_1255_; size_t v___x_1256_; lean_object* v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; size_t v___x_1260_; size_t v_h_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_k_1252_ = lean_array_fget_borrowed(v_keys_1246_, v_i_1248_);
v_v_1253_ = lean_array_fget_borrowed(v_vals_1247_, v_i_1248_);
v___x_1254_ = l_Lean_instHashableMVarId_hash(v_k_1252_);
v_h_1255_ = lean_uint64_to_usize(v___x_1254_);
v___x_1256_ = ((size_t)5ULL);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_sub(v_depth_1245_, v___x_1258_);
v___x_1260_ = lean_usize_mul(v___x_1256_, v___x_1259_);
v_h_1261_ = lean_usize_shift_right(v_h_1255_, v___x_1260_);
v___x_1262_ = lean_nat_add(v_i_1248_, v___x_1257_);
lean_dec(v_i_1248_);
lean_inc(v_v_1253_);
lean_inc(v_k_1252_);
v___x_1263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_entries_1249_, v_h_1261_, v_depth_1245_, v_k_1252_, v_v_1253_);
v_i_1248_ = v___x_1262_;
v_entries_1249_ = v___x_1263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1265_, lean_object* v_keys_1266_, lean_object* v_vals_1267_, lean_object* v_i_1268_, lean_object* v_entries_1269_){
_start:
{
size_t v_depth_boxed_1270_; lean_object* v_res_1271_; 
v_depth_boxed_1270_ = lean_unbox_usize(v_depth_1265_);
lean_dec(v_depth_1265_);
v_res_1271_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1270_, v_keys_1266_, v_vals_1267_, v_i_1268_, v_entries_1269_);
lean_dec_ref(v_vals_1267_);
lean_dec_ref(v_keys_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
size_t v_x_95745__boxed_1277_; size_t v_x_95746__boxed_1278_; lean_object* v_res_1279_; 
v_x_95745__boxed_1277_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_x_95746__boxed_1278_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_res_1279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1272_, v_x_95745__boxed_1277_, v_x_95746__boxed_1278_, v_x_1275_, v_x_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
uint64_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = l_Lean_instHashableMVarId_hash(v_x_1281_);
v___x_1284_ = lean_uint64_to_usize(v___x_1283_);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1280_, v___x_1284_, v___x_1285_, v_x_1281_, v_x_1282_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_1287_, lean_object* v_val_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v_mctx_1292_; lean_object* v_cache_1293_; lean_object* v_zetaDeltaFVarIds_1294_; lean_object* v_postponed_1295_; lean_object* v_diag_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1324_; 
v___x_1291_ = lean_st_ref_take(v___y_1289_);
v_mctx_1292_ = lean_ctor_get(v___x_1291_, 0);
v_cache_1293_ = lean_ctor_get(v___x_1291_, 1);
v_zetaDeltaFVarIds_1294_ = lean_ctor_get(v___x_1291_, 2);
v_postponed_1295_ = lean_ctor_get(v___x_1291_, 3);
v_diag_1296_ = lean_ctor_get(v___x_1291_, 4);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1298_ = v___x_1291_;
v_isShared_1299_ = v_isSharedCheck_1324_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_diag_1296_);
lean_inc(v_postponed_1295_);
lean_inc(v_zetaDeltaFVarIds_1294_);
lean_inc(v_cache_1293_);
lean_inc(v_mctx_1292_);
lean_dec(v___x_1291_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1324_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_depth_1300_; lean_object* v_levelAssignDepth_1301_; lean_object* v_lmvarCounter_1302_; lean_object* v_mvarCounter_1303_; lean_object* v_lDecls_1304_; lean_object* v_decls_1305_; lean_object* v_userNames_1306_; lean_object* v_lAssignment_1307_; lean_object* v_eAssignment_1308_; lean_object* v_dAssignment_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1323_; 
v_depth_1300_ = lean_ctor_get(v_mctx_1292_, 0);
v_levelAssignDepth_1301_ = lean_ctor_get(v_mctx_1292_, 1);
v_lmvarCounter_1302_ = lean_ctor_get(v_mctx_1292_, 2);
v_mvarCounter_1303_ = lean_ctor_get(v_mctx_1292_, 3);
v_lDecls_1304_ = lean_ctor_get(v_mctx_1292_, 4);
v_decls_1305_ = lean_ctor_get(v_mctx_1292_, 5);
v_userNames_1306_ = lean_ctor_get(v_mctx_1292_, 6);
v_lAssignment_1307_ = lean_ctor_get(v_mctx_1292_, 7);
v_eAssignment_1308_ = lean_ctor_get(v_mctx_1292_, 8);
v_dAssignment_1309_ = lean_ctor_get(v_mctx_1292_, 9);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_mctx_1292_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1311_ = v_mctx_1292_;
v_isShared_1312_ = v_isSharedCheck_1323_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_dAssignment_1309_);
lean_inc(v_eAssignment_1308_);
lean_inc(v_lAssignment_1307_);
lean_inc(v_userNames_1306_);
lean_inc(v_decls_1305_);
lean_inc(v_lDecls_1304_);
lean_inc(v_mvarCounter_1303_);
lean_inc(v_lmvarCounter_1302_);
lean_inc(v_levelAssignDepth_1301_);
lean_inc(v_depth_1300_);
lean_dec(v_mctx_1292_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1323_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_1308_, v_mvarId_1287_, v_val_1288_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 8, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_depth_1300_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_levelAssignDepth_1301_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_lmvarCounter_1302_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_mvarCounter_1303_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_lDecls_1304_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v_decls_1305_);
lean_ctor_set(v_reuseFailAlloc_1322_, 6, v_userNames_1306_);
lean_ctor_set(v_reuseFailAlloc_1322_, 7, v_lAssignment_1307_);
lean_ctor_set(v_reuseFailAlloc_1322_, 8, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1322_, 9, v_dAssignment_1309_);
v___x_1315_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1315_);
v___x_1317_ = v___x_1298_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_cache_1293_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_zetaDeltaFVarIds_1294_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_postponed_1295_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v_diag_1296_);
v___x_1317_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_st_ref_set(v___y_1289_, v___x_1317_);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_1325_, lean_object* v_val_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_1325_, v_val_1326_, v___y_1327_);
lean_dec(v___y_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1338_, uint8_t v_suppressElabErrors_1339_, lean_object* v_x_1340_){
_start:
{
if (lean_obj_tag(v_x_1340_) == 1)
{
lean_object* v_pre_1341_; 
v_pre_1341_ = lean_ctor_get(v_x_1340_, 0);
switch(lean_obj_tag(v_pre_1341_))
{
case 1:
{
lean_object* v_pre_1342_; 
v_pre_1342_ = lean_ctor_get(v_pre_1341_, 0);
switch(lean_obj_tag(v_pre_1342_))
{
case 0:
{
lean_object* v_str_1343_; lean_object* v_str_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_str_1343_ = lean_ctor_get(v_x_1340_, 1);
v_str_1344_ = lean_ctor_get(v_pre_1341_, 1);
v___x_1345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1346_ = lean_string_dec_eq(v_str_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1348_ = lean_string_dec_eq(v_str_1344_, v___x_1347_);
if (v___x_1348_ == 0)
{
return v___y_1338_;
}
else
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1350_ = lean_string_dec_eq(v_str_1343_, v___x_1349_);
if (v___x_1350_ == 0)
{
return v___y_1338_;
}
else
{
return v_suppressElabErrors_1339_;
}
}
}
else
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1352_ = lean_string_dec_eq(v_str_1343_, v___x_1351_);
if (v___x_1352_ == 0)
{
return v___y_1338_;
}
else
{
return v_suppressElabErrors_1339_;
}
}
}
case 1:
{
lean_object* v_pre_1353_; 
v_pre_1353_ = lean_ctor_get(v_pre_1342_, 0);
if (lean_obj_tag(v_pre_1353_) == 0)
{
lean_object* v_str_1354_; lean_object* v_str_1355_; lean_object* v_str_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_str_1354_ = lean_ctor_get(v_x_1340_, 1);
v_str_1355_ = lean_ctor_get(v_pre_1341_, 1);
v_str_1356_ = lean_ctor_get(v_pre_1342_, 1);
v___x_1357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1358_ = lean_string_dec_eq(v_str_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
return v___y_1338_;
}
else
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1360_ = lean_string_dec_eq(v_str_1355_, v___x_1359_);
if (v___x_1360_ == 0)
{
return v___y_1338_;
}
else
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1362_ = lean_string_dec_eq(v_str_1354_, v___x_1361_);
if (v___x_1362_ == 0)
{
return v___y_1338_;
}
else
{
return v_suppressElabErrors_1339_;
}
}
}
}
else
{
return v___y_1338_;
}
}
default: 
{
return v___y_1338_;
}
}
}
case 0:
{
lean_object* v_str_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_str_1363_ = lean_ctor_get(v_x_1340_, 1);
v___x_1364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1365_ = lean_string_dec_eq(v_str_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
return v___y_1338_;
}
else
{
return v_suppressElabErrors_1339_;
}
}
default: 
{
return v___y_1338_;
}
}
}
else
{
return v___y_1338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1366_, lean_object* v_suppressElabErrors_1367_, lean_object* v_x_1368_){
_start:
{
uint8_t v___y_95974__boxed_1369_; uint8_t v_suppressElabErrors_boxed_1370_; uint8_t v_res_1371_; lean_object* v_r_1372_; 
v___y_95974__boxed_1369_ = lean_unbox(v___y_1366_);
v_suppressElabErrors_boxed_1370_ = lean_unbox(v_suppressElabErrors_1367_);
v_res_1371_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v___y_95974__boxed_1369_, v_suppressElabErrors_boxed_1370_, v_x_1368_);
lean_dec(v_x_1368_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1374_, lean_object* v_msgData_1375_, uint8_t v_severity_1376_, uint8_t v_isSilent_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___y_1384_; uint8_t v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1420_; uint8_t v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; uint8_t v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1456_; lean_object* v___y_1457_; uint8_t v___y_1458_; uint8_t v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; uint8_t v___y_1462_; uint8_t v___x_1467_; lean_object* v___y_1469_; lean_object* v___y_1470_; uint8_t v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; uint8_t v___y_1474_; uint8_t v___y_1475_; uint8_t v___y_1477_; uint8_t v___x_1492_; 
v___x_1467_ = 2;
v___x_1492_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1376_, v___x_1467_);
if (v___x_1492_ == 0)
{
v___y_1477_ = v___x_1492_;
goto v___jp_1476_;
}
else
{
uint8_t v___x_1493_; 
lean_inc_ref(v_msgData_1375_);
v___x_1493_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1375_);
v___y_1477_ = v___x_1493_;
goto v___jp_1476_;
}
v___jp_1383_:
{
lean_object* v___x_1393_; lean_object* v_currNamespace_1394_; lean_object* v_openDecls_1395_; lean_object* v_env_1396_; lean_object* v_nextMacroScope_1397_; lean_object* v_ngen_1398_; lean_object* v_auxDeclNGen_1399_; lean_object* v_traceState_1400_; lean_object* v_cache_1401_; lean_object* v_messages_1402_; lean_object* v_infoState_1403_; lean_object* v_snapshotTasks_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1418_; 
v___x_1393_ = lean_st_ref_take(v___y_1392_);
v_currNamespace_1394_ = lean_ctor_get(v___y_1391_, 6);
v_openDecls_1395_ = lean_ctor_get(v___y_1391_, 7);
v_env_1396_ = lean_ctor_get(v___x_1393_, 0);
v_nextMacroScope_1397_ = lean_ctor_get(v___x_1393_, 1);
v_ngen_1398_ = lean_ctor_get(v___x_1393_, 2);
v_auxDeclNGen_1399_ = lean_ctor_get(v___x_1393_, 3);
v_traceState_1400_ = lean_ctor_get(v___x_1393_, 4);
v_cache_1401_ = lean_ctor_get(v___x_1393_, 5);
v_messages_1402_ = lean_ctor_get(v___x_1393_, 6);
v_infoState_1403_ = lean_ctor_get(v___x_1393_, 7);
v_snapshotTasks_1404_ = lean_ctor_get(v___x_1393_, 8);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1406_ = v___x_1393_;
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snapshotTasks_1404_);
lean_inc(v_infoState_1403_);
lean_inc(v_messages_1402_);
lean_inc(v_cache_1401_);
lean_inc(v_traceState_1400_);
lean_inc(v_auxDeclNGen_1399_);
lean_inc(v_ngen_1398_);
lean_inc(v_nextMacroScope_1397_);
lean_inc(v_env_1396_);
lean_dec(v___x_1393_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_inc(v_openDecls_1395_);
lean_inc(v_currNamespace_1394_);
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_currNamespace_1394_);
lean_ctor_set(v___x_1408_, 1, v_openDecls_1395_);
v___x_1409_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v___y_1384_);
lean_inc_ref(v___y_1389_);
lean_inc_ref(v___y_1387_);
v___x_1410_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1410_, 0, v___y_1387_);
lean_ctor_set(v___x_1410_, 1, v___y_1386_);
lean_ctor_set(v___x_1410_, 2, v___y_1390_);
lean_ctor_set(v___x_1410_, 3, v___y_1389_);
lean_ctor_set(v___x_1410_, 4, v___x_1409_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*5, v___y_1385_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*5 + 1, v___y_1388_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*5 + 2, v_isSilent_1377_);
v___x_1411_ = l_Lean_MessageLog_add(v___x_1410_, v_messages_1402_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 6, v___x_1411_);
v___x_1413_ = v___x_1406_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_env_1396_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_nextMacroScope_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_ngen_1398_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_auxDeclNGen_1399_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_traceState_1400_);
lean_ctor_set(v_reuseFailAlloc_1417_, 5, v_cache_1401_);
lean_ctor_set(v_reuseFailAlloc_1417_, 6, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1417_, 7, v_infoState_1403_);
lean_ctor_set(v_reuseFailAlloc_1417_, 8, v_snapshotTasks_1404_);
v___x_1413_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_st_ref_set(v___y_1392_, v___x_1413_);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1443_; 
v___x_1428_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1375_);
v___x_1429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v___x_1428_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1443_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1443_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_inc_ref_n(v___y_1426_, 2);
v___x_1434_ = l_Lean_FileMap_toPosition(v___y_1426_, v___y_1425_);
lean_dec(v___y_1425_);
v___x_1435_ = l_Lean_FileMap_toPosition(v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1422_ == 0)
{
lean_del_object(v___x_1432_);
lean_dec_ref(v___y_1420_);
v___y_1384_ = v_a_1430_;
v___y_1385_ = v___y_1421_;
v___y_1386_ = v___x_1434_;
v___y_1387_ = v___y_1423_;
v___y_1388_ = v___y_1424_;
v___y_1389_ = v___x_1437_;
v___y_1390_ = v___x_1436_;
v___y_1391_ = v___y_1380_;
v___y_1392_ = v___y_1381_;
goto v___jp_1383_;
}
else
{
uint8_t v___x_1438_; 
lean_inc(v_a_1430_);
v___x_1438_ = l_Lean_MessageData_hasTag(v___y_1420_, v_a_1430_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec_ref_known(v___x_1436_, 1);
lean_dec_ref(v___x_1434_);
lean_dec(v_a_1430_);
v___x_1439_ = lean_box(0);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1439_);
v___x_1441_ = v___x_1432_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
else
{
lean_del_object(v___x_1432_);
v___y_1384_ = v_a_1430_;
v___y_1385_ = v___y_1421_;
v___y_1386_ = v___x_1434_;
v___y_1387_ = v___y_1423_;
v___y_1388_ = v___y_1424_;
v___y_1389_ = v___x_1437_;
v___y_1390_ = v___x_1436_;
v___y_1391_ = v___y_1380_;
v___y_1392_ = v___y_1381_;
goto v___jp_1383_;
}
}
}
}
v___jp_1444_:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Syntax_getTailPos_x3f(v___y_1446_, v___y_1447_);
lean_dec(v___y_1446_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_inc(v___y_1452_);
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___y_1447_;
v___y_1422_ = v___y_1449_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1450_;
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___y_1451_;
v___y_1427_ = v___y_1452_;
goto v___jp_1419_;
}
else
{
lean_object* v_val_1454_; 
v_val_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_val_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___y_1447_;
v___y_1422_ = v___y_1449_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1450_;
v___y_1425_ = v___y_1452_;
v___y_1426_ = v___y_1451_;
v___y_1427_ = v_val_1454_;
goto v___jp_1419_;
}
}
v___jp_1455_:
{
lean_object* v_ref_1463_; lean_object* v___x_1464_; 
v_ref_1463_ = l_Lean_replaceRef(v_ref_1374_, v___y_1457_);
v___x_1464_ = l_Lean_Syntax_getPos_x3f(v_ref_1463_, v___y_1458_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_unsigned_to_nat(0u);
v___y_1445_ = v___y_1456_;
v___y_1446_ = v_ref_1463_;
v___y_1447_ = v___y_1458_;
v___y_1448_ = v___y_1460_;
v___y_1449_ = v___y_1459_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1461_;
v___y_1452_ = v___x_1465_;
goto v___jp_1444_;
}
else
{
lean_object* v_val_1466_; 
v_val_1466_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v___x_1464_, 1);
v___y_1445_ = v___y_1456_;
v___y_1446_ = v_ref_1463_;
v___y_1447_ = v___y_1458_;
v___y_1448_ = v___y_1460_;
v___y_1449_ = v___y_1459_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1461_;
v___y_1452_ = v_val_1466_;
goto v___jp_1444_;
}
}
v___jp_1468_:
{
if (v___y_1475_ == 0)
{
v___y_1456_ = v___y_1472_;
v___y_1457_ = v___y_1469_;
v___y_1458_ = v___y_1474_;
v___y_1459_ = v___y_1471_;
v___y_1460_ = v___y_1470_;
v___y_1461_ = v___y_1473_;
v___y_1462_ = v_severity_1376_;
goto v___jp_1455_;
}
else
{
v___y_1456_ = v___y_1472_;
v___y_1457_ = v___y_1469_;
v___y_1458_ = v___y_1474_;
v___y_1459_ = v___y_1471_;
v___y_1460_ = v___y_1470_;
v___y_1461_ = v___y_1473_;
v___y_1462_ = v___x_1467_;
goto v___jp_1455_;
}
}
v___jp_1476_:
{
if (v___y_1477_ == 0)
{
lean_object* v_fileName_1478_; lean_object* v_fileMap_1479_; lean_object* v_options_1480_; lean_object* v_ref_1481_; uint8_t v_suppressElabErrors_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___f_1485_; uint8_t v___x_1486_; uint8_t v___x_1487_; 
v_fileName_1478_ = lean_ctor_get(v___y_1380_, 0);
v_fileMap_1479_ = lean_ctor_get(v___y_1380_, 1);
v_options_1480_ = lean_ctor_get(v___y_1380_, 2);
v_ref_1481_ = lean_ctor_get(v___y_1380_, 5);
v_suppressElabErrors_1482_ = lean_ctor_get_uint8(v___y_1380_, sizeof(void*)*14 + 1);
v___x_1483_ = lean_box(v___y_1477_);
v___x_1484_ = lean_box(v_suppressElabErrors_1482_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1485_, 0, v___x_1483_);
lean_closure_set(v___f_1485_, 1, v___x_1484_);
v___x_1486_ = 1;
v___x_1487_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1376_, v___x_1486_);
if (v___x_1487_ == 0)
{
v___y_1469_ = v_ref_1481_;
v___y_1470_ = v_fileName_1478_;
v___y_1471_ = v_suppressElabErrors_1482_;
v___y_1472_ = v___f_1485_;
v___y_1473_ = v_fileMap_1479_;
v___y_1474_ = v___y_1477_;
v___y_1475_ = v___x_1487_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = l_Lean_warningAsError;
v___x_1489_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_1480_, v___x_1488_);
v___y_1469_ = v_ref_1481_;
v___y_1470_ = v_fileName_1478_;
v___y_1471_ = v_suppressElabErrors_1482_;
v___y_1472_ = v___f_1485_;
v___y_1473_ = v_fileMap_1479_;
v___y_1474_ = v___y_1477_;
v___y_1475_ = v___x_1489_;
goto v___jp_1468_;
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec_ref(v_msgData_1375_);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1494_, lean_object* v_msgData_1495_, lean_object* v_severity_1496_, lean_object* v_isSilent_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_severity_boxed_1503_; uint8_t v_isSilent_boxed_1504_; lean_object* v_res_1505_; 
v_severity_boxed_1503_ = lean_unbox(v_severity_1496_);
v_isSilent_boxed_1504_ = lean_unbox(v_isSilent_1497_);
v_res_1505_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1494_, v_msgData_1495_, v_severity_boxed_1503_, v_isSilent_boxed_1504_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v_ref_1494_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(lean_object* v_ref_1506_, lean_object* v_msgData_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v___x_1517_; uint8_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = 1;
v___x_1518_ = 0;
v___x_1519_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1506_, v_msgData_1507_, v___x_1517_, v___x_1518_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(lean_object* v_ref_1520_, lean_object* v_msgData_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_ref_1520_, v_msgData_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v_ref_1520_);
return v_res_1531_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_linterOption_1538_, lean_object* v_stx_1539_, lean_object* v_msg_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_name_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1568_; 
v_name_1550_ = lean_ctor_get(v_linterOption_1538_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_linterOption_1538_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_linterOption_1538_, 1);
lean_dec(v_unused_1569_);
v___x_1552_ = v_linterOption_1538_;
v_isShared_1553_ = v_isSharedCheck_1568_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_name_1550_);
lean_dec(v_linterOption_1538_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1568_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1554_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
lean_inc(v_name_1550_);
v___x_1555_ = l_Lean_MessageData_ofName(v_name_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 7);
lean_ctor_set(v___x_1552_, 1, v___x_1555_);
lean_ctor_set(v___x_1552_, 0, v___x_1554_);
v___x_1557_ = v___x_1552_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_disable_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1558_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v_disable_1560_ = l_Lean_MessageData_note(v___x_1559_);
v___x_1561_ = l_Lean_Linter_linterMessageTag;
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_msg_1540_);
lean_ctor_set(v___x_1562_, 1, v_disable_1560_);
v___x_1563_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_name_1550_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
lean_inc(v_stx_1539_);
v___x_1565_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_stx_1539_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_stx_1539_, v___x_1565_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v_stx_1539_);
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_linterOption_1570_, lean_object* v_stx_1571_, lean_object* v_msg_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_linterOption_1570_, v_stx_1571_, v_msg_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object* v___y_1583_, lean_object* v_mkInfoTree_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v_a_1592_, lean_object* v_a_x3f_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v_infoState_1596_; lean_object* v_trees_1597_; lean_object* v___x_1598_; 
v___x_1595_ = lean_st_ref_get(v___y_1583_);
v_infoState_1596_ = lean_ctor_get(v___x_1595_, 7);
lean_inc_ref(v_infoState_1596_);
lean_dec(v___x_1595_);
v_trees_1597_ = lean_ctor_get(v_infoState_1596_, 2);
lean_inc_ref(v_trees_1597_);
lean_dec_ref(v_infoState_1596_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
v___x_1598_ = lean_apply_10(v_mkInfoTree_1584_, v_trees_1597_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1583_, lean_box(0));
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1637_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1637_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1637_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v_infoState_1604_; lean_object* v_env_1605_; lean_object* v_nextMacroScope_1606_; lean_object* v_ngen_1607_; lean_object* v_auxDeclNGen_1608_; lean_object* v_traceState_1609_; lean_object* v_cache_1610_; lean_object* v_messages_1611_; lean_object* v_snapshotTasks_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1636_; 
v___x_1603_ = lean_st_ref_take(v___y_1583_);
v_infoState_1604_ = lean_ctor_get(v___x_1603_, 7);
v_env_1605_ = lean_ctor_get(v___x_1603_, 0);
v_nextMacroScope_1606_ = lean_ctor_get(v___x_1603_, 1);
v_ngen_1607_ = lean_ctor_get(v___x_1603_, 2);
v_auxDeclNGen_1608_ = lean_ctor_get(v___x_1603_, 3);
v_traceState_1609_ = lean_ctor_get(v___x_1603_, 4);
v_cache_1610_ = lean_ctor_get(v___x_1603_, 5);
v_messages_1611_ = lean_ctor_get(v___x_1603_, 6);
v_snapshotTasks_1612_ = lean_ctor_get(v___x_1603_, 8);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1614_ = v___x_1603_;
v_isShared_1615_ = v_isSharedCheck_1636_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_snapshotTasks_1612_);
lean_inc(v_infoState_1604_);
lean_inc(v_messages_1611_);
lean_inc(v_cache_1610_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1608_);
lean_inc(v_ngen_1607_);
lean_inc(v_nextMacroScope_1606_);
lean_inc(v_env_1605_);
lean_dec(v___x_1603_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1636_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
uint8_t v_enabled_1616_; lean_object* v_assignment_1617_; lean_object* v_lazyAssignment_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1634_; 
v_enabled_1616_ = lean_ctor_get_uint8(v_infoState_1604_, sizeof(void*)*3);
v_assignment_1617_ = lean_ctor_get(v_infoState_1604_, 0);
v_lazyAssignment_1618_ = lean_ctor_get(v_infoState_1604_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_infoState_1604_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v_infoState_1604_, 2);
lean_dec(v_unused_1635_);
v___x_1620_ = v_infoState_1604_;
v_isShared_1621_ = v_isSharedCheck_1634_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_lazyAssignment_1618_);
lean_inc(v_assignment_1617_);
lean_dec(v_infoState_1604_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1634_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = l_Lean_PersistentArray_push___redArg(v_a_1592_, v_a_1599_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 2, v___x_1622_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_assignment_1617_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_lazyAssignment_1618_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v___x_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*3, v_enabled_1616_);
v___x_1624_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1626_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 7, v___x_1624_);
v___x_1626_ = v___x_1614_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_env_1605_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_nextMacroScope_1606_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_ngen_1607_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_auxDeclNGen_1608_);
lean_ctor_set(v_reuseFailAlloc_1632_, 4, v_traceState_1609_);
lean_ctor_set(v_reuseFailAlloc_1632_, 5, v_cache_1610_);
lean_ctor_set(v_reuseFailAlloc_1632_, 6, v_messages_1611_);
lean_ctor_set(v_reuseFailAlloc_1632_, 7, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1632_, 8, v_snapshotTasks_1612_);
v___x_1626_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1627_ = lean_st_ref_set(v___y_1583_, v___x_1626_);
v___x_1628_ = lean_box(0);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1628_);
v___x_1630_ = v___x_1601_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_a_1592_);
v_a_1638_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1598_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1598_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object* v___y_1646_, lean_object* v_mkInfoTree_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v_a_1655_, lean_object* v_a_x3f_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1646_, v_mkInfoTree_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v_a_1655_, v_a_x3f_1656_);
lean_dec(v_a_x3f_1656_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1646_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object* v_x_1659_, lean_object* v_mkInfoTree_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v_infoState_1671_; uint8_t v_enabled_1672_; 
v___x_1670_ = lean_st_ref_get(v___y_1668_);
v_infoState_1671_ = lean_ctor_get(v___x_1670_, 7);
lean_inc_ref(v_infoState_1671_);
lean_dec(v___x_1670_);
v_enabled_1672_ = lean_ctor_get_uint8(v_infoState_1671_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1671_);
if (v_enabled_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_dec_ref(v_mkInfoTree_1660_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1661_);
v___x_1673_ = lean_apply_9(v_x_1659_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, lean_box(0));
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v_a_1675_; lean_object* v_r_1676_; 
v___x_1674_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1668_);
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref(v___x_1674_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1661_);
v_r_1676_ = lean_apply_9(v_x_1659_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, lean_box(0));
if (lean_obj_tag(v_r_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1701_; 
v_a_1677_ = lean_ctor_get(v_r_1676_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_r_1676_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1679_ = v_r_1676_;
v_isShared_1680_ = v_isSharedCheck_1701_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v_r_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1701_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
lean_inc(v_a_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 1);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1668_, v_mkInfoTree_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v_a_1675_, v___x_1682_);
lean_dec_ref(v___x_1682_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v___x_1683_, 0);
lean_dec(v_unused_1691_);
v___x_1685_ = v___x_1683_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_dec(v___x_1683_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v_a_1677_);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1677_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_a_1677_);
v_a_1692_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1683_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1683_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_a_1702_ = lean_ctor_get(v_r_1676_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v_r_1676_, 1);
v___x_1703_ = lean_box(0);
v___x_1704_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1668_, v_mkInfoTree_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v_a_1675_, v___x_1703_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v___x_1704_, 0);
lean_dec(v_unused_1712_);
v___x_1706_ = v___x_1704_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_dec(v___x_1704_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 1);
lean_ctor_set(v___x_1706_, 0, v_a_1702_);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1702_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_a_1702_);
v_a_1713_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1704_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1704_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object* v_x_1721_, lean_object* v_mkInfoTree_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_1721_, v_mkInfoTree_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v_env_1737_; lean_object* v___x_1738_; lean_object* v_toEnvExtension_1739_; lean_object* v_asyncMode_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_merged_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v___x_1736_ = lean_st_ref_get(v___y_1734_);
v_env_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc_ref(v_env_1737_);
lean_dec(v___x_1736_);
v___x_1738_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1739_ = lean_ctor_get(v___x_1738_, 0);
v_asyncMode_1740_ = lean_ctor_get(v_toEnvExtension_1739_, 2);
v___x_1741_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1742_ = lean_box(0);
v___x_1743_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1741_, v___x_1738_, v_env_1737_, v_asyncMode_1740_, v___x_1742_);
v_merged_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1743_, 1);
lean_dec(v_unused_1753_);
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_merged_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v_merged_1744_);
lean_ctor_set(v___x_1746_, 0, v_o_1733_);
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_o_1733_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_merged_1744_);
v___x_1749_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_1754_, v___y_1755_);
lean_dec(v___y_1755_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_options_1767_; lean_object* v___x_1768_; 
v_options_1767_ = lean_ctor_get(v___y_1764_, 2);
lean_inc_ref(v_options_1767_);
v___x_1768_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_1767_, v___y_1765_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2));
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6));
v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
return v___x_1790_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8));
v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10));
v___x_1796_ = l_Lean_stringToMessageData(v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_usingArg_1800_, lean_object* v_snd_1801_, uint8_t v___x_1802_, uint8_t v___x_1803_, lean_object* v___x_1804_, uint8_t v_useReducible_1805_, uint8_t v___x_1806_, lean_object* v___x_1807_, lean_object* v___x_1808_, lean_object* v_simprocs_1809_, lean_object* v_discharge_x3f_1810_, lean_object* v_snd_1811_, lean_object* v___x_1812_, lean_object* v___f_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; 
if (lean_obj_tag(v_usingArg_1800_) == 1)
{
lean_object* v_val_2004_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___x_2056_; lean_object* v_infoState_2057_; uint8_t v_enabled_2058_; 
v_val_2004_ = lean_ctor_get(v_usingArg_1800_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v_usingArg_1800_, 1);
v___x_2056_ = lean_st_ref_get(v___y_1821_);
v_infoState_2057_ = lean_ctor_get(v___x_2056_, 7);
lean_inc_ref(v_infoState_2057_);
lean_dec(v___x_2056_);
v_enabled_2058_ = lean_ctor_get_uint8(v_infoState_2057_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2057_);
if (v_enabled_2058_ == 0)
{
lean_dec_ref(v___f_1813_);
v___y_2006_ = v___y_1814_;
v___y_2007_ = v___y_1815_;
v___y_2008_ = v___y_1816_;
v___y_2009_ = v___y_1817_;
v___y_2010_ = v___y_1818_;
v___y_2011_ = v___y_1819_;
v___y_2012_ = v___y_1820_;
v___y_2013_ = v___y_1821_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2059_; lean_object* v_a_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; 
v___x_2059_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1821_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref(v___x_2059_);
v___f_2061_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2061_, 0, v_a_2060_);
v___x_2062_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_2061_, v___f_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_dec_ref_known(v___x_2062_, 1);
v___y_2006_ = v___y_1814_;
v___y_2007_ = v___y_1815_;
v___y_2008_ = v___y_1816_;
v___y_2009_ = v___y_1817_;
v___y_2010_ = v___y_1818_;
v___y_2011_ = v___y_1819_;
v___y_2012_ = v___y_1820_;
v___y_2013_ = v___y_1821_;
goto v___jp_2005_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_val_2004_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
v___jp_2005_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_st_ref_get(v___y_2011_);
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Lean_Elab_Tactic_elabTerm(v_val_2004_, v___x_2015_, v___x_1802_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc_n(v_a_2017_, 2);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_1801_, v_a_2017_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_mctx_2019_; lean_object* v_a_2020_; uint8_t v___x_2021_; 
v_mctx_2019_ = lean_ctor_get(v___x_2014_, 0);
lean_inc_ref(v_mctx_2019_);
lean_dec(v___x_2014_);
v_a_2020_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2021_ = lean_unbox(v_a_2020_);
lean_dec(v_a_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_mctx_2019_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
v___x_2022_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
v___x_2023_ = l_Lean_indentExpr(v_a_2017_);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = l_Lean_Expr_mvar___override(v_snd_1801_);
v___x_2028_ = l_Lean_MessageData_ofExpr(v___x_2027_);
v___x_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2026_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_2029_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
else
{
lean_object* v_mvarCounter_2039_; 
v_mvarCounter_2039_ = lean_ctor_get(v_mctx_2019_, 3);
lean_inc(v_mvarCounter_2039_);
lean_dec_ref(v_mctx_2019_);
lean_inc(v_a_2017_);
v___y_1888_ = v_mvarCounter_2039_;
v___y_1889_ = v___x_2015_;
v___y_1890_ = v_a_2017_;
v___y_1891_ = v___x_2015_;
v___y_1892_ = v_a_2017_;
v___y_1893_ = v___y_2006_;
v___y_1894_ = v___y_2007_;
v___y_1895_ = v___y_2008_;
v___y_1896_ = v___y_2009_;
v___y_1897_ = v___y_2010_;
v___y_1898_ = v___y_2011_;
v___y_1899_ = v___y_2012_;
v___y_1900_ = v___y_2013_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_2017_);
lean_dec(v___x_2014_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_2040_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2018_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2018_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v___x_2014_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_2048_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2016_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2016_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
else
{
lean_object* v_lctx_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref(v___f_1813_);
lean_dec_ref(v___x_1804_);
lean_dec(v_usingArg_1800_);
v_lctx_2071_ = lean_ctor_get(v___y_1818_, 2);
v___x_2072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13));
v___x_2073_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2071_, v___x_2072_);
if (lean_obj_tag(v___x_2073_) == 1)
{
lean_object* v_val_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_val_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_val_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2075_ = l_Lean_LocalDecl_fvarId(v_val_2074_);
lean_dec(v_val_2074_);
v___x_2076_ = lean_mk_empty_array_with_capacity(v___x_1807_);
v___x_2077_ = lean_array_push(v___x_2076_, v___x_2075_);
lean_inc_ref(v_snd_1811_);
v___x_2078_ = l_Lean_Meta_simpGoal(v_snd_1801_, v___x_1808_, v_simprocs_1809_, v_discharge_x3f_1810_, v___x_1803_, v___x_2077_, v_snd_1811_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2107_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2107_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2107_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_fst_2083_; 
v_fst_2083_ = lean_ctor_get(v_a_2079_, 0);
if (lean_obj_tag(v_fst_2083_) == 1)
{
lean_object* v_val_2084_; lean_object* v_snd_2085_; lean_object* v_snd_2086_; lean_object* v___x_2087_; 
lean_del_object(v___x_2081_);
lean_dec_ref(v_snd_1811_);
v_val_2084_ = lean_ctor_get(v_fst_2083_, 0);
lean_inc(v_val_2084_);
v_snd_2085_ = lean_ctor_get(v_a_2079_, 1);
lean_inc(v_snd_2085_);
lean_dec(v_a_2079_);
v_snd_2086_ = lean_ctor_get(v_val_2084_, 1);
lean_inc(v_snd_2086_);
lean_dec(v_val_2084_);
v___x_2087_ = l_Lean_MVarId_assumption(v_snd_2086_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v___x_2087_, 0);
lean_dec(v_unused_2095_);
v___x_2089_ = v___x_2087_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v___x_2087_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v_snd_2085_);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_snd_2085_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_snd_2085_);
v_a_2096_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2087_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2087_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v___x_2105_; 
lean_dec(v_a_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v_snd_1811_);
v___x_2105_ = v___x_2081_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_snd_1811_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_snd_1811_);
v_a_2108_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2078_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2078_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v___x_2116_; 
lean_dec(v___x_2073_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
v___x_2116_ = l_Lean_MVarId_assumption(v_snd_1801_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; 
v_unused_2124_ = lean_ctor_get(v___x_2116_, 0);
lean_dec(v_unused_2124_);
v___x_2118_ = v___x_2116_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v___x_2116_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_snd_1811_);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_snd_1811_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v_snd_1811_);
v_a_2125_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2116_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2116_);
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
v___jp_1823_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v___x_1827_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_1801_, v___y_1825_, v___y_1826_);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v___x_1827_, 0);
lean_dec(v_unused_1835_);
v___x_1829_ = v___x_1827_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_dec(v___x_1827_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___y_1824_);
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___y_1824_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
v___jp_1836_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Core_mkFreshUserName(v___y_1851_, v___y_1850_, v___y_1844_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc_n(v_a_1854_, 2);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l_Lean_MVarId_rename(v___y_1842_, v___y_1852_, v_a_1854_, v___y_1848_, v___y_1843_, v___y_1850_, v___y_1844_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___f_1861_; lean_object* v___x_1862_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc_n(v_a_1856_, 2);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = lean_box(v___x_1802_);
v___x_1858_ = lean_box(v___x_1803_);
v___x_1859_ = lean_box(v_useReducible_1805_);
v___x_1860_ = lean_box(v___x_1806_);
v___f_1861_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 19, 10);
lean_closure_set(v___f_1861_, 0, v_a_1856_);
lean_closure_set(v___f_1861_, 1, v_a_1854_);
lean_closure_set(v___f_1861_, 2, v___x_1857_);
lean_closure_set(v___f_1861_, 3, v___x_1858_);
lean_closure_set(v___f_1861_, 4, v___y_1839_);
lean_closure_set(v___f_1861_, 5, v___y_1838_);
lean_closure_set(v___f_1861_, 6, v___x_1804_);
lean_closure_set(v___f_1861_, 7, v___y_1837_);
lean_closure_set(v___f_1861_, 8, v___x_1859_);
lean_closure_set(v___f_1861_, 9, v___x_1860_);
v___x_1862_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1856_, v___f_1861_, v___y_1846_, v___y_1845_, v___y_1841_, v___y_1849_, v___y_1848_, v___y_1843_, v___y_1850_, v___y_1844_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_dec_ref_known(v___x_1862_, 1);
v___y_1824_ = v___y_1847_;
v___y_1825_ = v___y_1840_;
v___y_1826_ = v___y_1843_;
goto v___jp_1823_;
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___y_1840_);
lean_dec(v_snd_1801_);
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
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
lean_dec(v_a_1854_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_1871_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1855_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1855_);
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
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_1879_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1853_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1853_);
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
v___jp_1887_:
{
lean_object* v___x_1901_; 
lean_inc(v_snd_1801_);
v___x_1901_ = l_Lean_MVarId_getType(v_snd_1801_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
lean_inc(v_snd_1801_);
v___x_1903_ = l_Lean_MVarId_getTag(v_snd_1801_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1902_, v_a_1904_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = l_Lean_Expr_mvarId_x21(v_a_1906_);
v___x_1908_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1));
lean_inc_ref(v___y_1892_);
v___x_1909_ = l_Lean_MVarId_note(v___x_1907_, v___x_1908_, v___y_1892_, v___y_1891_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v_fst_1911_; lean_object* v_snd_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1971_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v_fst_1911_ = lean_ctor_get(v_a_1910_, 0);
v_snd_1912_ = lean_ctor_get(v_a_1910_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_a_1910_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1914_ = v_a_1910_;
v_isShared_1915_ = v_isSharedCheck_1971_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snd_1912_);
lean_inc(v_fst_1911_);
lean_dec(v_a_1910_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1971_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_mk_empty_array_with_capacity(v___x_1807_);
lean_inc(v_fst_1911_);
v___x_1917_ = lean_array_push(v___x_1916_, v_fst_1911_);
v___x_1918_ = l_Lean_Meta_simpGoal(v_snd_1912_, v___x_1808_, v_simprocs_1809_, v_discharge_x3f_1810_, v___x_1803_, v___x_1917_, v_snd_1811_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v_fst_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v_fst_1920_ = lean_ctor_get(v_a_1919_, 0);
if (lean_obj_tag(v_fst_1920_) == 0)
{
lean_object* v_snd_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_fst_1911_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___x_1804_);
v_snd_1921_ = lean_ctor_get(v_a_1919_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1919_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v_a_1919_, 0);
lean_dec(v_unused_1955_);
v___x_1923_ = v_a_1919_;
v_isShared_1924_ = v_isSharedCheck_1954_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snd_1921_);
lean_dec(v_a_1919_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1954_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v_a_1926_; uint8_t v___x_1927_; 
v___x_1925_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
v___x_1927_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1926_);
lean_dec(v_a_1926_);
if (v___x_1927_ == 0)
{
lean_del_object(v___x_1923_);
lean_del_object(v___x_1914_);
lean_dec_ref(v___y_1892_);
v___y_1824_ = v_snd_1921_;
v___y_1825_ = v_a_1906_;
v___y_1826_ = v___y_1898_;
goto v___jp_1823_;
}
else
{
if (lean_obj_tag(v___y_1892_) == 1)
{
lean_object* v_fvarId_1928_; lean_object* v_lctx_1929_; lean_object* v___x_1930_; 
v_fvarId_1928_ = lean_ctor_get(v___y_1892_, 0);
v_lctx_1929_ = lean_ctor_get(v___y_1897_, 2);
lean_inc(v_fvarId_1928_);
lean_inc_ref(v_lctx_1929_);
v___x_1930_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1929_, v_fvarId_1928_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_dec_ref_known(v___y_1892_, 1);
lean_del_object(v___x_1923_);
lean_del_object(v___x_1914_);
v___y_1824_ = v_snd_1921_;
v___y_1825_ = v_a_1906_;
v___y_1826_ = v___y_1898_;
goto v___jp_1823_;
}
else
{
lean_dec_ref_known(v___x_1930_, 1);
if (v___x_1806_ == 0)
{
lean_dec_ref_known(v___y_1892_, 1);
lean_del_object(v___x_1923_);
lean_del_object(v___x_1914_);
v___y_1824_ = v_snd_1921_;
v___y_1825_ = v_a_1906_;
v___y_1826_ = v___y_1898_;
goto v___jp_1823_;
}
else
{
lean_object* v_ref_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v_ref_1931_ = lean_ctor_get(v___y_1899_, 5);
v___x_1932_ = l_Lean_linter_unnecessarySimpa;
v___x_1933_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_1934_ = l_Lean_MessageData_ofExpr(v___y_1892_);
lean_inc_ref(v___x_1934_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set_tag(v___x_1923_, 7);
lean_ctor_set(v___x_1923_, 1, v___x_1934_);
lean_ctor_set(v___x_1923_, 0, v___x_1933_);
v___x_1936_ = v___x_1923_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 7);
lean_ctor_set(v___x_1914_, 1, v___x_1937_);
lean_ctor_set(v___x_1914_, 0, v___x_1936_);
v___x_1939_ = v___x_1914_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1934_);
v___x_1941_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
lean_inc(v_ref_1931_);
v___x_1943_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_1932_, v_ref_1931_, v___x_1942_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_dec_ref_known(v___x_1943_, 1);
v___y_1824_ = v_snd_1921_;
v___y_1825_ = v_a_1906_;
v___y_1826_ = v___y_1898_;
goto v___jp_1823_;
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_snd_1921_);
lean_dec(v_a_1906_);
lean_dec(v_snd_1801_);
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
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
}
}
}
}
else
{
lean_del_object(v___x_1923_);
lean_del_object(v___x_1914_);
lean_dec_ref(v___y_1892_);
v___y_1824_ = v_snd_1921_;
v___y_1825_ = v_a_1906_;
v___y_1826_ = v___y_1898_;
goto v___jp_1823_;
}
}
}
}
else
{
lean_object* v_val_1956_; lean_object* v_snd_1957_; lean_object* v_fst_1958_; lean_object* v_snd_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
lean_del_object(v___x_1914_);
lean_dec_ref(v___y_1892_);
v_val_1956_ = lean_ctor_get(v_fst_1920_, 0);
lean_inc(v_val_1956_);
v_snd_1957_ = lean_ctor_get(v_a_1919_, 1);
lean_inc(v_snd_1957_);
lean_dec(v_a_1919_);
v_fst_1958_ = lean_ctor_get(v_val_1956_, 0);
lean_inc(v_fst_1958_);
v_snd_1959_ = lean_ctor_get(v_val_1956_, 1);
lean_inc(v_snd_1959_);
lean_dec(v_val_1956_);
v___x_1960_ = lean_array_get_size(v_fst_1958_);
v___x_1961_ = lean_nat_dec_lt(v___x_1812_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_dec(v_fst_1958_);
v___y_1837_ = v___y_1889_;
v___y_1838_ = v___y_1888_;
v___y_1839_ = v___y_1890_;
v___y_1840_ = v_a_1906_;
v___y_1841_ = v___y_1895_;
v___y_1842_ = v_snd_1959_;
v___y_1843_ = v___y_1898_;
v___y_1844_ = v___y_1900_;
v___y_1845_ = v___y_1894_;
v___y_1846_ = v___y_1893_;
v___y_1847_ = v_snd_1957_;
v___y_1848_ = v___y_1897_;
v___y_1849_ = v___y_1896_;
v___y_1850_ = v___y_1899_;
v___y_1851_ = v___x_1908_;
v___y_1852_ = v_fst_1911_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1962_; 
lean_dec(v_fst_1911_);
v___x_1962_ = lean_array_fget(v_fst_1958_, v___x_1812_);
lean_dec(v_fst_1958_);
v___y_1837_ = v___y_1889_;
v___y_1838_ = v___y_1888_;
v___y_1839_ = v___y_1890_;
v___y_1840_ = v_a_1906_;
v___y_1841_ = v___y_1895_;
v___y_1842_ = v_snd_1959_;
v___y_1843_ = v___y_1898_;
v___y_1844_ = v___y_1900_;
v___y_1845_ = v___y_1894_;
v___y_1846_ = v___y_1893_;
v___y_1847_ = v_snd_1957_;
v___y_1848_ = v___y_1897_;
v___y_1849_ = v___y_1896_;
v___y_1850_ = v___y_1899_;
v___y_1851_ = v___x_1908_;
v___y_1852_ = v___x_1962_;
goto v___jp_1836_;
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_del_object(v___x_1914_);
lean_dec(v_fst_1911_);
lean_dec(v_a_1906_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_1963_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1918_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1918_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_a_1906_);
lean_dec_ref(v___y_1892_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_1972_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1909_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1909_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_1980_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1905_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1905_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_a_1902_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_1988_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1903_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1903_);
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
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v_snd_1811_);
lean_dec(v_discharge_x3f_1810_);
lean_dec_ref(v_simprocs_1809_);
lean_dec_ref(v___x_1808_);
lean_dec_ref(v___x_1804_);
lean_dec(v_snd_1801_);
v_a_1996_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1901_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1901_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2133_ = _args[0];
lean_object* v_snd_2134_ = _args[1];
lean_object* v___x_2135_ = _args[2];
lean_object* v___x_2136_ = _args[3];
lean_object* v___x_2137_ = _args[4];
lean_object* v_useReducible_2138_ = _args[5];
lean_object* v___x_2139_ = _args[6];
lean_object* v___x_2140_ = _args[7];
lean_object* v___x_2141_ = _args[8];
lean_object* v_simprocs_2142_ = _args[9];
lean_object* v_discharge_x3f_2143_ = _args[10];
lean_object* v_snd_2144_ = _args[11];
lean_object* v___x_2145_ = _args[12];
lean_object* v___f_2146_ = _args[13];
lean_object* v___y_2147_ = _args[14];
lean_object* v___y_2148_ = _args[15];
lean_object* v___y_2149_ = _args[16];
lean_object* v___y_2150_ = _args[17];
lean_object* v___y_2151_ = _args[18];
lean_object* v___y_2152_ = _args[19];
lean_object* v___y_2153_ = _args[20];
lean_object* v___y_2154_ = _args[21];
lean_object* v___y_2155_ = _args[22];
_start:
{
uint8_t v___x_96709__boxed_2156_; uint8_t v___x_96710__boxed_2157_; uint8_t v_useReducible_boxed_2158_; uint8_t v___x_96712__boxed_2159_; lean_object* v_res_2160_; 
v___x_96709__boxed_2156_ = lean_unbox(v___x_2135_);
v___x_96710__boxed_2157_ = lean_unbox(v___x_2136_);
v_useReducible_boxed_2158_ = lean_unbox(v_useReducible_2138_);
v___x_96712__boxed_2159_ = lean_unbox(v___x_2139_);
v_res_2160_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2133_, v_snd_2134_, v___x_96709__boxed_2156_, v___x_96710__boxed_2157_, v___x_2137_, v_useReducible_boxed_2158_, v___x_96712__boxed_2159_, v___x_2140_, v___x_2141_, v_simprocs_2142_, v_discharge_x3f_2143_, v_snd_2144_, v___x_2145_, v___f_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___x_2145_);
lean_dec(v___x_2140_);
return v_res_2160_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2161_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_unsigned_to_nat(32u);
v___x_2165_ = lean_mk_empty_array_with_capacity(v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2171_ = l_Lean_MessageData_ofFormat(v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v___x_2172_, lean_object* v_tk_2173_, lean_object* v___x_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v_simprocs_2177_, uint8_t v___x_2178_, lean_object* v_usingArg_2179_, uint8_t v___x_2180_, lean_object* v___x_2181_, uint8_t v_useReducible_2182_, uint8_t v___x_2183_, lean_object* v___x_2184_, lean_object* v_usingTk_x3f_2185_, lean_object* v_discharge_x3f_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___y_2197_; 
if (lean_obj_tag(v_usingTk_x3f_2185_) == 0)
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_box(0);
v___y_2197_ = v___x_2302_;
goto v___jp_2196_;
}
else
{
lean_object* v_val_2303_; 
v_val_2303_ = lean_ctor_get(v_usingTk_x3f_2185_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v_usingTk_x3f_2185_, 1);
v___y_2197_ = v_val_2303_;
goto v___jp_2196_;
}
v___jp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2198_ = lean_mk_empty_array_with_capacity(v___x_2172_);
v___x_2199_ = lean_array_push(v___x_2198_, v_tk_2173_);
v___x_2200_ = lean_array_push(v___x_2199_, v___y_2197_);
v___x_2201_ = lean_box(2);
v___x_2202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2174_);
lean_ctor_set(v___x_2202_, 2, v___x_2200_);
v___x_2203_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2202_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2188_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = lean_mk_empty_array_with_capacity(v___x_2175_);
v___x_2208_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
lean_inc_n(v___x_2175_, 3);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2175_);
v___x_2210_ = lean_unsigned_to_nat(32u);
v___x_2211_ = lean_mk_empty_array_with_capacity(v___x_2210_);
v___x_2212_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
v___x_2213_ = ((size_t)5ULL);
v___x_2214_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2211_);
lean_ctor_set(v___x_2214_, 2, v___x_2175_);
lean_ctor_set(v___x_2214_, 3, v___x_2175_);
lean_ctor_set_usize(v___x_2214_, 4, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2208_);
lean_ctor_set(v___x_2215_, 1, v___x_2208_);
lean_ctor_set(v___x_2215_, 2, v___x_2208_);
lean_ctor_set(v___x_2215_, 3, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2209_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
lean_inc_ref(v___x_2216_);
lean_inc(v_discharge_x3f_2186_);
lean_inc_ref(v_simprocs_2177_);
lean_inc_ref(v___x_2176_);
v___x_2217_ = l_Lean_Meta_simpGoal(v_a_2206_, v___x_2176_, v_simprocs_2177_, v_discharge_x3f_2186_, v___x_2178_, v___x_2207_, v___x_2216_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v_fst_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v_fst_2219_ = lean_ctor_get(v_a_2218_, 0);
if (lean_obj_tag(v_fst_2219_) == 1)
{
lean_object* v_val_2220_; lean_object* v_snd_2221_; lean_object* v_snd_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref_known(v___x_2216_, 2);
v_val_2220_ = lean_ctor_get(v_fst_2219_, 0);
lean_inc(v_val_2220_);
v_snd_2221_ = lean_ctor_get(v_a_2218_, 1);
lean_inc(v_snd_2221_);
lean_dec(v_a_2218_);
v_snd_2222_ = lean_ctor_get(v_val_2220_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_val_2220_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v_val_2220_, 0);
lean_dec(v_unused_2247_);
v___x_2224_ = v_val_2220_;
v_isShared_2225_ = v_isSharedCheck_2246_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_snd_2222_);
lean_dec(v_val_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2246_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = lean_box(0);
lean_inc(v_snd_2222_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 1);
lean_ctor_set(v___x_2224_, 1, v___x_2226_);
lean_ctor_set(v___x_2224_, 0, v_snd_2222_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_snd_2222_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2228_, v___y_2188_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___y_2235_; lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2229_, 1);
v___f_2230_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2230_, 0, v_a_2204_);
v___x_2231_ = lean_box(v___x_2178_);
v___x_2232_ = lean_box(v___x_2180_);
v___x_2233_ = lean_box(v_useReducible_2182_);
v___x_2234_ = lean_box(v___x_2183_);
lean_inc(v_snd_2222_);
v___y_2235_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 23, 14);
lean_closure_set(v___y_2235_, 0, v_usingArg_2179_);
lean_closure_set(v___y_2235_, 1, v_snd_2222_);
lean_closure_set(v___y_2235_, 2, v___x_2231_);
lean_closure_set(v___y_2235_, 3, v___x_2232_);
lean_closure_set(v___y_2235_, 4, v___x_2181_);
lean_closure_set(v___y_2235_, 5, v___x_2233_);
lean_closure_set(v___y_2235_, 6, v___x_2234_);
lean_closure_set(v___y_2235_, 7, v___x_2184_);
lean_closure_set(v___y_2235_, 8, v___x_2176_);
lean_closure_set(v___y_2235_, 9, v_simprocs_2177_);
lean_closure_set(v___y_2235_, 10, v_discharge_x3f_2186_);
lean_closure_set(v___y_2235_, 11, v_snd_2221_);
lean_closure_set(v___y_2235_, 12, v___x_2175_);
lean_closure_set(v___y_2235_, 13, v___f_2230_);
v___x_2236_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_2222_, v___y_2235_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
return v___x_2236_;
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_snd_2222_);
lean_dec(v_snd_2221_);
lean_dec(v_a_2204_);
lean_dec(v_discharge_x3f_2186_);
lean_dec(v___x_2184_);
lean_dec_ref(v___x_2181_);
lean_dec(v_usingArg_2179_);
lean_dec_ref(v_simprocs_2177_);
lean_dec_ref(v___x_2176_);
lean_dec(v___x_2175_);
v_a_2237_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2229_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2229_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
}
else
{
lean_object* v___x_2248_; lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_a_2218_);
lean_dec(v_a_2204_);
lean_dec(v_discharge_x3f_2186_);
lean_dec(v___x_2184_);
lean_dec_ref(v___x_2181_);
lean_dec(v_usingArg_2179_);
lean_dec_ref(v_simprocs_2177_);
lean_dec_ref(v___x_2176_);
lean_dec(v___x_2175_);
v___x_2248_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2277_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2277_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
uint8_t v___x_2253_; 
v___x_2253_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2249_);
lean_dec(v_a_2249_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2255_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2216_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2216_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
else
{
lean_object* v_ref_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_del_object(v___x_2251_);
v_ref_2257_ = lean_ctor_get(v___y_2193_, 5);
v___x_2258_ = l_Lean_linter_unnecessarySimpa;
v___x_2259_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
lean_inc(v_ref_2257_);
v___x_2260_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2258_, v_ref_2257_, v___x_2259_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v___x_2260_, 0);
lean_dec(v_unused_2268_);
v___x_2262_ = v___x_2260_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_dec(v___x_2260_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2216_);
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2216_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref_known(v___x_2216_, 2);
v_a_2269_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2260_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2260_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref_known(v___x_2216_, 2);
lean_dec(v_a_2204_);
lean_dec(v_discharge_x3f_2186_);
lean_dec(v___x_2184_);
lean_dec_ref(v___x_2181_);
lean_dec(v_usingArg_2179_);
lean_dec_ref(v_simprocs_2177_);
lean_dec_ref(v___x_2176_);
lean_dec(v___x_2175_);
v_a_2278_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2217_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2217_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_a_2204_);
lean_dec(v_discharge_x3f_2186_);
lean_dec(v___x_2184_);
lean_dec_ref(v___x_2181_);
lean_dec(v_usingArg_2179_);
lean_dec_ref(v_simprocs_2177_);
lean_dec_ref(v___x_2176_);
lean_dec(v___x_2175_);
v_a_2286_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2205_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2205_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_discharge_x3f_2186_);
lean_dec(v___x_2184_);
lean_dec_ref(v___x_2181_);
lean_dec(v_usingArg_2179_);
lean_dec_ref(v_simprocs_2177_);
lean_dec_ref(v___x_2176_);
lean_dec(v___x_2175_);
v_a_2294_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2203_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2203_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v___x_2304_ = _args[0];
lean_object* v_tk_2305_ = _args[1];
lean_object* v___x_2306_ = _args[2];
lean_object* v___x_2307_ = _args[3];
lean_object* v___x_2308_ = _args[4];
lean_object* v_simprocs_2309_ = _args[5];
lean_object* v___x_2310_ = _args[6];
lean_object* v_usingArg_2311_ = _args[7];
lean_object* v___x_2312_ = _args[8];
lean_object* v___x_2313_ = _args[9];
lean_object* v_useReducible_2314_ = _args[10];
lean_object* v___x_2315_ = _args[11];
lean_object* v___x_2316_ = _args[12];
lean_object* v_usingTk_x3f_2317_ = _args[13];
lean_object* v_discharge_x3f_2318_ = _args[14];
lean_object* v___y_2319_ = _args[15];
lean_object* v___y_2320_ = _args[16];
lean_object* v___y_2321_ = _args[17];
lean_object* v___y_2322_ = _args[18];
lean_object* v___y_2323_ = _args[19];
lean_object* v___y_2324_ = _args[20];
lean_object* v___y_2325_ = _args[21];
lean_object* v___y_2326_ = _args[22];
lean_object* v___y_2327_ = _args[23];
_start:
{
uint8_t v___x_97433__boxed_2328_; uint8_t v___x_97434__boxed_2329_; uint8_t v_useReducible_boxed_2330_; uint8_t v___x_97436__boxed_2331_; lean_object* v_res_2332_; 
v___x_97433__boxed_2328_ = lean_unbox(v___x_2310_);
v___x_97434__boxed_2329_ = lean_unbox(v___x_2312_);
v_useReducible_boxed_2330_ = lean_unbox(v_useReducible_2314_);
v___x_97436__boxed_2331_ = lean_unbox(v___x_2315_);
v_res_2332_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2304_, v_tk_2305_, v___x_2306_, v___x_2307_, v___x_2308_, v_simprocs_2309_, v___x_97433__boxed_2328_, v_usingArg_2311_, v___x_97434__boxed_2329_, v___x_2313_, v_useReducible_boxed_2330_, v___x_97436__boxed_2331_, v___x_2316_, v_usingTk_x3f_2317_, v_discharge_x3f_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___x_2304_);
return v_res_2332_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2341_ = lean_unsigned_to_nat(38u);
v___x_2342_ = lean_unsigned_to_nat(130u);
v___x_2343_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2345_ = l_mkPanicMessageWithDecl(v___x_2344_, v___x_2343_, v___x_2342_, v___x_2341_, v___x_2340_);
return v___x_2345_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Array_mkArray0(lean_box(0));
return v___x_2350_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2363_ = lean_unsigned_to_nat(15u);
v___x_2364_ = lean_unsigned_to_nat(131u);
v___x_2365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2367_ = l_mkPanicMessageWithDecl(v___x_2366_, v___x_2365_, v___x_2364_, v___x_2363_, v___x_2362_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2369_, lean_object* v___x_2370_, lean_object* v___x_2371_, lean_object* v___x_2372_, lean_object* v___x_2373_, uint8_t v___x_2374_, lean_object* v___x_2375_, lean_object* v___x_2376_, uint8_t v_useReducible_2377_, lean_object* v___f_2378_, lean_object* v___x_2379_, lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v___x_2382_, lean_object* v___x_2383_, lean_object* v___x_2384_, lean_object* v_usingArg_2385_, lean_object* v___x_2386_, uint8_t v___x_2387_, lean_object* v_usingTk_x3f_2388_, lean_object* v_squeeze_2389_, lean_object* v_unfold_2390_, lean_object* v_args_2391_, lean_object* v_only_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___y_2404_; lean_object* v___y_2408_; lean_object* v_stx_2409_; lean_object* v___y_2410_; lean_object* v_ref_2411_; lean_object* v___y_2412_; lean_object* v___y_2431_; lean_object* v_stx_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v_options_2457_; lean_object* v_ref_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2867_; lean_object* v___y_2868_; uint8_t v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v_args_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2908_; uint8_t v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v_only_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; uint8_t v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; uint8_t v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; uint8_t v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3020_; uint8_t v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3092_; 
v_options_2457_ = lean_ctor_get(v___y_2400_, 2);
v_ref_2458_ = lean_ctor_get(v___y_2400_, 5);
v___x_2459_ = 0;
v___x_2460_ = l_Lean_SourceInfo_fromRef(v_ref_2458_, v___x_2459_);
v___x_2461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7));
lean_inc_ref(v___x_2372_);
lean_inc_ref(v___x_2371_);
lean_inc_ref(v___x_2370_);
v___x_2462_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2461_);
lean_inc(v___x_2460_);
v___x_2463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2460_);
lean_ctor_set(v___x_2463_, 1, v___x_2461_);
v___x_2464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_2465_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_2393_) == 0)
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_3092_ = v___x_3101_;
goto v___jp_3091_;
}
else
{
lean_object* v_val_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_val_3102_ = lean_ctor_get(v___y_2393_, 0);
lean_inc(v_val_3102_);
lean_dec_ref_known(v___y_2393_, 1);
v___x_3103_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_3104_ = lean_array_push(v___x_3103_, v_val_3102_);
v___y_3092_ = v___x_3104_;
goto v___jp_3091_;
}
v___jp_2403_:
{
lean_object* v_diag_2405_; lean_object* v___x_2406_; 
v_diag_2405_ = lean_ctor_get(v___y_2404_, 1);
lean_inc_ref(v_diag_2405_);
lean_dec_ref(v___y_2404_);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v_diag_2405_);
return v___x_2406_;
}
v___jp_2407_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1));
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v_stx_2409_);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
lean_ctor_set(v___x_2416_, 2, v___x_2415_);
lean_ctor_set(v___x_2416_, 3, v___x_2415_);
lean_ctor_set(v___x_2416_, 4, v___x_2415_);
lean_ctor_set(v___x_2416_, 5, v___x_2415_);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_ref_2411_);
v___x_2418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2));
v___x_2419_ = 4;
v___x_2420_ = l_Lean_MessageData_nil;
v___x_2421_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2369_, v___x_2416_, v___x_2417_, v___x_2418_, v___x_2415_, v___x_2419_, v___x_2420_, v___y_2410_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2410_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_dec_ref_known(v___x_2421_, 1);
v___y_2404_ = v___y_2408_;
goto v___jp_2403_;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v___y_2408_);
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
v___jp_2430_:
{
lean_object* v_ref_2435_; 
v_ref_2435_ = lean_ctor_get(v___y_2433_, 5);
lean_inc(v_ref_2435_);
v___y_2408_ = v___y_2431_;
v_stx_2409_ = v_stx_2432_;
v___y_2410_ = v___y_2433_;
v_ref_2411_ = v_ref_2435_;
v___y_2412_ = v___y_2434_;
goto v___jp_2407_;
}
v___jp_2436_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
v___x_2447_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2446_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___y_2431_ = v___y_2437_;
v_stx_2432_ = v_a_2448_;
v___y_2433_ = v___y_2444_;
v___y_2434_ = v___y_2445_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2437_);
lean_dec(v_tk_2369_);
v_a_2449_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2447_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2447_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
v___jp_2466_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2478_ = l_Array_append___redArg(v___x_2465_, v___y_2477_);
lean_dec_ref(v___y_2477_);
lean_inc_n(v___y_2473_, 2);
v___x_2479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2479_, 0, v___y_2473_);
lean_ctor_set(v___x_2479_, 1, v___x_2464_);
lean_ctor_set(v___x_2479_, 2, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node5(v___y_2473_, v___x_2375_, v___y_2470_, v___y_2467_, v___y_2469_, v___y_2476_, v___x_2479_);
v___x_2481_ = l_Lean_Syntax_node2(v___y_2473_, v___y_2475_, v___y_2471_, v___x_2480_);
v___y_2431_ = v___y_2474_;
v_stx_2432_ = v___x_2481_;
v___y_2433_ = v___y_2468_;
v___y_2434_ = v___y_2472_;
goto v___jp_2430_;
}
v___jp_2482_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = l_Array_append___redArg(v___x_2465_, v___y_2493_);
lean_dec_ref(v___y_2493_);
lean_inc(v___y_2490_);
v___x_2495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2495_, 0, v___y_2490_);
lean_ctor_set(v___x_2495_, 1, v___x_2464_);
lean_ctor_set(v___x_2495_, 2, v___x_2494_);
if (lean_obj_tag(v___y_2487_) == 1)
{
lean_object* v_val_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v___x_2373_);
v_val_2496_ = lean_ctor_get(v___y_2487_, 0);
lean_inc(v_val_2496_);
lean_dec_ref_known(v___y_2487_, 1);
v___x_2497_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2490_);
v___x_2498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___y_2490_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = l_Array_mkArray2___redArg(v___x_2498_, v_val_2496_);
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2485_;
v___y_2469_ = v___y_2484_;
v___y_2470_ = v___y_2486_;
v___y_2471_ = v___y_2488_;
v___y_2472_ = v___y_2489_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2491_;
v___y_2475_ = v___y_2492_;
v___y_2476_ = v___x_2495_;
v___y_2477_ = v___x_2499_;
goto v___jp_2466_;
}
else
{
lean_object* v___x_2500_; 
lean_dec(v___y_2487_);
v___x_2500_ = lean_mk_empty_array_with_capacity(v___x_2373_);
lean_dec(v___x_2373_);
v___y_2467_ = v___y_2483_;
v___y_2468_ = v___y_2485_;
v___y_2469_ = v___y_2484_;
v___y_2470_ = v___y_2486_;
v___y_2471_ = v___y_2488_;
v___y_2472_ = v___y_2489_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2491_;
v___y_2475_ = v___y_2492_;
v___y_2476_ = v___x_2495_;
v___y_2477_ = v___x_2500_;
goto v___jp_2466_;
}
}
v___jp_2501_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = l_Array_append___redArg(v___x_2465_, v___y_2512_);
lean_dec_ref(v___y_2512_);
lean_inc(v___y_2509_);
v___x_2514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2514_, 0, v___y_2509_);
lean_ctor_set(v___x_2514_, 1, v___x_2464_);
lean_ctor_set(v___x_2514_, 2, v___x_2513_);
if (lean_obj_tag(v___y_2505_) == 1)
{
lean_object* v_val_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_val_2515_ = lean_ctor_get(v___y_2505_, 0);
lean_inc(v_val_2515_);
lean_dec_ref_known(v___y_2505_, 1);
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2517_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2516_);
v___x_2518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2509_, 4);
v___x_2519_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___y_2509_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = l_Array_append___redArg(v___x_2465_, v_val_2515_);
lean_dec(v_val_2515_);
v___x_2521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2521_, 0, v___y_2509_);
lean_ctor_set(v___x_2521_, 1, v___x_2464_);
lean_ctor_set(v___x_2521_, 2, v___x_2520_);
v___x_2522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___y_2509_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = l_Lean_Syntax_node3(v___y_2509_, v___x_2517_, v___x_2519_, v___x_2521_, v___x_2523_);
v___x_2525_ = l_Array_mkArray1___redArg(v___x_2524_);
v___y_2483_ = v___y_2502_;
v___y_2484_ = v___x_2514_;
v___y_2485_ = v___y_2503_;
v___y_2486_ = v___y_2504_;
v___y_2487_ = v___y_2507_;
v___y_2488_ = v___y_2506_;
v___y_2489_ = v___y_2508_;
v___y_2490_ = v___y_2509_;
v___y_2491_ = v___y_2510_;
v___y_2492_ = v___y_2511_;
v___y_2493_ = v___x_2525_;
goto v___jp_2482_;
}
else
{
lean_object* v___x_2526_; 
lean_dec(v___y_2505_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2526_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2483_ = v___y_2502_;
v___y_2484_ = v___x_2514_;
v___y_2485_ = v___y_2503_;
v___y_2486_ = v___y_2504_;
v___y_2487_ = v___y_2507_;
v___y_2488_ = v___y_2506_;
v___y_2489_ = v___y_2508_;
v___y_2490_ = v___y_2509_;
v___y_2491_ = v___y_2510_;
v___y_2492_ = v___y_2511_;
v___y_2493_ = v___x_2526_;
goto v___jp_2482_;
}
}
v___jp_2527_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = l_Array_append___redArg(v___x_2465_, v___y_2538_);
lean_dec_ref(v___y_2538_);
lean_inc(v___y_2534_);
v___x_2540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2540_, 0, v___y_2534_);
lean_ctor_set(v___x_2540_, 1, v___x_2464_);
lean_ctor_set(v___x_2540_, 2, v___x_2539_);
if (lean_obj_tag(v___y_2536_) == 1)
{
lean_object* v_val_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v_val_2541_ = lean_ctor_get(v___y_2536_, 0);
lean_inc(v_val_2541_);
lean_dec_ref_known(v___y_2536_, 1);
v___x_2542_ = l_Lean_SourceInfo_fromRef(v_val_2541_, v___x_2374_);
lean_dec(v_val_2541_);
v___x_2543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2542_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Array_mkArray1___redArg(v___x_2544_);
v___y_2502_ = v___x_2540_;
v___y_2503_ = v___y_2528_;
v___y_2504_ = v___y_2529_;
v___y_2505_ = v___y_2530_;
v___y_2506_ = v___y_2532_;
v___y_2507_ = v___y_2531_;
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
v___y_2510_ = v___y_2535_;
v___y_2511_ = v___y_2537_;
v___y_2512_ = v___x_2545_;
goto v___jp_2501_;
}
else
{
lean_object* v___x_2546_; 
lean_dec(v___y_2536_);
v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2502_ = v___x_2540_;
v___y_2503_ = v___y_2528_;
v___y_2504_ = v___y_2529_;
v___y_2505_ = v___y_2530_;
v___y_2506_ = v___y_2532_;
v___y_2507_ = v___y_2531_;
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
v___y_2510_ = v___y_2535_;
v___y_2511_ = v___y_2537_;
v___y_2512_ = v___x_2546_;
goto v___jp_2501_;
}
}
v___jp_2547_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2562_ = l_Array_append___redArg(v___x_2465_, v___y_2561_);
lean_dec_ref(v___y_2561_);
lean_inc_n(v___y_2550_, 3);
v___x_2563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2563_, 0, v___y_2550_);
lean_ctor_set(v___x_2563_, 1, v___x_2464_);
lean_ctor_set(v___x_2563_, 2, v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___y_2550_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = l_Lean_Syntax_node6(v___y_2550_, v___y_2555_, v___y_2556_, v___y_2559_, v___y_2551_, v___x_2563_, v___x_2565_, v___y_2549_);
v___x_2567_ = l_Lean_Syntax_node4(v___y_2550_, v___y_2557_, v___y_2552_, v___y_2560_, v___y_2558_, v___x_2566_);
v___y_2431_ = v___y_2554_;
v_stx_2432_ = v___x_2567_;
v___y_2433_ = v___y_2548_;
v___y_2434_ = v___y_2553_;
goto v___jp_2430_;
}
v___jp_2568_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = l_Array_append___redArg(v___x_2465_, v___y_2582_);
lean_dec_ref(v___y_2582_);
lean_inc(v___y_2571_);
v___x_2584_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2584_, 0, v___y_2571_);
lean_ctor_set(v___x_2584_, 1, v___x_2464_);
lean_ctor_set(v___x_2584_, 2, v___x_2583_);
if (lean_obj_tag(v___y_2578_) == 1)
{
lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec(v___x_2373_);
v_val_2585_ = lean_ctor_get(v___y_2578_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v___y_2578_, 1);
v___x_2586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2587_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2586_);
v___x_2588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2571_, 4);
v___x_2589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___y_2571_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = l_Array_append___redArg(v___x_2465_, v_val_2585_);
lean_dec(v_val_2585_);
v___x_2591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___y_2571_);
lean_ctor_set(v___x_2591_, 1, v___x_2464_);
lean_ctor_set(v___x_2591_, 2, v___x_2590_);
v___x_2592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___y_2571_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = l_Lean_Syntax_node3(v___y_2571_, v___x_2587_, v___x_2589_, v___x_2591_, v___x_2593_);
v___x_2595_ = l_Array_mkArray1___redArg(v___x_2594_);
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___x_2584_;
v___y_2552_ = v___y_2572_;
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___y_2574_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2576_;
v___y_2557_ = v___y_2577_;
v___y_2558_ = v___y_2579_;
v___y_2559_ = v___y_2580_;
v___y_2560_ = v___y_2581_;
v___y_2561_ = v___x_2595_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2596_; 
lean_dec(v___y_2578_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2596_ = lean_mk_empty_array_with_capacity(v___x_2373_);
lean_dec(v___x_2373_);
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___x_2584_;
v___y_2552_ = v___y_2572_;
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___y_2574_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2576_;
v___y_2557_ = v___y_2577_;
v___y_2558_ = v___y_2579_;
v___y_2559_ = v___y_2580_;
v___y_2560_ = v___y_2581_;
v___y_2561_ = v___x_2596_;
goto v___jp_2547_;
}
}
v___jp_2597_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = l_Array_append___redArg(v___x_2465_, v___y_2611_);
lean_dec_ref(v___y_2611_);
lean_inc(v___y_2600_);
v___x_2613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2613_, 0, v___y_2600_);
lean_ctor_set(v___x_2613_, 1, v___x_2464_);
lean_ctor_set(v___x_2613_, 2, v___x_2612_);
if (lean_obj_tag(v___y_2604_) == 1)
{
lean_object* v_val_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_val_2614_ = lean_ctor_get(v___y_2604_, 0);
lean_inc(v_val_2614_);
lean_dec_ref_known(v___y_2604_, 1);
v___x_2615_ = l_Lean_SourceInfo_fromRef(v_val_2614_, v___x_2374_);
lean_dec(v_val_2614_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = l_Array_mkArray1___redArg(v___x_2617_);
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2599_;
v___y_2571_ = v___y_2600_;
v___y_2572_ = v___y_2601_;
v___y_2573_ = v___y_2602_;
v___y_2574_ = v___y_2603_;
v___y_2575_ = v___y_2605_;
v___y_2576_ = v___y_2606_;
v___y_2577_ = v___y_2607_;
v___y_2578_ = v___y_2608_;
v___y_2579_ = v___y_2609_;
v___y_2580_ = v___x_2613_;
v___y_2581_ = v___y_2610_;
v___y_2582_ = v___x_2618_;
goto v___jp_2568_;
}
else
{
lean_object* v___x_2619_; 
lean_dec(v___y_2604_);
v___x_2619_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2599_;
v___y_2571_ = v___y_2600_;
v___y_2572_ = v___y_2601_;
v___y_2573_ = v___y_2602_;
v___y_2574_ = v___y_2603_;
v___y_2575_ = v___y_2605_;
v___y_2576_ = v___y_2606_;
v___y_2577_ = v___y_2607_;
v___y_2578_ = v___y_2608_;
v___y_2579_ = v___y_2609_;
v___y_2580_ = v___x_2613_;
v___y_2581_ = v___y_2610_;
v___y_2582_ = v___x_2619_;
goto v___jp_2568_;
}
}
v___jp_2620_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2632_ = l_Array_append___redArg(v___x_2465_, v___y_2631_);
lean_dec_ref(v___y_2631_);
lean_inc_n(v___y_2621_, 2);
v___x_2633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2633_, 0, v___y_2621_);
lean_ctor_set(v___x_2633_, 1, v___x_2464_);
lean_ctor_set(v___x_2633_, 2, v___x_2632_);
v___x_2634_ = l_Lean_Syntax_node5(v___y_2621_, v___x_2375_, v___y_2625_, v___y_2629_, v___y_2624_, v___y_2630_, v___x_2633_);
lean_inc(v___y_2623_);
v___x_2635_ = l_Lean_Syntax_node4(v___y_2621_, v___x_2376_, v___y_2628_, v___y_2623_, v___y_2623_, v___x_2634_);
v___y_2431_ = v___y_2627_;
v_stx_2432_ = v___x_2635_;
v___y_2433_ = v___y_2622_;
v___y_2434_ = v___y_2626_;
goto v___jp_2430_;
}
v___jp_2636_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = l_Array_append___redArg(v___x_2465_, v___y_2647_);
lean_dec_ref(v___y_2647_);
lean_inc(v___y_2637_);
v___x_2649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2649_, 0, v___y_2637_);
lean_ctor_set(v___x_2649_, 1, v___x_2464_);
lean_ctor_set(v___x_2649_, 2, v___x_2648_);
if (lean_obj_tag(v___y_2642_) == 1)
{
lean_object* v_val_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec(v___x_2373_);
v_val_2650_ = lean_ctor_get(v___y_2642_, 0);
lean_inc(v_val_2650_);
lean_dec_ref_known(v___y_2642_, 1);
v___x_2651_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2637_);
v___x_2652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___y_2637_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = l_Array_mkArray2___redArg(v___x_2652_, v_val_2650_);
v___y_2621_ = v___y_2637_;
v___y_2622_ = v___y_2638_;
v___y_2623_ = v___y_2640_;
v___y_2624_ = v___y_2639_;
v___y_2625_ = v___y_2641_;
v___y_2626_ = v___y_2643_;
v___y_2627_ = v___y_2645_;
v___y_2628_ = v___y_2644_;
v___y_2629_ = v___y_2646_;
v___y_2630_ = v___x_2649_;
v___y_2631_ = v___x_2653_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2654_; 
lean_dec(v___y_2642_);
v___x_2654_ = lean_mk_empty_array_with_capacity(v___x_2373_);
lean_dec(v___x_2373_);
v___y_2621_ = v___y_2637_;
v___y_2622_ = v___y_2638_;
v___y_2623_ = v___y_2640_;
v___y_2624_ = v___y_2639_;
v___y_2625_ = v___y_2641_;
v___y_2626_ = v___y_2643_;
v___y_2627_ = v___y_2645_;
v___y_2628_ = v___y_2644_;
v___y_2629_ = v___y_2646_;
v___y_2630_ = v___x_2649_;
v___y_2631_ = v___x_2654_;
goto v___jp_2620_;
}
}
v___jp_2655_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = l_Array_append___redArg(v___x_2465_, v___y_2666_);
lean_dec_ref(v___y_2666_);
lean_inc(v___y_2656_);
v___x_2668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2668_, 0, v___y_2656_);
lean_ctor_set(v___x_2668_, 1, v___x_2464_);
lean_ctor_set(v___x_2668_, 2, v___x_2667_);
if (lean_obj_tag(v___y_2660_) == 1)
{
lean_object* v_val_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_val_2669_ = lean_ctor_get(v___y_2660_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v___y_2660_, 1);
v___x_2670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2671_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2670_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2656_, 4);
v___x_2673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___y_2656_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Array_append___redArg(v___x_2465_, v_val_2669_);
lean_dec(v_val_2669_);
v___x_2675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2675_, 0, v___y_2656_);
lean_ctor_set(v___x_2675_, 1, v___x_2464_);
lean_ctor_set(v___x_2675_, 2, v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2677_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___y_2656_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = l_Lean_Syntax_node3(v___y_2656_, v___x_2671_, v___x_2673_, v___x_2675_, v___x_2677_);
v___x_2679_ = l_Array_mkArray1___redArg(v___x_2678_);
v___y_2637_ = v___y_2656_;
v___y_2638_ = v___y_2657_;
v___y_2639_ = v___x_2668_;
v___y_2640_ = v___y_2658_;
v___y_2641_ = v___y_2659_;
v___y_2642_ = v___y_2661_;
v___y_2643_ = v___y_2662_;
v___y_2644_ = v___y_2664_;
v___y_2645_ = v___y_2663_;
v___y_2646_ = v___y_2665_;
v___y_2647_ = v___x_2679_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2680_; 
lean_dec(v___y_2660_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2680_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2637_ = v___y_2656_;
v___y_2638_ = v___y_2657_;
v___y_2639_ = v___x_2668_;
v___y_2640_ = v___y_2658_;
v___y_2641_ = v___y_2659_;
v___y_2642_ = v___y_2661_;
v___y_2643_ = v___y_2662_;
v___y_2644_ = v___y_2664_;
v___y_2645_ = v___y_2663_;
v___y_2646_ = v___y_2665_;
v___y_2647_ = v___x_2680_;
goto v___jp_2636_;
}
}
v___jp_2681_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = l_Array_append___redArg(v___x_2465_, v___y_2692_);
lean_dec_ref(v___y_2692_);
lean_inc(v___y_2682_);
v___x_2694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2694_, 0, v___y_2682_);
lean_ctor_set(v___x_2694_, 1, v___x_2464_);
lean_ctor_set(v___x_2694_, 2, v___x_2693_);
if (lean_obj_tag(v___y_2691_) == 1)
{
lean_object* v_val_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v_val_2695_ = lean_ctor_get(v___y_2691_, 0);
lean_inc(v_val_2695_);
lean_dec_ref_known(v___y_2691_, 1);
v___x_2696_ = l_Lean_SourceInfo_fromRef(v_val_2695_, v___x_2374_);
lean_dec(v_val_2695_);
v___x_2697_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_Array_mkArray1___redArg(v___x_2698_);
v___y_2656_ = v___y_2682_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2684_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2686_;
v___y_2661_ = v___y_2687_;
v___y_2662_ = v___y_2688_;
v___y_2663_ = v___y_2690_;
v___y_2664_ = v___y_2689_;
v___y_2665_ = v___x_2694_;
v___y_2666_ = v___x_2699_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2700_; 
lean_dec(v___y_2691_);
v___x_2700_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2656_ = v___y_2682_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2684_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2686_;
v___y_2661_ = v___y_2687_;
v___y_2662_ = v___y_2688_;
v___y_2663_ = v___y_2690_;
v___y_2664_ = v___y_2689_;
v___y_2665_ = v___x_2694_;
v___y_2666_ = v___x_2700_;
goto v___jp_2655_;
}
}
v___jp_2701_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2715_ = l_Array_append___redArg(v___x_2465_, v___y_2714_);
lean_dec_ref(v___y_2714_);
lean_inc_n(v___y_2709_, 3);
v___x_2716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2716_, 0, v___y_2709_);
lean_ctor_set(v___x_2716_, 1, v___x_2464_);
lean_ctor_set(v___x_2716_, 2, v___x_2715_);
v___x_2717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___y_2709_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = l_Lean_Syntax_node6(v___y_2709_, v___y_2704_, v___y_2710_, v___y_2712_, v___y_2705_, v___x_2716_, v___x_2718_, v___y_2713_);
lean_inc(v___y_2708_);
v___x_2720_ = l_Lean_Syntax_node4(v___y_2709_, v___y_2711_, v___y_2703_, v___y_2708_, v___y_2708_, v___x_2719_);
v___y_2431_ = v___y_2707_;
v_stx_2432_ = v___x_2720_;
v___y_2433_ = v___y_2702_;
v___y_2434_ = v___y_2706_;
goto v___jp_2430_;
}
v___jp_2721_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = l_Array_append___redArg(v___x_2465_, v___y_2734_);
lean_dec_ref(v___y_2734_);
lean_inc(v___y_2728_);
v___x_2736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2736_, 0, v___y_2728_);
lean_ctor_set(v___x_2736_, 1, v___x_2464_);
lean_ctor_set(v___x_2736_, 2, v___x_2735_);
if (lean_obj_tag(v___y_2730_) == 1)
{
lean_object* v_val_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_dec(v___x_2373_);
v_val_2737_ = lean_ctor_get(v___y_2730_, 0);
lean_inc(v_val_2737_);
lean_dec_ref_known(v___y_2730_, 1);
v___x_2738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2739_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2738_);
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2728_, 4);
v___x_2741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___y_2728_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l_Array_append___redArg(v___x_2465_, v_val_2737_);
lean_dec(v_val_2737_);
v___x_2743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2743_, 0, v___y_2728_);
lean_ctor_set(v___x_2743_, 1, v___x_2464_);
lean_ctor_set(v___x_2743_, 2, v___x_2742_);
v___x_2744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___y_2728_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = l_Lean_Syntax_node3(v___y_2728_, v___x_2739_, v___x_2741_, v___x_2743_, v___x_2745_);
v___x_2747_ = l_Array_mkArray1___redArg(v___x_2746_);
v___y_2702_ = v___y_2722_;
v___y_2703_ = v___y_2723_;
v___y_2704_ = v___y_2724_;
v___y_2705_ = v___x_2736_;
v___y_2706_ = v___y_2725_;
v___y_2707_ = v___y_2726_;
v___y_2708_ = v___y_2727_;
v___y_2709_ = v___y_2728_;
v___y_2710_ = v___y_2729_;
v___y_2711_ = v___y_2731_;
v___y_2712_ = v___y_2732_;
v___y_2713_ = v___y_2733_;
v___y_2714_ = v___x_2747_;
goto v___jp_2701_;
}
else
{
lean_object* v___x_2748_; 
lean_dec(v___y_2730_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2748_ = lean_mk_empty_array_with_capacity(v___x_2373_);
lean_dec(v___x_2373_);
v___y_2702_ = v___y_2722_;
v___y_2703_ = v___y_2723_;
v___y_2704_ = v___y_2724_;
v___y_2705_ = v___x_2736_;
v___y_2706_ = v___y_2725_;
v___y_2707_ = v___y_2726_;
v___y_2708_ = v___y_2727_;
v___y_2709_ = v___y_2728_;
v___y_2710_ = v___y_2729_;
v___y_2711_ = v___y_2731_;
v___y_2712_ = v___y_2732_;
v___y_2713_ = v___y_2733_;
v___y_2714_ = v___x_2748_;
goto v___jp_2701_;
}
}
v___jp_2749_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = l_Array_append___redArg(v___x_2465_, v___y_2762_);
lean_dec_ref(v___y_2762_);
lean_inc(v___y_2757_);
v___x_2764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2764_, 0, v___y_2757_);
lean_ctor_set(v___x_2764_, 1, v___x_2464_);
lean_ctor_set(v___x_2764_, 2, v___x_2763_);
if (lean_obj_tag(v___y_2755_) == 1)
{
lean_object* v_val_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_val_2765_ = lean_ctor_get(v___y_2755_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v___y_2755_, 1);
v___x_2766_ = l_Lean_SourceInfo_fromRef(v_val_2765_, v___x_2374_);
lean_dec(v_val_2765_);
v___x_2767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_Array_mkArray1___redArg(v___x_2768_);
v___y_2722_ = v___y_2750_;
v___y_2723_ = v___y_2751_;
v___y_2724_ = v___y_2752_;
v___y_2725_ = v___y_2753_;
v___y_2726_ = v___y_2754_;
v___y_2727_ = v___y_2756_;
v___y_2728_ = v___y_2757_;
v___y_2729_ = v___y_2758_;
v___y_2730_ = v___y_2759_;
v___y_2731_ = v___y_2760_;
v___y_2732_ = v___x_2764_;
v___y_2733_ = v___y_2761_;
v___y_2734_ = v___x_2769_;
goto v___jp_2721_;
}
else
{
lean_object* v___x_2770_; 
lean_dec(v___y_2755_);
v___x_2770_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2722_ = v___y_2750_;
v___y_2723_ = v___y_2751_;
v___y_2724_ = v___y_2752_;
v___y_2725_ = v___y_2753_;
v___y_2726_ = v___y_2754_;
v___y_2727_ = v___y_2756_;
v___y_2728_ = v___y_2757_;
v___y_2729_ = v___y_2758_;
v___y_2730_ = v___y_2759_;
v___y_2731_ = v___y_2760_;
v___y_2732_ = v___x_2764_;
v___y_2733_ = v___y_2761_;
v___y_2734_ = v___x_2770_;
goto v___jp_2721_;
}
}
v___jp_2771_:
{
if (v___y_2781_ == 0)
{
if (v_useReducible_2377_ == 0)
{
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
if (lean_obj_tag(v___y_2782_) == 0)
{
lean_dec(v___y_2786_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2776_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___y_2437_ = v___y_2774_;
v___y_2438_ = v___y_2780_;
v___y_2439_ = v___y_2783_;
v___y_2440_ = v___y_2777_;
v___y_2441_ = v___y_2784_;
v___y_2442_ = v___y_2775_;
v___y_2443_ = v___y_2785_;
v___y_2444_ = v___y_2772_;
v___y_2445_ = v___y_2773_;
goto v___jp_2436_;
}
else
{
lean_object* v_val_2787_; lean_object* v___x_2788_; 
v_val_2787_ = lean_ctor_get(v___y_2782_, 0);
lean_inc(v_val_2787_);
lean_dec_ref_known(v___y_2782_, 1);
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
v___x_2788_ = lean_apply_9(v___f_2378_, v___y_2780_, v___y_2783_, v___y_2777_, v___y_2784_, v___y_2775_, v___y_2785_, v___y_2772_, v___y_2773_, lean_box(0));
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_n(v_a_2789_, 3);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2372_, 2);
lean_inc_ref_n(v___x_2371_, 2);
lean_inc_ref_n(v___x_2370_, 2);
v___x_2791_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2790_);
v___x_2792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_a_2789_);
lean_ctor_set(v___x_2792_, 1, v___x_2379_);
v___x_2793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2793_, 0, v_a_2789_);
lean_ctor_set(v___x_2793_, 1, v___x_2464_);
lean_ctor_set(v___x_2793_, 2, v___x_2465_);
v___x_2794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2795_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2794_);
if (lean_obj_tag(v___y_2786_) == 0)
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2750_ = v___y_2772_;
v___y_2751_ = v___x_2792_;
v___y_2752_ = v___x_2795_;
v___y_2753_ = v___y_2773_;
v___y_2754_ = v___y_2774_;
v___y_2755_ = v___y_2776_;
v___y_2756_ = v___x_2793_;
v___y_2757_ = v_a_2789_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___x_2791_;
v___y_2761_ = v_val_2787_;
v___y_2762_ = v___x_2796_;
goto v___jp_2749_;
}
else
{
lean_object* v_val_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_val_2797_ = lean_ctor_get(v___y_2786_, 0);
lean_inc(v_val_2797_);
lean_dec_ref_known(v___y_2786_, 1);
v___x_2798_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_2799_ = lean_array_push(v___x_2798_, v_val_2797_);
v___y_2750_ = v___y_2772_;
v___y_2751_ = v___x_2792_;
v___y_2752_ = v___x_2795_;
v___y_2753_ = v___y_2773_;
v___y_2754_ = v___y_2774_;
v___y_2755_ = v___y_2776_;
v___y_2756_ = v___x_2793_;
v___y_2757_ = v_a_2789_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___y_2779_;
v___y_2760_ = v___x_2791_;
v___y_2761_ = v_val_2787_;
v___y_2762_ = v___x_2799_;
goto v___jp_2749_;
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_val_2787_);
lean_dec(v___y_2786_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec_ref(v___x_2379_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v_a_2800_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2788_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2788_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
else
{
lean_object* v___x_2808_; 
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
v___x_2808_ = lean_apply_9(v___f_2378_, v___y_2780_, v___y_2783_, v___y_2777_, v___y_2784_, v___y_2775_, v___y_2785_, v___y_2772_, v___y_2773_, lean_box(0));
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_n(v_a_2809_, 3);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2810_, 0, v_a_2809_);
lean_ctor_set(v___x_2810_, 1, v___x_2379_);
v___x_2811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2464_);
lean_ctor_set(v___x_2811_, 2, v___x_2465_);
if (lean_obj_tag(v___y_2786_) == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2682_ = v_a_2809_;
v___y_2683_ = v___y_2772_;
v___y_2684_ = v___x_2811_;
v___y_2685_ = v___y_2778_;
v___y_2686_ = v___y_2779_;
v___y_2687_ = v___y_2782_;
v___y_2688_ = v___y_2773_;
v___y_2689_ = v___x_2810_;
v___y_2690_ = v___y_2774_;
v___y_2691_ = v___y_2776_;
v___y_2692_ = v___x_2812_;
goto v___jp_2681_;
}
else
{
lean_object* v_val_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_val_2813_ = lean_ctor_get(v___y_2786_, 0);
lean_inc(v_val_2813_);
lean_dec_ref_known(v___y_2786_, 1);
v___x_2814_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_2815_ = lean_array_push(v___x_2814_, v_val_2813_);
v___y_2682_ = v_a_2809_;
v___y_2683_ = v___y_2772_;
v___y_2684_ = v___x_2811_;
v___y_2685_ = v___y_2778_;
v___y_2686_ = v___y_2779_;
v___y_2687_ = v___y_2782_;
v___y_2688_ = v___y_2773_;
v___y_2689_ = v___x_2810_;
v___y_2690_ = v___y_2774_;
v___y_2691_ = v___y_2776_;
v___y_2692_ = v___x_2815_;
goto v___jp_2681_;
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v___y_2786_);
lean_dec(v___y_2782_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec_ref(v___x_2379_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v_a_2816_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2808_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2808_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
else
{
lean_dec(v___x_2376_);
if (v_useReducible_2377_ == 0)
{
lean_dec(v___x_2375_);
if (lean_obj_tag(v___y_2782_) == 0)
{
lean_dec(v___y_2786_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2776_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___y_2437_ = v___y_2774_;
v___y_2438_ = v___y_2780_;
v___y_2439_ = v___y_2783_;
v___y_2440_ = v___y_2777_;
v___y_2441_ = v___y_2784_;
v___y_2442_ = v___y_2775_;
v___y_2443_ = v___y_2785_;
v___y_2444_ = v___y_2772_;
v___y_2445_ = v___y_2773_;
goto v___jp_2436_;
}
else
{
lean_object* v_val_2824_; lean_object* v___x_2825_; 
v_val_2824_ = lean_ctor_get(v___y_2782_, 0);
lean_inc(v_val_2824_);
lean_dec_ref_known(v___y_2782_, 1);
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
v___x_2825_ = lean_apply_9(v___f_2378_, v___y_2780_, v___y_2783_, v___y_2777_, v___y_2784_, v___y_2775_, v___y_2785_, v___y_2772_, v___y_2773_, lean_box(0));
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_n(v_a_2826_, 5);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2372_, 2);
lean_inc_ref_n(v___x_2371_, 2);
lean_inc_ref_n(v___x_2370_, 2);
v___x_2828_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_a_2826_);
lean_ctor_set(v___x_2829_, 1, v___x_2379_);
v___x_2830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2830_, 0, v_a_2826_);
lean_ctor_set(v___x_2830_, 1, v___x_2464_);
lean_ctor_set(v___x_2830_, 2, v___x_2465_);
v___x_2831_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_2832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2832_, 0, v_a_2826_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = l_Lean_Syntax_node1(v_a_2826_, v___x_2464_, v___x_2832_);
v___x_2834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2835_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2834_);
if (lean_obj_tag(v___y_2786_) == 0)
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2598_ = v___y_2772_;
v___y_2599_ = v_val_2824_;
v___y_2600_ = v_a_2826_;
v___y_2601_ = v___x_2829_;
v___y_2602_ = v___y_2773_;
v___y_2603_ = v___y_2774_;
v___y_2604_ = v___y_2776_;
v___y_2605_ = v___x_2835_;
v___y_2606_ = v___y_2778_;
v___y_2607_ = v___x_2828_;
v___y_2608_ = v___y_2779_;
v___y_2609_ = v___x_2833_;
v___y_2610_ = v___x_2830_;
v___y_2611_ = v___x_2836_;
goto v___jp_2597_;
}
else
{
lean_object* v_val_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_val_2837_ = lean_ctor_get(v___y_2786_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v___y_2786_, 1);
v___x_2838_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_2839_ = lean_array_push(v___x_2838_, v_val_2837_);
v___y_2598_ = v___y_2772_;
v___y_2599_ = v_val_2824_;
v___y_2600_ = v_a_2826_;
v___y_2601_ = v___x_2829_;
v___y_2602_ = v___y_2773_;
v___y_2603_ = v___y_2774_;
v___y_2604_ = v___y_2776_;
v___y_2605_ = v___x_2835_;
v___y_2606_ = v___y_2778_;
v___y_2607_ = v___x_2828_;
v___y_2608_ = v___y_2779_;
v___y_2609_ = v___x_2833_;
v___y_2610_ = v___x_2830_;
v___y_2611_ = v___x_2839_;
goto v___jp_2597_;
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_val_2824_);
lean_dec(v___y_2786_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec_ref(v___x_2379_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v_a_2840_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2825_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2825_);
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
else
{
lean_object* v___x_2848_; 
lean_dec_ref(v___x_2379_);
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
v___x_2848_ = lean_apply_9(v___f_2378_, v___y_2780_, v___y_2783_, v___y_2777_, v___y_2784_, v___y_2775_, v___y_2785_, v___y_2772_, v___y_2773_, lean_box(0));
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc_n(v_a_2849_, 2);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20));
lean_inc_ref(v___x_2372_);
lean_inc_ref(v___x_2371_);
lean_inc_ref(v___x_2370_);
v___x_2851_ = l_Lean_Name_mkStr4(v___x_2370_, v___x_2371_, v___x_2372_, v___x_2850_);
v___x_2852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21));
v___x_2853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2849_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
if (lean_obj_tag(v___y_2786_) == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_2528_ = v___y_2772_;
v___y_2529_ = v___y_2778_;
v___y_2530_ = v___y_2779_;
v___y_2531_ = v___y_2782_;
v___y_2532_ = v___x_2853_;
v___y_2533_ = v___y_2773_;
v___y_2534_ = v_a_2849_;
v___y_2535_ = v___y_2774_;
v___y_2536_ = v___y_2776_;
v___y_2537_ = v___x_2851_;
v___y_2538_ = v___x_2854_;
goto v___jp_2527_;
}
else
{
lean_object* v_val_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_val_2855_ = lean_ctor_get(v___y_2786_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v___y_2786_, 1);
v___x_2856_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_2857_ = lean_array_push(v___x_2856_, v_val_2855_);
v___y_2528_ = v___y_2772_;
v___y_2529_ = v___y_2778_;
v___y_2530_ = v___y_2779_;
v___y_2531_ = v___y_2782_;
v___y_2532_ = v___x_2853_;
v___y_2533_ = v___y_2773_;
v___y_2534_ = v_a_2849_;
v___y_2535_ = v___y_2774_;
v___y_2536_ = v___y_2776_;
v___y_2537_ = v___x_2851_;
v___y_2538_ = v___x_2857_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v___y_2786_);
lean_dec(v___y_2782_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v_a_2858_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2848_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2848_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
v___jp_2866_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2883_ = lean_unsigned_to_nat(5u);
v___x_2884_ = l_Lean_Syntax_getArg(v___y_2873_, v___x_2883_);
lean_dec(v___y_2873_);
v___x_2885_ = l_Lean_Syntax_matchesNull(v___x_2884_, v___x_2373_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec(v_args_2874_);
lean_dec(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2886_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2887_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2886_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___y_2431_ = v___y_2870_;
v_stx_2432_ = v_a_2888_;
v___y_2433_ = v___y_2881_;
v___y_2434_ = v___y_2882_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2870_);
lean_dec(v_tk_2369_);
v_a_2889_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2887_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2887_);
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
else
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Syntax_getOptional_x3f(v___y_2872_);
lean_dec(v___y_2872_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_box(0);
v___y_2772_ = v___y_2881_;
v___y_2773_ = v___y_2882_;
v___y_2774_ = v___y_2870_;
v___y_2775_ = v___y_2879_;
v___y_2776_ = v___y_2871_;
v___y_2777_ = v___y_2877_;
v___y_2778_ = v___y_2867_;
v___y_2779_ = v_args_2874_;
v___y_2780_ = v___y_2875_;
v___y_2781_ = v___y_2869_;
v___y_2782_ = v___y_2868_;
v___y_2783_ = v___y_2876_;
v___y_2784_ = v___y_2878_;
v___y_2785_ = v___y_2880_;
v___y_2786_ = v___x_2898_;
goto v___jp_2771_;
}
else
{
lean_object* v_val_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_val_2899_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2897_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_val_2899_);
lean_dec(v___x_2897_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_val_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
v___y_2772_ = v___y_2881_;
v___y_2773_ = v___y_2882_;
v___y_2774_ = v___y_2870_;
v___y_2775_ = v___y_2879_;
v___y_2776_ = v___y_2871_;
v___y_2777_ = v___y_2877_;
v___y_2778_ = v___y_2867_;
v___y_2779_ = v_args_2874_;
v___y_2780_ = v___y_2875_;
v___y_2781_ = v___y_2869_;
v___y_2782_ = v___y_2868_;
v___y_2783_ = v___y_2876_;
v___y_2784_ = v___y_2878_;
v___y_2785_ = v___y_2880_;
v___y_2786_ = v___x_2904_;
goto v___jp_2771_;
}
}
}
}
}
v___jp_2907_:
{
lean_object* v___x_2923_; uint8_t v___x_2924_; 
v___x_2923_ = l_Lean_Syntax_getArg(v___y_2913_, v___x_2380_);
v___x_2924_ = l_Lean_Syntax_isNone(v___x_2923_);
if (v___x_2924_ == 0)
{
uint8_t v___x_2925_; 
lean_inc(v___x_2923_);
v___x_2925_ = l_Lean_Syntax_matchesNull(v___x_2923_, v___x_2381_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v___x_2923_);
lean_dec(v_only_2914_);
lean_dec(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec(v___y_2910_);
lean_dec(v___y_2908_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2927_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2926_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___y_2431_ = v___y_2911_;
v_stx_2432_ = v_a_2928_;
v___y_2433_ = v___y_2921_;
v___y_2434_ = v___y_2922_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v___y_2911_);
lean_dec(v_tk_2369_);
v_a_2929_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2927_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = l_Lean_Syntax_getArg(v___x_2923_, v___x_2382_);
lean_dec(v___x_2382_);
lean_dec(v___x_2923_);
v___x_2938_ = l_Lean_Syntax_getArgs(v___x_2937_);
lean_dec(v___x_2937_);
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
v___y_2867_ = v___y_2908_;
v___y_2868_ = v___y_2910_;
v___y_2869_ = v___y_2909_;
v___y_2870_ = v___y_2911_;
v___y_2871_ = v_only_2914_;
v___y_2872_ = v___y_2912_;
v___y_2873_ = v___y_2913_;
v_args_2874_ = v___x_2939_;
v___y_2875_ = v___y_2915_;
v___y_2876_ = v___y_2916_;
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2918_;
v___y_2879_ = v___y_2919_;
v___y_2880_ = v___y_2920_;
v___y_2881_ = v___y_2921_;
v___y_2882_ = v___y_2922_;
goto v___jp_2866_;
}
}
else
{
lean_object* v___x_2940_; 
lean_dec(v___x_2923_);
lean_dec(v___x_2382_);
v___x_2940_ = lean_box(0);
v___y_2867_ = v___y_2908_;
v___y_2868_ = v___y_2910_;
v___y_2869_ = v___y_2909_;
v___y_2870_ = v___y_2911_;
v___y_2871_ = v_only_2914_;
v___y_2872_ = v___y_2912_;
v___y_2873_ = v___y_2913_;
v_args_2874_ = v___x_2940_;
v___y_2875_ = v___y_2915_;
v___y_2876_ = v___y_2916_;
v___y_2877_ = v___y_2917_;
v___y_2878_ = v___y_2918_;
v___y_2879_ = v___y_2919_;
v___y_2880_ = v___y_2920_;
v___y_2881_ = v___y_2921_;
v___y_2882_ = v___y_2922_;
goto v___jp_2866_;
}
}
v___jp_2941_:
{
lean_object* v_usedTheorems_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_usedTheorems_2946_ = lean_ctor_get(v___y_2943_, 0);
v___x_2947_ = l_Lean_Syntax_unsetTrailing(v___y_2944_);
v___x_2948_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2947_, v_usedTheorems_2946_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; uint8_t v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc_n(v_a_2949_, 2);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = l_Lean_Syntax_isOfKind(v_a_2949_, v___x_2462_);
lean_dec(v___x_2462_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_inc(v_ref_2458_);
lean_dec(v_a_2949_);
lean_dec(v___y_2945_);
lean_dec(v___x_2384_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2951_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2952_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2951_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___y_2408_ = v___y_2943_;
v_stx_2409_ = v_a_2953_;
v___y_2410_ = v___y_2400_;
v_ref_2411_ = v_ref_2458_;
v___y_2412_ = v___y_2401_;
goto v___jp_2407_;
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v___y_2943_);
lean_dec(v_ref_2458_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_tk_2369_);
v_a_2954_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2952_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2952_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = l_Lean_Syntax_getArg(v_a_2949_, v___x_2382_);
lean_inc(v___x_2962_);
v___x_2963_ = l_Lean_Syntax_isOfKind(v___x_2962_, v___x_2383_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_inc(v_ref_2458_);
lean_dec(v___x_2962_);
lean_dec(v_a_2949_);
lean_dec(v___y_2945_);
lean_dec(v___x_2384_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2964_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2965_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2964_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v___y_2408_ = v___y_2943_;
v_stx_2409_ = v_a_2966_;
v___y_2410_ = v___y_2400_;
v_ref_2411_ = v_ref_2458_;
v___y_2412_ = v___y_2401_;
goto v___jp_2407_;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v___y_2943_);
lean_dec(v_ref_2458_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_tk_2369_);
v_a_2967_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2965_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2965_);
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
else
{
lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2975_ = l_Lean_Syntax_getArg(v_a_2949_, v___x_2384_);
lean_dec(v___x_2384_);
v___x_2976_ = l_Lean_Syntax_getArg(v_a_2949_, v___x_2381_);
v___x_2977_ = l_Lean_Syntax_isNone(v___x_2976_);
if (v___x_2977_ == 0)
{
uint8_t v___x_2978_; 
lean_inc(v___x_2976_);
v___x_2978_ = l_Lean_Syntax_matchesNull(v___x_2976_, v___x_2382_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_inc(v_ref_2458_);
lean_dec(v___x_2976_);
lean_dec(v___x_2975_);
lean_dec(v___x_2962_);
lean_dec(v_a_2949_);
lean_dec(v___y_2945_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
v___x_2979_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2980_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2979_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___y_2408_ = v___y_2943_;
v_stx_2409_ = v_a_2981_;
v___y_2410_ = v___y_2400_;
v_ref_2411_ = v_ref_2458_;
v___y_2412_ = v___y_2401_;
goto v___jp_2407_;
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref(v___y_2943_);
lean_dec(v_ref_2458_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_tk_2369_);
v_a_2982_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2980_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = l_Lean_Syntax_getArg(v___x_2976_, v___x_2373_);
lean_dec(v___x_2976_);
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
v___y_2908_ = v___x_2962_;
v___y_2909_ = v___y_2942_;
v___y_2910_ = v___y_2945_;
v___y_2911_ = v___y_2943_;
v___y_2912_ = v___x_2975_;
v___y_2913_ = v_a_2949_;
v_only_2914_ = v___x_2991_;
v___y_2915_ = v___y_2394_;
v___y_2916_ = v___y_2395_;
v___y_2917_ = v___y_2396_;
v___y_2918_ = v___y_2397_;
v___y_2919_ = v___y_2398_;
v___y_2920_ = v___y_2399_;
v___y_2921_ = v___y_2400_;
v___y_2922_ = v___y_2401_;
goto v___jp_2907_;
}
}
else
{
lean_object* v___x_2992_; 
lean_dec(v___x_2976_);
v___x_2992_ = lean_box(0);
v___y_2908_ = v___x_2962_;
v___y_2909_ = v___y_2942_;
v___y_2910_ = v___y_2945_;
v___y_2911_ = v___y_2943_;
v___y_2912_ = v___x_2975_;
v___y_2913_ = v_a_2949_;
v_only_2914_ = v___x_2992_;
v___y_2915_ = v___y_2394_;
v___y_2916_ = v___y_2395_;
v___y_2917_ = v___y_2396_;
v___y_2918_ = v___y_2397_;
v___y_2919_ = v___y_2398_;
v___y_2920_ = v___y_2399_;
v___y_2921_ = v___y_2400_;
v___y_2922_ = v___y_2401_;
goto v___jp_2907_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2943_);
lean_dec(v___x_2462_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___x_2384_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v_a_2993_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2948_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2948_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
v___jp_3001_:
{
if (lean_obj_tag(v_usingArg_2385_) == 0)
{
v___y_2942_ = v___y_3002_;
v___y_2943_ = v___y_3003_;
v___y_2944_ = v___y_3004_;
v___y_2945_ = v_usingArg_2385_;
goto v___jp_2941_;
}
else
{
lean_object* v_val_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3013_; 
v_val_3005_ = lean_ctor_get(v_usingArg_2385_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_usingArg_2385_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3007_ = v_usingArg_2385_;
v_isShared_3008_ = v_isSharedCheck_3013_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_val_3005_);
lean_dec(v_usingArg_2385_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3013_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3009_ = l_Lean_Syntax_unsetTrailing(v_val_3005_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3009_);
v___x_3011_ = v___x_3007_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
v___y_2942_ = v___y_3002_;
v___y_2943_ = v___y_3003_;
v___y_2944_ = v___y_3004_;
v___y_2945_ = v___x_3011_;
goto v___jp_2941_;
}
}
}
}
v___jp_3014_:
{
if (v___y_3018_ == 0)
{
lean_dec(v___y_3017_);
lean_dec(v___x_2462_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v_usingArg_2385_);
lean_dec(v___x_2384_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v___y_2404_ = v___y_3016_;
goto v___jp_2403_;
}
else
{
v___y_3002_ = v___y_3015_;
v___y_3003_ = v___y_3016_;
v___y_3004_ = v___y_3017_;
goto v___jp_3001_;
}
}
v___jp_3019_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___f_3030_; lean_object* v___x_3031_; 
v___x_3025_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3024_, v___x_2459_);
v___x_3026_ = lean_box(v___x_2374_);
v___x_3027_ = lean_box(v___x_2459_);
v___x_3028_ = lean_box(v_useReducible_2377_);
v___x_3029_ = lean_box(v___x_2387_);
lean_inc(v___x_2382_);
lean_inc_ref(v___x_2379_);
lean_inc(v_usingArg_2385_);
lean_inc(v___x_2373_);
lean_inc(v_tk_2369_);
lean_inc(v___x_2384_);
v___f_3030_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 24, 14);
lean_closure_set(v___f_3030_, 0, v___x_2384_);
lean_closure_set(v___f_3030_, 1, v_tk_2369_);
lean_closure_set(v___f_3030_, 2, v___x_2464_);
lean_closure_set(v___f_3030_, 3, v___x_2373_);
lean_closure_set(v___f_3030_, 4, v___x_3025_);
lean_closure_set(v___f_3030_, 5, v___y_3020_);
lean_closure_set(v___f_3030_, 6, v___x_3026_);
lean_closure_set(v___f_3030_, 7, v_usingArg_2385_);
lean_closure_set(v___f_3030_, 8, v___x_3027_);
lean_closure_set(v___f_3030_, 9, v___x_2379_);
lean_closure_set(v___f_3030_, 10, v___x_3028_);
lean_closure_set(v___f_3030_, 11, v___x_3029_);
lean_closure_set(v___f_3030_, 12, v___x_2382_);
lean_closure_set(v___f_3030_, 13, v_usingTk_x3f_2388_);
v___x_3031_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3022_, v___f_3030_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_3022_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v___x_3033_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3034_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_2457_, v___x_3033_);
if (v___x_3034_ == 0)
{
if (lean_obj_tag(v_squeeze_2389_) == 0)
{
v___y_3015_ = v___y_3021_;
v___y_3016_ = v_a_3032_;
v___y_3017_ = v___y_3023_;
v___y_3018_ = v___x_3034_;
goto v___jp_3014_;
}
else
{
v___y_3015_ = v___y_3021_;
v___y_3016_ = v_a_3032_;
v___y_3017_ = v___y_3023_;
v___y_3018_ = v___x_2387_;
goto v___jp_3014_;
}
}
else
{
v___y_3002_ = v___y_3021_;
v___y_3003_ = v_a_3032_;
v___y_3004_ = v___y_3023_;
goto v___jp_3001_;
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v___y_3023_);
lean_dec(v___x_2462_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v_usingArg_2385_);
lean_dec(v___x_2384_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v_a_3035_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3031_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3031_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
v___jp_3043_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3047_ = l_Array_append___redArg(v___x_2465_, v___y_3046_);
lean_dec_ref(v___y_3046_);
lean_inc_n(v___x_2460_, 2);
v___x_3048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___x_2460_);
lean_ctor_set(v___x_3048_, 1, v___x_2464_);
lean_ctor_set(v___x_3048_, 2, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3049_, 0, v___x_2460_);
lean_ctor_set(v___x_3049_, 1, v___x_2464_);
lean_ctor_set(v___x_3049_, 2, v___x_2465_);
lean_inc(v___x_2462_);
v___x_3050_ = l_Lean_Syntax_node6(v___x_2460_, v___x_2462_, v___x_2463_, v___x_2386_, v___y_3044_, v___y_3045_, v___x_3048_, v___x_3049_);
v___x_3051_ = 0;
v___x_3052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23));
v___x_3053_ = lean_box(v___x_2459_);
v___x_3054_ = lean_box(v___x_3051_);
v___x_3055_ = lean_box(v___x_2459_);
lean_inc(v___x_3050_);
v___x_3056_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3056_, 0, v___x_3050_);
lean_closure_set(v___x_3056_, 1, v___x_3053_);
lean_closure_set(v___x_3056_, 2, v___x_3054_);
lean_closure_set(v___x_3056_, 3, v___x_3055_);
lean_closure_set(v___x_3056_, 4, v___x_3052_);
v___x_3057_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3056_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
if (lean_obj_tag(v_unfold_2390_) == 0)
{
lean_object* v_ctx_3059_; lean_object* v_simprocs_3060_; lean_object* v_dischargeWrapper_3061_; 
v_ctx_3059_ = lean_ctor_get(v_a_3058_, 0);
lean_inc_ref(v_ctx_3059_);
v_simprocs_3060_ = lean_ctor_get(v_a_3058_, 1);
lean_inc_ref(v_simprocs_3060_);
v_dischargeWrapper_3061_ = lean_ctor_get(v_a_3058_, 2);
lean_inc(v_dischargeWrapper_3061_);
lean_dec(v_a_3058_);
v___y_3020_ = v_simprocs_3060_;
v___y_3021_ = v___x_2459_;
v___y_3022_ = v_dischargeWrapper_3061_;
v___y_3023_ = v___x_3050_;
v___y_3024_ = v_ctx_3059_;
goto v___jp_3019_;
}
else
{
if (v___x_2387_ == 0)
{
lean_object* v_ctx_3062_; lean_object* v_simprocs_3063_; lean_object* v_dischargeWrapper_3064_; 
v_ctx_3062_ = lean_ctor_get(v_a_3058_, 0);
lean_inc_ref(v_ctx_3062_);
v_simprocs_3063_ = lean_ctor_get(v_a_3058_, 1);
lean_inc_ref(v_simprocs_3063_);
v_dischargeWrapper_3064_ = lean_ctor_get(v_a_3058_, 2);
lean_inc(v_dischargeWrapper_3064_);
lean_dec(v_a_3058_);
v___y_3020_ = v_simprocs_3063_;
v___y_3021_ = v___x_2387_;
v___y_3022_ = v_dischargeWrapper_3064_;
v___y_3023_ = v___x_3050_;
v___y_3024_ = v_ctx_3062_;
goto v___jp_3019_;
}
else
{
lean_object* v_ctx_3065_; lean_object* v_simprocs_3066_; lean_object* v_dischargeWrapper_3067_; lean_object* v___x_3068_; 
v_ctx_3065_ = lean_ctor_get(v_a_3058_, 0);
lean_inc_ref(v_ctx_3065_);
v_simprocs_3066_ = lean_ctor_get(v_a_3058_, 1);
lean_inc_ref(v_simprocs_3066_);
v_dischargeWrapper_3067_ = lean_ctor_get(v_a_3058_, 2);
lean_inc(v_dischargeWrapper_3067_);
lean_dec(v_a_3058_);
v___x_3068_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3065_);
v___y_3020_ = v_simprocs_3066_;
v___y_3021_ = v___x_2387_;
v___y_3022_ = v_dischargeWrapper_3067_;
v___y_3023_ = v___x_3050_;
v___y_3024_ = v___x_3068_;
goto v___jp_3019_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v___x_3050_);
lean_dec(v___x_2462_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v_usingTk_x3f_2388_);
lean_dec(v_usingArg_2385_);
lean_dec(v___x_2384_);
lean_dec(v___x_2382_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___f_2378_);
lean_dec(v___x_2376_);
lean_dec(v___x_2375_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec(v_tk_2369_);
v_a_3069_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3057_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3057_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
v___jp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = l_Array_append___redArg(v___x_2465_, v___y_3079_);
lean_dec_ref(v___y_3079_);
lean_inc(v___x_2460_);
v___x_3081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3081_, 0, v___x_2460_);
lean_ctor_set(v___x_3081_, 1, v___x_2464_);
lean_ctor_set(v___x_3081_, 2, v___x_3080_);
if (lean_obj_tag(v_args_2391_) == 1)
{
lean_object* v_val_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v_val_3082_ = lean_ctor_get(v_args_2391_, 0);
v___x_3083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___x_2460_, 3);
v___x_3084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_2460_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = l_Array_append___redArg(v___x_2465_, v_val_3082_);
v___x_3086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3086_, 0, v___x_2460_);
lean_ctor_set(v___x_3086_, 1, v___x_2464_);
lean_ctor_set(v___x_3086_, 2, v___x_3085_);
v___x_3087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_2460_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Array_mkArray3___redArg(v___x_3084_, v___x_3086_, v___x_3088_);
v___y_3044_ = v___y_3078_;
v___y_3045_ = v___x_3081_;
v___y_3046_ = v___x_3089_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_3044_ = v___y_3078_;
v___y_3045_ = v___x_3081_;
v___y_3046_ = v___x_3090_;
goto v___jp_3043_;
}
}
v___jp_3091_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = l_Array_append___redArg(v___x_2465_, v___y_3092_);
lean_dec_ref(v___y_3092_);
lean_inc(v___x_2460_);
v___x_3094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3094_, 0, v___x_2460_);
lean_ctor_set(v___x_3094_, 1, v___x_2464_);
lean_ctor_set(v___x_3094_, 2, v___x_3093_);
if (lean_obj_tag(v_only_2392_) == 1)
{
lean_object* v_val_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_val_3095_ = lean_ctor_get(v_only_2392_, 0);
v___x_3096_ = l_Lean_SourceInfo_fromRef(v_val_3095_, v___x_2374_);
v___x_3097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Array_mkArray1___redArg(v___x_3098_);
v___y_3078_ = v___x_3094_;
v___y_3079_ = v___x_3099_;
goto v___jp_3077_;
}
else
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___y_3078_ = v___x_3094_;
v___y_3079_ = v___x_3100_;
goto v___jp_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v_tk_3105_ = _args[0];
lean_object* v___x_3106_ = _args[1];
lean_object* v___x_3107_ = _args[2];
lean_object* v___x_3108_ = _args[3];
lean_object* v___x_3109_ = _args[4];
lean_object* v___x_3110_ = _args[5];
lean_object* v___x_3111_ = _args[6];
lean_object* v___x_3112_ = _args[7];
lean_object* v_useReducible_3113_ = _args[8];
lean_object* v___f_3114_ = _args[9];
lean_object* v___x_3115_ = _args[10];
lean_object* v___x_3116_ = _args[11];
lean_object* v___x_3117_ = _args[12];
lean_object* v___x_3118_ = _args[13];
lean_object* v___x_3119_ = _args[14];
lean_object* v___x_3120_ = _args[15];
lean_object* v_usingArg_3121_ = _args[16];
lean_object* v___x_3122_ = _args[17];
lean_object* v___x_3123_ = _args[18];
lean_object* v_usingTk_x3f_3124_ = _args[19];
lean_object* v_squeeze_3125_ = _args[20];
lean_object* v_unfold_3126_ = _args[21];
lean_object* v_args_3127_ = _args[22];
lean_object* v_only_3128_ = _args[23];
lean_object* v___y_3129_ = _args[24];
lean_object* v___y_3130_ = _args[25];
lean_object* v___y_3131_ = _args[26];
lean_object* v___y_3132_ = _args[27];
lean_object* v___y_3133_ = _args[28];
lean_object* v___y_3134_ = _args[29];
lean_object* v___y_3135_ = _args[30];
lean_object* v___y_3136_ = _args[31];
lean_object* v___y_3137_ = _args[32];
lean_object* v___y_3138_ = _args[33];
_start:
{
uint8_t v___x_97849__boxed_3139_; uint8_t v_useReducible_boxed_3140_; uint8_t v___x_97860__boxed_3141_; lean_object* v_res_3142_; 
v___x_97849__boxed_3139_ = lean_unbox(v___x_3110_);
v_useReducible_boxed_3140_ = lean_unbox(v_useReducible_3113_);
v___x_97860__boxed_3141_ = lean_unbox(v___x_3123_);
v_res_3142_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3105_, v___x_3106_, v___x_3107_, v___x_3108_, v___x_3109_, v___x_97849__boxed_3139_, v___x_3111_, v___x_3112_, v_useReducible_boxed_3140_, v___f_3114_, v___x_3115_, v___x_3116_, v___x_3117_, v___x_3118_, v___x_3119_, v___x_3120_, v_usingArg_3121_, v___x_3122_, v___x_97860__boxed_3141_, v_usingTk_x3f_3124_, v_squeeze_3125_, v_unfold_3126_, v_args_3127_, v_only_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v_only_3128_);
lean_dec(v_args_3127_);
lean_dec(v_unfold_3126_);
lean_dec(v_squeeze_3125_);
lean_dec(v___x_3119_);
lean_dec(v___x_3117_);
lean_dec(v___x_3116_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3168_, lean_object* v_stx_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3181_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_3182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
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
lean_object* v___f_3186_; lean_object* v___x_3187_; lean_object* v_tk_3188_; lean_object* v___x_3189_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; uint8_t v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; uint8_t v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v_usingTk_x3f_3240_; lean_object* v_usingArg_3241_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v_args_3273_; lean_object* v___y_3285_; lean_object* v___y_3286_; uint8_t v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v_only_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v_unfold_3329_; lean_object* v_squeeze_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___f_3186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
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
v___x_3215_ = lean_box(v___y_3207_);
lean_inc(v___y_3209_);
lean_inc(v___y_3204_);
v___f_3216_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3216_, 0, v_tk_3188_);
lean_closure_set(v___f_3216_, 1, v___x_3179_);
lean_closure_set(v___f_3216_, 2, v___x_3180_);
lean_closure_set(v___f_3216_, 3, v___x_3181_);
lean_closure_set(v___f_3216_, 4, v___x_3187_);
lean_closure_set(v___f_3216_, 5, v___x_3213_);
lean_closure_set(v___f_3216_, 6, v___y_3204_);
lean_closure_set(v___f_3216_, 7, v___x_3183_);
lean_closure_set(v___f_3216_, 8, v___x_3214_);
lean_closure_set(v___f_3216_, 9, v___f_3186_);
lean_closure_set(v___f_3216_, 10, v___x_3182_);
lean_closure_set(v___f_3216_, 11, v___y_3208_);
lean_closure_set(v___f_3216_, 12, v___y_3191_);
lean_closure_set(v___f_3216_, 13, v___x_3189_);
lean_closure_set(v___f_3216_, 14, v___y_3209_);
lean_closure_set(v___f_3216_, 15, v___y_3193_);
lean_closure_set(v___f_3216_, 16, v___y_3206_);
lean_closure_set(v___f_3216_, 17, v___y_3199_);
lean_closure_set(v___f_3216_, 18, v___x_3215_);
lean_closure_set(v___f_3216_, 19, v___y_3197_);
lean_closure_set(v___f_3216_, 20, v___y_3201_);
lean_closure_set(v___f_3216_, 21, v___y_3202_);
lean_closure_set(v___f_3216_, 22, v___y_3194_);
lean_closure_set(v___f_3216_, 23, v___y_3200_);
lean_closure_set(v___f_3216_, 24, v___y_3212_);
v___x_3217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3217_, 0, v___f_3216_);
v___x_3218_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3217_, v___y_3205_, v___y_3211_, v___y_3196_, v___y_3203_, v___y_3192_, v___y_3198_, v___y_3210_, v___y_3195_);
return v___x_3218_;
}
v___jp_3219_:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Syntax_getOptional_x3f(v___y_3220_);
lean_dec(v___y_3220_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_box(0);
v___y_3191_ = v___y_3221_;
v___y_3192_ = v___y_3222_;
v___y_3193_ = v___y_3223_;
v___y_3194_ = v___y_3224_;
v___y_3195_ = v___y_3225_;
v___y_3196_ = v___y_3226_;
v___y_3197_ = v_usingTk_x3f_3240_;
v___y_3198_ = v___y_3227_;
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
v___y_3204_ = v___y_3233_;
v___y_3205_ = v___y_3234_;
v___y_3206_ = v_usingArg_3241_;
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3237_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3238_;
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
v___y_3191_ = v___y_3221_;
v___y_3192_ = v___y_3222_;
v___y_3193_ = v___y_3223_;
v___y_3194_ = v___y_3224_;
v___y_3195_ = v___y_3225_;
v___y_3196_ = v___y_3226_;
v___y_3197_ = v_usingTk_x3f_3240_;
v___y_3198_ = v___y_3227_;
v___y_3199_ = v___y_3228_;
v___y_3200_ = v___y_3229_;
v___y_3201_ = v___y_3230_;
v___y_3202_ = v___y_3231_;
v___y_3203_ = v___y_3232_;
v___y_3204_ = v___y_3233_;
v___y_3205_ = v___y_3234_;
v___y_3206_ = v_usingArg_3241_;
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3237_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3238_;
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
v___x_3275_ = l_Lean_Syntax_getArg(v___y_3266_, v___x_3274_);
lean_dec(v___y_3266_);
v___x_3276_ = l_Lean_Syntax_isNone(v___x_3275_);
if (v___x_3276_ == 0)
{
uint8_t v___x_3277_; 
lean_inc(v___x_3275_);
v___x_3277_ = l_Lean_Syntax_matchesNull(v___x_3275_, v___y_3269_);
lean_dec(v___y_3269_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; 
lean_dec(v___x_3275_);
lean_dec(v_args_3273_);
lean_dec(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3256_);
lean_dec(v___y_3254_);
lean_dec(v___y_3253_);
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
v___y_3222_ = v___y_3255_;
v___y_3223_ = v___y_3256_;
v___y_3224_ = v_args_3273_;
v___y_3225_ = v___y_3257_;
v___y_3226_ = v___y_3258_;
v___y_3227_ = v___y_3259_;
v___y_3228_ = v___y_3260_;
v___y_3229_ = v___y_3261_;
v___y_3230_ = v___y_3262_;
v___y_3231_ = v___y_3263_;
v___y_3232_ = v___y_3264_;
v___y_3233_ = v___y_3265_;
v___y_3234_ = v___y_3267_;
v___y_3235_ = v___y_3268_;
v___y_3236_ = v___y_3270_;
v___y_3237_ = v___x_3274_;
v___y_3238_ = v___y_3271_;
v___y_3239_ = v___y_3272_;
v_usingTk_x3f_3240_ = v___x_3281_;
v_usingArg_3241_ = v___x_3282_;
goto v___jp_3219_;
}
}
else
{
lean_object* v___x_3283_; 
lean_dec(v___x_3275_);
lean_dec(v___y_3269_);
v___x_3283_ = lean_box(0);
v___y_3220_ = v___y_3253_;
v___y_3221_ = v___y_3254_;
v___y_3222_ = v___y_3255_;
v___y_3223_ = v___y_3256_;
v___y_3224_ = v_args_3273_;
v___y_3225_ = v___y_3257_;
v___y_3226_ = v___y_3258_;
v___y_3227_ = v___y_3259_;
v___y_3228_ = v___y_3260_;
v___y_3229_ = v___y_3261_;
v___y_3230_ = v___y_3262_;
v___y_3231_ = v___y_3263_;
v___y_3232_ = v___y_3264_;
v___y_3233_ = v___y_3265_;
v___y_3234_ = v___y_3267_;
v___y_3235_ = v___y_3268_;
v___y_3236_ = v___y_3270_;
v___y_3237_ = v___x_3274_;
v___y_3238_ = v___y_3271_;
v___y_3239_ = v___y_3272_;
v_usingTk_x3f_3240_ = v___x_3283_;
v_usingArg_3241_ = v___x_3283_;
goto v___jp_3219_;
}
}
v___jp_3284_:
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = l_Lean_Syntax_getArg(v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
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
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3286_);
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
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3310_);
v___x_3312_ = l_Lean_Syntax_isOfKind(v___x_3310_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_dec(v___x_3310_);
lean_dec(v_only_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3286_);
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
v___y_3253_ = v___y_3296_;
v___y_3254_ = v___y_3285_;
v___y_3255_ = v___y_3302_;
v___y_3256_ = v___y_3286_;
v___y_3257_ = v___y_3305_;
v___y_3258_ = v___y_3300_;
v___y_3259_ = v___y_3303_;
v___y_3260_ = v___y_3289_;
v___y_3261_ = v_only_3297_;
v___y_3262_ = v___y_3290_;
v___y_3263_ = v___y_3291_;
v___y_3264_ = v___y_3301_;
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___y_3293_;
v___y_3267_ = v___y_3298_;
v___y_3268_ = v___y_3287_;
v___y_3269_ = v___y_3295_;
v___y_3270_ = v___y_3288_;
v___y_3271_ = v___y_3304_;
v___y_3272_ = v___y_3299_;
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
v___y_3253_ = v___y_3296_;
v___y_3254_ = v___y_3285_;
v___y_3255_ = v___y_3302_;
v___y_3256_ = v___y_3286_;
v___y_3257_ = v___y_3305_;
v___y_3258_ = v___y_3300_;
v___y_3259_ = v___y_3303_;
v___y_3260_ = v___y_3289_;
v___y_3261_ = v_only_3297_;
v___y_3262_ = v___y_3290_;
v___y_3263_ = v___y_3291_;
v___y_3264_ = v___y_3301_;
v___y_3265_ = v___y_3292_;
v___y_3266_ = v___y_3293_;
v___y_3267_ = v___y_3298_;
v___y_3268_ = v___y_3287_;
v___y_3269_ = v___y_3295_;
v___y_3270_ = v___y_3288_;
v___y_3271_ = v___y_3304_;
v___y_3272_ = v___y_3299_;
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
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3331_);
v___x_3333_ = l_Lean_Syntax_isOfKind(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
lean_dec(v___x_3331_);
lean_dec(v_unfold_3329_);
lean_dec(v___y_3323_);
lean_dec(v___y_3319_);
lean_dec(v_tk_3188_);
v___x_3334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3335_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3187_);
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3335_);
v___x_3337_ = l_Lean_Syntax_isOfKind(v___x_3335_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_dec(v___x_3335_);
lean_dec(v___x_3331_);
lean_dec(v_unfold_3329_);
lean_dec(v___y_3323_);
lean_dec(v___y_3319_);
lean_dec(v_tk_3188_);
v___x_3338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3339_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3189_);
v___x_3340_ = l_Lean_Syntax_getArg(v___x_3331_, v___y_3319_);
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
lean_dec(v___y_3323_);
lean_dec(v___y_3319_);
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
lean_inc(v___y_3319_);
v___y_3285_ = v___x_3330_;
v___y_3286_ = v___y_3319_;
v___y_3287_ = v___x_3337_;
v___y_3288_ = v___x_3336_;
v___y_3289_ = v___x_3335_;
v___y_3290_ = v___y_3323_;
v___y_3291_ = v_unfold_3329_;
v___y_3292_ = v___x_3332_;
v___y_3293_ = v___x_3331_;
v___y_3294_ = v___x_3330_;
v___y_3295_ = v___y_3319_;
v___y_3296_ = v___x_3339_;
v_only_3297_ = v___x_3345_;
v___y_3298_ = v___y_3325_;
v___y_3299_ = v___y_3324_;
v___y_3300_ = v___y_3322_;
v___y_3301_ = v___y_3321_;
v___y_3302_ = v___y_3328_;
v___y_3303_ = v___y_3327_;
v___y_3304_ = v___y_3326_;
v___y_3305_ = v___y_3320_;
goto v___jp_3284_;
}
}
else
{
lean_object* v___x_3346_; 
lean_dec(v___x_3340_);
v___x_3346_ = lean_box(0);
lean_inc(v___y_3319_);
v___y_3285_ = v___x_3330_;
v___y_3286_ = v___y_3319_;
v___y_3287_ = v___x_3337_;
v___y_3288_ = v___x_3336_;
v___y_3289_ = v___x_3335_;
v___y_3290_ = v___y_3323_;
v___y_3291_ = v_unfold_3329_;
v___y_3292_ = v___x_3332_;
v___y_3293_ = v___x_3331_;
v___y_3294_ = v___x_3330_;
v___y_3295_ = v___y_3319_;
v___y_3296_ = v___x_3339_;
v_only_3297_ = v___x_3346_;
v___y_3298_ = v___y_3325_;
v___y_3299_ = v___y_3324_;
v___y_3300_ = v___y_3322_;
v___y_3301_ = v___y_3321_;
v___y_3302_ = v___y_3328_;
v___y_3303_ = v___y_3327_;
v___y_3304_ = v___y_3326_;
v___y_3305_ = v___y_3320_;
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
v___y_3319_ = v___x_3357_;
v___y_3320_ = v___y_3356_;
v___y_3321_ = v___y_3352_;
v___y_3322_ = v___y_3351_;
v___y_3323_ = v_squeeze_3348_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___y_3349_;
v___y_3326_ = v___y_3355_;
v___y_3327_ = v___y_3354_;
v___y_3328_ = v___y_3353_;
v_unfold_3329_ = v___x_3363_;
goto v___jp_3318_;
}
}
else
{
lean_object* v___x_3364_; 
lean_dec(v___x_3358_);
v___x_3364_ = lean_box(0);
v___y_3319_ = v___x_3357_;
v___y_3320_ = v___y_3356_;
v___y_3321_ = v___y_3352_;
v___y_3322_ = v___y_3351_;
v___y_3323_ = v_squeeze_3348_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___y_3349_;
v___y_3326_ = v___y_3355_;
v___y_3327_ = v___y_3354_;
v___y_3328_ = v___y_3353_;
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
size_t v_x_100062__boxed_3561_; size_t v_x_100063__boxed_3562_; lean_object* v_res_3563_; 
v_x_100062__boxed_3561_ = lean_unbox_usize(v_x_3557_);
lean_dec(v_x_3557_);
v_x_100063__boxed_3562_ = lean_unbox_usize(v_x_3558_);
lean_dec(v_x_3558_);
v_res_3563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_3555_, v_x_3556_, v_x_100062__boxed_3561_, v_x_100063__boxed_3562_, v_x_3559_, v_x_3560_);
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
v___x_3676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
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
lean_object* v___y_3741_; lean_object* v___y_3742_; uint8_t v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
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
lean_object* v___x_3774_; lean_object* v___y_3776_; uint8_t v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; uint8_t v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; uint8_t v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; uint8_t v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v_tk_3901_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v_args_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___x_3961_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v_only_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v_unfold_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v_squeeze_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
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
lean_inc_ref(v___y_3779_);
v___x_3798_ = l_Array_append___redArg(v___y_3779_, v___y_3797_);
lean_dec_ref(v___y_3797_);
lean_inc(v___y_3785_);
lean_inc(v___y_3790_);
v___x_3799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3799_, 0, v___y_3790_);
lean_ctor_set(v___x_3799_, 1, v___y_3785_);
lean_ctor_set(v___x_3799_, 2, v___x_3798_);
if (lean_obj_tag(v___y_3789_) == 1)
{
lean_object* v_val_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_val_3800_ = lean_ctor_get(v___y_3789_, 0);
lean_inc(v_val_3800_);
lean_dec_ref_known(v___y_3789_, 1);
v___x_3801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3790_, 4);
v___x_3803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___y_3790_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
lean_inc_ref(v___y_3779_);
v___x_3804_ = l_Array_append___redArg(v___y_3779_, v_val_3800_);
lean_dec(v_val_3800_);
lean_inc(v___y_3785_);
v___x_3805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3805_, 0, v___y_3790_);
lean_ctor_set(v___x_3805_, 1, v___y_3785_);
lean_ctor_set(v___x_3805_, 2, v___x_3804_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___y_3790_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = l_Lean_Syntax_node3(v___y_3790_, v___x_3801_, v___x_3803_, v___x_3805_, v___x_3807_);
v___x_3809_ = l_Array_mkArray1___redArg(v___x_3808_);
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___x_3799_;
v___y_3743_ = v___y_3777_;
v___y_3744_ = v___y_3778_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3779_;
v___y_3748_ = v___y_3782_;
v___y_3749_ = v___y_3783_;
v___y_3750_ = v___y_3784_;
v___y_3751_ = v___y_3785_;
v___y_3752_ = v___y_3786_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3787_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3792_;
v___y_3757_ = v___y_3791_;
v___y_3758_ = v___y_3794_;
v___y_3759_ = v___y_3793_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v___y_3796_;
v___y_3762_ = v___x_3809_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3810_; 
lean_dec(v___y_3789_);
v___x_3810_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___x_3799_;
v___y_3743_ = v___y_3777_;
v___y_3744_ = v___y_3778_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3779_;
v___y_3748_ = v___y_3782_;
v___y_3749_ = v___y_3783_;
v___y_3750_ = v___y_3784_;
v___y_3751_ = v___y_3785_;
v___y_3752_ = v___y_3786_;
v___y_3753_ = v___y_3788_;
v___y_3754_ = v___y_3787_;
v___y_3755_ = v___y_3790_;
v___y_3756_ = v___y_3792_;
v___y_3757_ = v___y_3791_;
v___y_3758_ = v___y_3794_;
v___y_3759_ = v___y_3793_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v___y_3796_;
v___y_3762_ = v___x_3810_;
goto v___jp_3740_;
}
}
v___jp_3811_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_inc_ref(v___y_3814_);
v___x_3834_ = l_Array_append___redArg(v___y_3814_, v___y_3833_);
lean_dec_ref(v___y_3833_);
lean_inc(v___y_3820_);
lean_inc(v___y_3825_);
v___x_3835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3835_, 0, v___y_3825_);
lean_ctor_set(v___x_3835_, 1, v___y_3820_);
lean_ctor_set(v___x_3835_, 2, v___x_3834_);
if (lean_obj_tag(v___y_3826_) == 1)
{
lean_object* v_val_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_val_3836_ = lean_ctor_get(v___y_3826_, 0);
lean_inc(v_val_3836_);
lean_dec_ref_known(v___y_3826_, 1);
v___x_3837_ = l_Lean_SourceInfo_fromRef(v_val_3836_, v___x_3772_);
lean_dec(v_val_3836_);
v___x_3838_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3837_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___x_3840_ = l_Array_mkArray1___redArg(v___x_3839_);
v___y_3776_ = v___x_3835_;
v___y_3777_ = v___y_3812_;
v___y_3778_ = v___y_3813_;
v___y_3779_ = v___y_3814_;
v___y_3780_ = v___y_3815_;
v___y_3781_ = v___y_3816_;
v___y_3782_ = v___y_3817_;
v___y_3783_ = v___y_3818_;
v___y_3784_ = v___y_3819_;
v___y_3785_ = v___y_3820_;
v___y_3786_ = v___y_3821_;
v___y_3787_ = v___y_3823_;
v___y_3788_ = v___y_3822_;
v___y_3789_ = v___y_3824_;
v___y_3790_ = v___y_3825_;
v___y_3791_ = v___y_3828_;
v___y_3792_ = v___y_3827_;
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
v___x_3841_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3826_);
lean_dec(v___y_3826_);
v___y_3776_ = v___x_3835_;
v___y_3777_ = v___y_3812_;
v___y_3778_ = v___y_3813_;
v___y_3779_ = v___y_3814_;
v___y_3780_ = v___y_3815_;
v___y_3781_ = v___y_3816_;
v___y_3782_ = v___y_3817_;
v___y_3783_ = v___y_3818_;
v___y_3784_ = v___y_3819_;
v___y_3785_ = v___y_3820_;
v___y_3786_ = v___y_3821_;
v___y_3787_ = v___y_3823_;
v___y_3788_ = v___y_3822_;
v___y_3789_ = v___y_3824_;
v___y_3790_ = v___y_3825_;
v___y_3791_ = v___y_3828_;
v___y_3792_ = v___y_3827_;
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
lean_inc_ref(v___y_3846_);
v___x_3864_ = l_Array_append___redArg(v___y_3846_, v___y_3863_);
lean_dec_ref(v___y_3863_);
lean_inc(v___y_3851_);
lean_inc(v___y_3856_);
v___x_3865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3865_, 0, v___y_3856_);
lean_ctor_set(v___x_3865_, 1, v___y_3851_);
lean_ctor_set(v___x_3865_, 2, v___x_3864_);
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_3845_) == 0)
{
lean_object* v___x_3867_; 
v___x_3867_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3812_ = v___y_3843_;
v___y_3813_ = v___y_3844_;
v___y_3814_ = v___y_3846_;
v___y_3815_ = v___y_3847_;
v___y_3816_ = v___y_3848_;
v___y_3817_ = v___x_3866_;
v___y_3818_ = v___y_3849_;
v___y_3819_ = v___y_3850_;
v___y_3820_ = v___y_3851_;
v___y_3821_ = v___y_3852_;
v___y_3822_ = v___y_3853_;
v___y_3823_ = v___y_3854_;
v___y_3824_ = v___y_3855_;
v___y_3825_ = v___y_3856_;
v___y_3826_ = v___y_3857_;
v___y_3827_ = v___y_3859_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3861_;
v___y_3830_ = v___y_3860_;
v___y_3831_ = v___y_3862_;
v___y_3832_ = v___x_3865_;
v___y_3833_ = v___x_3867_;
goto v___jp_3811_;
}
else
{
lean_object* v_val_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_val_3868_ = lean_ctor_get(v___y_3845_, 0);
lean_inc(v_val_3868_);
lean_dec_ref_known(v___y_3845_, 1);
v___x_3869_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3870_ = lean_array_push(v___x_3869_, v_val_3868_);
v___y_3812_ = v___y_3843_;
v___y_3813_ = v___y_3844_;
v___y_3814_ = v___y_3846_;
v___y_3815_ = v___y_3847_;
v___y_3816_ = v___y_3848_;
v___y_3817_ = v___x_3866_;
v___y_3818_ = v___y_3849_;
v___y_3819_ = v___y_3850_;
v___y_3820_ = v___y_3851_;
v___y_3821_ = v___y_3852_;
v___y_3822_ = v___y_3853_;
v___y_3823_ = v___y_3854_;
v___y_3824_ = v___y_3855_;
v___y_3825_ = v___y_3856_;
v___y_3826_ = v___y_3857_;
v___y_3827_ = v___y_3859_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3861_;
v___y_3830_ = v___y_3860_;
v___y_3831_ = v___y_3862_;
v___y_3832_ = v___x_3865_;
v___y_3833_ = v___x_3870_;
goto v___jp_3811_;
}
}
v___jp_3871_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_inc_ref(v___y_3874_);
v___x_3893_ = l_Array_append___redArg(v___y_3874_, v___y_3892_);
lean_dec_ref(v___y_3892_);
lean_inc(v___y_3881_);
lean_inc(v___y_3886_);
v___x_3894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3894_, 0, v___y_3886_);
lean_ctor_set(v___x_3894_, 1, v___y_3881_);
lean_ctor_set(v___x_3894_, 2, v___x_3893_);
if (lean_obj_tag(v___y_3880_) == 1)
{
lean_object* v_val_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_val_3895_ = lean_ctor_get(v___y_3880_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___y_3880_, 1);
v___x_3896_ = l_Lean_SourceInfo_fromRef(v_val_3895_, v___x_3772_);
lean_dec(v_val_3895_);
v___x_3897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_3898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = l_Array_mkArray1___redArg(v___x_3898_);
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3875_;
v___y_3846_ = v___y_3874_;
v___y_3847_ = v___y_3876_;
v___y_3848_ = v___y_3877_;
v___y_3849_ = v___y_3878_;
v___y_3850_ = v___y_3879_;
v___y_3851_ = v___y_3881_;
v___y_3852_ = v___y_3882_;
v___y_3853_ = v___y_3884_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3885_;
v___y_3856_ = v___y_3886_;
v___y_3857_ = v___y_3887_;
v___y_3858_ = v___y_3889_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___x_3894_;
v___y_3861_ = v___y_3890_;
v___y_3862_ = v___y_3891_;
v___y_3863_ = v___x_3899_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3880_);
lean_dec(v___y_3880_);
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3875_;
v___y_3846_ = v___y_3874_;
v___y_3847_ = v___y_3876_;
v___y_3848_ = v___y_3877_;
v___y_3849_ = v___y_3878_;
v___y_3850_ = v___y_3879_;
v___y_3851_ = v___y_3881_;
v___y_3852_ = v___y_3882_;
v___y_3853_ = v___y_3884_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3885_;
v___y_3856_ = v___y_3886_;
v___y_3857_ = v___y_3887_;
v___y_3858_ = v___y_3889_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___x_3894_;
v___y_3861_ = v___y_3890_;
v___y_3862_ = v___y_3891_;
v___y_3863_ = v___x_3900_;
goto v___jp_3842_;
}
}
v___jp_3902_:
{
lean_object* v_ref_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_ref_3918_ = lean_ctor_get(v___y_3916_, 5);
v___x_3919_ = 0;
v___x_3920_ = l_Lean_SourceInfo_fromRef(v_ref_3918_, v___x_3919_);
v___x_3921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3923_ = l_Lean_SourceInfo_fromRef(v_tk_3901_, v___x_3772_);
lean_dec(v_tk_3901_);
v___x_3924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v___x_3921_);
v___x_3925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_3926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_3913_) == 1)
{
lean_object* v_val_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_val_3927_ = lean_ctor_get(v___y_3913_, 0);
lean_inc(v_val_3927_);
lean_dec_ref_known(v___y_3913_, 1);
v___x_3928_ = l_Lean_SourceInfo_fromRef(v_val_3927_, v___x_3772_);
lean_dec(v_val_3927_);
v___x_3929_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_3930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l_Array_mkArray1___redArg(v___x_3930_);
v___y_3872_ = v___x_3919_;
v___y_3873_ = v___y_3903_;
v___y_3874_ = v___x_3926_;
v___y_3875_ = v___y_3917_;
v___y_3876_ = v___y_3904_;
v___y_3877_ = v___y_3905_;
v___y_3878_ = v___y_3906_;
v___y_3879_ = v___x_3924_;
v___y_3880_ = v___y_3907_;
v___y_3881_ = v___x_3925_;
v___y_3882_ = v___y_3908_;
v___y_3883_ = v___y_3909_;
v___y_3884_ = v___y_3910_;
v___y_3885_ = v___y_3911_;
v___y_3886_ = v___x_3920_;
v___y_3887_ = v___y_3912_;
v___y_3888_ = v___y_3914_;
v___y_3889_ = v___x_3922_;
v___y_3890_ = v___y_3915_;
v___y_3891_ = v___y_3916_;
v___y_3892_ = v___x_3931_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3913_);
lean_dec(v___y_3913_);
v___y_3872_ = v___x_3919_;
v___y_3873_ = v___y_3903_;
v___y_3874_ = v___x_3926_;
v___y_3875_ = v___y_3917_;
v___y_3876_ = v___y_3904_;
v___y_3877_ = v___y_3905_;
v___y_3878_ = v___y_3906_;
v___y_3879_ = v___x_3924_;
v___y_3880_ = v___y_3907_;
v___y_3881_ = v___x_3925_;
v___y_3882_ = v___y_3908_;
v___y_3883_ = v___y_3909_;
v___y_3884_ = v___y_3910_;
v___y_3885_ = v___y_3911_;
v___y_3886_ = v___x_3920_;
v___y_3887_ = v___y_3912_;
v___y_3888_ = v___y_3914_;
v___y_3889_ = v___x_3922_;
v___y_3890_ = v___y_3915_;
v___y_3891_ = v___y_3916_;
v___y_3892_ = v___x_3932_;
goto v___jp_3871_;
}
}
v___jp_3933_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = lean_unsigned_to_nat(5u);
v___x_3950_ = l_Lean_Syntax_getArg(v___y_3938_, v___x_3949_);
lean_dec(v___y_3938_);
v___x_3951_ = l_Lean_Syntax_getOptional_x3f(v___y_3935_);
lean_dec(v___y_3935_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_box(0);
v___y_3903_ = v___y_3945_;
v___y_3904_ = v___y_3946_;
v___y_3905_ = v___y_3943_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v___y_3937_;
v___y_3908_ = v___x_3950_;
v___y_3909_ = v___y_3942_;
v___y_3910_ = v___y_3948_;
v___y_3911_ = v_args_3940_;
v___y_3912_ = v___y_3939_;
v___y_3913_ = v___y_3934_;
v___y_3914_ = v___y_3944_;
v___y_3915_ = v___y_3941_;
v___y_3916_ = v___y_3947_;
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
v___y_3903_ = v___y_3945_;
v___y_3904_ = v___y_3946_;
v___y_3905_ = v___y_3943_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v___y_3937_;
v___y_3908_ = v___x_3950_;
v___y_3909_ = v___y_3942_;
v___y_3910_ = v___y_3948_;
v___y_3911_ = v_args_3940_;
v___y_3912_ = v___y_3939_;
v___y_3913_ = v___y_3934_;
v___y_3914_ = v___y_3944_;
v___y_3915_ = v___y_3941_;
v___y_3916_ = v___y_3947_;
v___y_3917_ = v___x_3958_;
goto v___jp_3902_;
}
}
}
}
v___jp_3962_:
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3978_ = l_Lean_Syntax_getArg(v___y_3968_, v___y_3963_);
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
lean_dec(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v_tk_3901_);
v___x_3981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3982_ = l_Lean_Syntax_getArg(v___x_3978_, v___x_3774_);
lean_dec(v___x_3978_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3982_);
v___x_3984_ = l_Lean_Syntax_isOfKind(v___x_3982_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; 
lean_dec(v___x_3982_);
lean_dec(v_only_3969_);
lean_dec(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
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
v___y_3934_ = v___y_3964_;
v___y_3935_ = v___y_3965_;
v___y_3936_ = v___y_3966_;
v___y_3937_ = v___y_3967_;
v___y_3938_ = v___y_3968_;
v___y_3939_ = v_only_3969_;
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
v___y_3934_ = v___y_3964_;
v___y_3935_ = v___y_3965_;
v___y_3936_ = v___y_3966_;
v___y_3937_ = v___y_3967_;
v___y_3938_ = v___y_3968_;
v___y_3939_ = v_only_3969_;
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
lean_dec(v___y_3991_);
lean_dec(v_tk_3901_);
v___x_4006_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4006_;
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4007_ = l_Lean_Syntax_getArg(v___x_4003_, v___x_3774_);
v___x_4008_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4007_);
v___x_4009_ = l_Lean_Syntax_isOfKind(v___x_4007_, v___x_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; 
lean_dec(v___x_4007_);
lean_dec(v___x_4003_);
lean_dec(v_unfold_3993_);
lean_dec(v___y_3991_);
lean_dec(v_tk_3901_);
v___x_4010_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4010_;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4011_ = l_Lean_Syntax_getArg(v___x_4003_, v___x_3961_);
v___x_4012_ = l_Lean_Syntax_getArg(v___x_4003_, v___y_3992_);
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
lean_dec(v___y_3991_);
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
v___y_3963_ = v___x_4002_;
v___y_3964_ = v___y_3991_;
v___y_3965_ = v___x_4011_;
v___y_3966_ = v___x_4007_;
v___y_3967_ = v_unfold_3993_;
v___y_3968_ = v___x_4003_;
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
v___y_3963_ = v___x_4002_;
v___y_3964_ = v___y_3991_;
v___y_3965_ = v___x_4011_;
v___y_3966_ = v___x_4007_;
v___y_3967_ = v_unfold_3993_;
v___y_3968_ = v___x_4003_;
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
v___y_3991_ = v_squeeze_4020_;
v___y_3992_ = v___x_4029_;
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
v___y_3991_ = v_squeeze_4020_;
v___y_3992_ = v___x_4029_;
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
lean_inc_ref(v___y_3747_);
v___x_3763_ = l_Array_append___redArg(v___y_3747_, v___y_3762_);
lean_dec_ref(v___y_3762_);
lean_inc_n(v___y_3751_, 2);
lean_inc_n(v___y_3755_, 4);
v___x_3764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3764_, 0, v___y_3755_);
lean_ctor_set(v___x_3764_, 1, v___y_3751_);
lean_ctor_set(v___x_3764_, 2, v___x_3763_);
v___x_3765_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___y_3755_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = l_Lean_Syntax_node2(v___y_3755_, v___y_3751_, v___x_3766_, v___y_3752_);
lean_inc(v___y_3748_);
v___x_3768_ = l_Lean_Syntax_node5(v___y_3755_, v___y_3748_, v___y_3749_, v___y_3741_, v___y_3742_, v___x_3764_, v___x_3767_);
lean_inc(v___y_3757_);
v___x_3769_ = l_Lean_Syntax_node4(v___y_3755_, v___y_3757_, v___y_3750_, v___y_3759_, v___y_3761_, v___x_3768_);
v___x_3770_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3743_, v___x_3769_, v___y_3758_, v___y_3754_, v___y_3746_, v___y_3756_, v___y_3744_, v___y_3745_, v___y_3760_, v___y_3753_);
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
