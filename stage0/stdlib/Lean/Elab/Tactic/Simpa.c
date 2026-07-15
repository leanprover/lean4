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
uint8_t v___x_94439__boxed_618_; uint8_t v___x_94440__boxed_619_; uint8_t v_useReducible_boxed_620_; uint8_t v___x_94444__boxed_621_; lean_object* v_res_622_; 
v___x_94439__boxed_618_ = lean_unbox(v___x_601_);
v___x_94440__boxed_619_ = lean_unbox(v___x_602_);
v_useReducible_boxed_620_ = lean_unbox(v_useReducible_607_);
v___x_94444__boxed_621_ = lean_unbox(v___x_608_);
v_res_622_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_599_, v_a_600_, v___x_94439__boxed_618_, v___x_94440__boxed_619_, v_a_603_, v_mvarCounter_604_, v___x_605_, v___x_606_, v_useReducible_boxed_620_, v___x_94444__boxed_621_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
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
lean_object* v_d_846_; lean_object* v_b_847_; lean_object* v___y_848_; uint8_t v___x_854_; 
v___x_854_ = l_Lean_Expr_hasExprMVar(v_e_834_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec_ref(v_e_834_);
v___x_855_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_a_835_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
else
{
uint8_t v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_835_, v_e_834_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(0);
lean_inc_ref(v_e_834_);
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_a_835_, v_e_834_, v___x_859_);
switch(lean_obj_tag(v_e_834_))
{
case 11:
{
lean_object* v_struct_861_; 
v_struct_861_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_struct_861_);
lean_dec_ref_known(v_e_834_, 3);
v_e_834_ = v_struct_861_;
v_a_835_ = v___x_860_;
goto _start;
}
case 7:
{
lean_object* v_binderType_863_; lean_object* v_body_864_; 
v_binderType_863_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_binderType_863_);
v_body_864_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_body_864_);
lean_dec_ref_known(v_e_834_, 3);
v_d_846_ = v_binderType_863_;
v_b_847_ = v_body_864_;
v___y_848_ = v___x_860_;
goto v___jp_845_;
}
case 6:
{
lean_object* v_binderType_865_; lean_object* v_body_866_; 
v_binderType_865_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_binderType_865_);
v_body_866_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_body_866_);
lean_dec_ref_known(v_e_834_, 3);
v_d_846_ = v_binderType_865_;
v_b_847_ = v_body_866_;
v___y_848_ = v___x_860_;
goto v___jp_845_;
}
case 8:
{
lean_object* v_type_867_; lean_object* v_value_868_; lean_object* v_body_869_; lean_object* v___x_870_; 
v_type_867_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_type_867_);
v_value_868_ = lean_ctor_get(v_e_834_, 2);
lean_inc_ref(v_value_868_);
v_body_869_ = lean_ctor_get(v_e_834_, 3);
lean_inc_ref(v_body_869_);
lean_dec_ref_known(v_e_834_, 4);
v___x_870_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_833_, v_type_867_, v___x_860_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v_fst_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
v_fst_872_ = lean_ctor_get(v_a_871_, 0);
if (lean_obj_tag(v_fst_872_) == 0)
{
lean_dec(v_a_871_);
lean_dec_ref(v_body_869_);
lean_dec_ref(v_value_868_);
return v___x_870_;
}
else
{
lean_object* v_snd_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v___x_870_, 1);
v_snd_873_ = lean_ctor_get(v_a_871_, 1);
lean_inc(v_snd_873_);
lean_dec(v_a_871_);
v___x_874_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_833_, v_value_868_, v_snd_873_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v_fst_876_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
v_fst_876_ = lean_ctor_get(v_a_875_, 0);
if (lean_obj_tag(v_fst_876_) == 0)
{
lean_dec(v_a_875_);
lean_dec_ref(v_body_869_);
return v___x_874_;
}
else
{
lean_object* v_snd_877_; 
lean_dec_ref_known(v___x_874_, 1);
v_snd_877_ = lean_ctor_get(v_a_875_, 1);
lean_inc(v_snd_877_);
lean_dec(v_a_875_);
v_e_834_ = v_body_869_;
v_a_835_ = v_snd_877_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_869_);
return v___x_874_;
}
}
}
else
{
lean_dec_ref(v_body_869_);
lean_dec_ref(v_value_868_);
return v___x_870_;
}
}
case 10:
{
lean_object* v_expr_879_; 
v_expr_879_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_expr_879_);
lean_dec_ref_known(v_e_834_, 2);
v_e_834_ = v_expr_879_;
v_a_835_ = v___x_860_;
goto _start;
}
case 5:
{
lean_object* v_fn_881_; lean_object* v_arg_882_; lean_object* v___x_883_; 
v_fn_881_ = lean_ctor_get(v_e_834_, 0);
lean_inc_ref(v_fn_881_);
v_arg_882_ = lean_ctor_get(v_e_834_, 1);
lean_inc_ref(v_arg_882_);
lean_dec_ref_known(v_e_834_, 2);
v___x_883_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_833_, v_fn_881_, v___x_860_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v_fst_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
v_fst_885_ = lean_ctor_get(v_a_884_, 0);
if (lean_obj_tag(v_fst_885_) == 0)
{
lean_dec(v_a_884_);
lean_dec_ref(v_arg_882_);
return v___x_883_;
}
else
{
lean_object* v_snd_886_; 
lean_dec_ref_known(v___x_883_, 1);
v_snd_886_ = lean_ctor_get(v_a_884_, 1);
lean_inc(v_snd_886_);
lean_dec(v_a_884_);
v_e_834_ = v_arg_882_;
v_a_835_ = v_snd_886_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_882_);
return v___x_883_;
}
}
case 2:
{
lean_object* v_mvarId_888_; lean_object* v___x_889_; 
v_mvarId_888_ = lean_ctor_get(v_e_834_, 0);
lean_inc(v_mvarId_888_);
lean_dec_ref_known(v_e_834_, 1);
v___x_889_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_833_, v_mvarId_888_, v___x_860_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_889_;
}
default: 
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref(v_e_834_);
v___x_890_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_860_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v_e_834_);
v___x_893_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_a_835_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object* v_mvarId_896_, lean_object* v_mvarId_x27_897_, lean_object* v_a_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = l_Lean_instBEqMVarId_beq(v_mvarId_896_, v_mvarId_x27_897_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_897_, v_a_898_, v___y_904_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_993_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_993_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_993_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_993_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_fst_914_; 
v_fst_914_ = lean_ctor_get(v_a_910_, 0);
lean_inc(v_fst_914_);
if (lean_obj_tag(v_fst_914_) == 0)
{
lean_object* v_snd_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_mvarId_x27_897_);
v_snd_915_ = lean_ctor_get(v_a_910_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_a_910_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v_a_910_, 0);
lean_dec(v_unused_934_);
v___x_917_ = v_a_910_;
v_isShared_918_ = v_isSharedCheck_933_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_snd_915_);
lean_dec(v_a_910_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_933_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_932_; 
v_a_919_ = lean_ctor_get(v_fst_914_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_fst_914_);
if (v_isSharedCheck_932_ == 0)
{
v___x_921_ = v_fst_914_;
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v_fst_914_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_931_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_924_);
v___x_926_ = v___x_917_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_snd_915_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_926_);
v___x_928_ = v___x_912_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
else
{
lean_object* v_a_935_; 
lean_del_object(v___x_912_);
v_a_935_ = lean_ctor_get(v_fst_914_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v_fst_914_, 1);
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v_snd_936_; lean_object* v___x_937_; 
v_snd_936_ = lean_ctor_get(v_a_910_, 1);
lean_inc(v_snd_936_);
lean_dec(v_a_910_);
v___x_937_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_897_, v_snd_936_, v___y_904_);
lean_dec(v_mvarId_x27_897_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_981_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_981_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_981_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_981_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_fst_942_; 
v_fst_942_ = lean_ctor_get(v_a_938_, 0);
lean_inc(v_fst_942_);
if (lean_obj_tag(v_fst_942_) == 0)
{
lean_object* v_snd_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_961_; 
v_snd_943_ = lean_ctor_get(v_a_938_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_a_938_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_a_938_, 0);
lean_dec(v_unused_962_);
v___x_945_ = v_a_938_;
v_isShared_946_ = v_isSharedCheck_961_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_snd_943_);
lean_dec(v_a_938_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_961_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_960_; 
v_a_947_ = lean_ctor_get(v_fst_942_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_fst_942_);
if (v_isSharedCheck_960_ == 0)
{
v___x_949_ = v_fst_942_;
v_isShared_950_ = v_isSharedCheck_960_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v_fst_942_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_960_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_959_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_952_);
v___x_954_ = v___x_945_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_snd_943_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_954_);
v___x_956_ = v___x_940_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
else
{
lean_object* v_a_963_; 
v_a_963_ = lean_ctor_get(v_fst_942_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v_fst_942_, 1);
if (lean_obj_tag(v_a_963_) == 0)
{
lean_object* v_snd_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_975_; 
v_snd_964_ = lean_ctor_get(v_a_938_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_a_938_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v_a_938_, 0);
lean_dec(v_unused_976_);
v___x_966_ = v_a_938_;
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_snd_964_);
lean_dec(v_a_938_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_975_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_970_ = v___x_966_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_snd_964_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_970_);
v___x_972_ = v___x_940_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v_val_977_; lean_object* v_snd_978_; lean_object* v_mvarIdPending_979_; 
lean_del_object(v___x_940_);
v_val_977_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_a_963_, 1);
v_snd_978_ = lean_ctor_get(v_a_938_, 1);
lean_inc(v_snd_978_);
lean_dec(v_a_938_);
v_mvarIdPending_979_ = lean_ctor_get(v_val_977_, 1);
lean_inc(v_mvarIdPending_979_);
lean_dec(v_val_977_);
v_mvarId_x27_897_ = v_mvarIdPending_979_;
v_a_898_ = v_snd_978_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_937_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_937_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_snd_990_; lean_object* v_val_991_; lean_object* v___x_992_; 
lean_dec(v_mvarId_x27_897_);
v_snd_990_ = lean_ctor_get(v_a_910_, 1);
lean_inc(v_snd_990_);
lean_dec(v_a_910_);
v_val_991_ = lean_ctor_get(v_a_935_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_a_935_, 1);
v___x_992_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_896_, v_val_991_, v_snd_990_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_mvarId_x27_897_);
v_a_994_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_909_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_909_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
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
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v_mvarId_x27_897_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1));
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v_a_898_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_1005_, lean_object* v_mvarId_x27_1006_, lean_object* v_a_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_1005_, v_mvarId_x27_1006_, v_a_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v_mvarId_1005_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_1018_, lean_object* v_e_1019_, lean_object* v_a_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1018_, v_e_1019_, v_a_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v_mvarId_1018_);
return v_res_1030_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_unsigned_to_nat(16u);
v___x_1033_ = lean_mk_array(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1037_, lean_object* v_e_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v___x_1048_; 
v___x_1048_ = l_Lean_Expr_hasExprMVar(v_e_1038_);
if (v___x_1048_ == 0)
{
uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_dec_ref(v_e_1038_);
v___x_1049_ = 1;
v___x_1050_ = lean_box(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1053_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1037_, v_e_1038_, v___x_1052_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1068_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1068_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1068_;
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
uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec_ref_known(v_fst_1058_, 1);
v___x_1059_ = 0;
v___x_1060_ = lean_box(v___x_1059_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1060_);
v___x_1062_ = v___x_1056_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_dec_ref_known(v_fst_1058_, 1);
v___x_1064_ = lean_box(v___x_1048_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1064_);
v___x_1066_ = v___x_1056_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1053_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1053_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1077_, lean_object* v_e_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1077_, v_e_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v_mvarId_1077_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object* v_msgData_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v_env_1096_; lean_object* v___x_1097_; lean_object* v_mctx_1098_; lean_object* v_lctx_1099_; lean_object* v_options_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1095_ = lean_st_ref_get(v___y_1093_);
v_env_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_env_1096_);
lean_dec(v___x_1095_);
v___x_1097_ = lean_st_ref_get(v___y_1091_);
v_mctx_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_mctx_1098_);
lean_dec(v___x_1097_);
v_lctx_1099_ = lean_ctor_get(v___y_1090_, 2);
v_options_1100_ = lean_ctor_get(v___y_1092_, 2);
lean_inc_ref(v_options_1100_);
lean_inc_ref(v_lctx_1099_);
v___x_1101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1101_, 0, v_env_1096_);
lean_ctor_set(v___x_1101_, 1, v_mctx_1098_);
lean_ctor_set(v___x_1101_, 2, v_lctx_1099_);
lean_ctor_set(v___x_1101_, 3, v_options_1100_);
v___x_1102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v_msgData_1089_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object* v_msgData_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msgData_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_ref_1117_; lean_object* v___x_1118_; lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_ref_1117_ = lean_ctor_get(v___y_1114_, 5);
v___x_1118_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msg_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_inc(v_ref_1117_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_ref_1117_);
lean_ctor_set(v___x_1123_, 1, v_a_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 1);
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v_msg_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_ks_1139_; lean_object* v_vs_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1164_; 
v_ks_1139_ = lean_ctor_get(v_x_1135_, 0);
v_vs_1140_ = lean_ctor_get(v_x_1135_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_x_1135_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1142_ = v_x_1135_;
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_vs_1140_);
lean_inc(v_ks_1139_);
lean_dec(v_x_1135_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1164_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = lean_array_get_size(v_ks_1139_);
v___x_1145_ = lean_nat_dec_lt(v_x_1136_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
lean_dec(v_x_1136_);
v___x_1146_ = lean_array_push(v_ks_1139_, v_x_1137_);
v___x_1147_ = lean_array_push(v_vs_1140_, v_x_1138_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1147_);
lean_ctor_set(v___x_1142_, 0, v___x_1146_);
v___x_1149_ = v___x_1142_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
else
{
lean_object* v_k_x27_1151_; uint8_t v___x_1152_; 
v_k_x27_1151_ = lean_array_fget_borrowed(v_ks_1139_, v_x_1136_);
v___x_1152_ = l_Lean_instBEqMVarId_beq(v_x_1137_, v_k_x27_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1154_; 
if (v_isShared_1143_ == 0)
{
v___x_1154_ = v___x_1142_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_ks_1139_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_vs_1140_);
v___x_1154_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_nat_add(v_x_1136_, v___x_1155_);
lean_dec(v_x_1136_);
v_x_1135_ = v___x_1154_;
v_x_1136_ = v___x_1156_;
goto _start;
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1159_ = lean_array_fset(v_ks_1139_, v_x_1136_, v_x_1137_);
v___x_1160_ = lean_array_fset(v_vs_1140_, v_x_1136_, v_x_1138_);
lean_dec(v_x_1136_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1160_);
lean_ctor_set(v___x_1142_, 0, v___x_1159_);
v___x_1162_ = v___x_1142_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1165_, lean_object* v_k_1166_, lean_object* v_v_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1165_, v___x_1168_, v_k_1166_, v_v_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0(void){
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
lean_object* v_es_1176_; size_t v___x_1177_; size_t v___x_1178_; lean_object* v_j_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_es_1176_ = lean_ctor_get(v_x_1171_, 0);
v___x_1177_ = ((size_t)31ULL);
v___x_1178_ = lean_usize_land(v_x_1172_, v___x_1177_);
v_j_1179_ = lean_usize_to_nat(v___x_1178_);
v___x_1180_ = lean_array_get_size(v_es_1176_);
v___x_1181_ = lean_nat_dec_lt(v_j_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v_j_1179_);
lean_dec(v_x_1175_);
lean_dec(v_x_1174_);
return v_x_1171_;
}
else
{
lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1220_; 
lean_inc_ref(v_es_1176_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_x_1171_, 0);
lean_dec(v_unused_1221_);
v___x_1183_ = v_x_1171_;
v_isShared_1184_ = v_isSharedCheck_1220_;
goto v_resetjp_1182_;
}
else
{
lean_dec(v_x_1171_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1220_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_v_1185_; lean_object* v___x_1186_; lean_object* v_xs_x27_1187_; lean_object* v___y_1189_; 
v_v_1185_ = lean_array_fget(v_es_1176_, v_j_1179_);
v___x_1186_ = lean_box(0);
v_xs_x27_1187_ = lean_array_fset(v_es_1176_, v_j_1179_, v___x_1186_);
switch(lean_obj_tag(v_v_1185_))
{
case 0:
{
lean_object* v_key_1194_; lean_object* v_val_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1205_; 
v_key_1194_ = lean_ctor_get(v_v_1185_, 0);
v_val_1195_ = lean_ctor_get(v_v_1185_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_v_1185_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1197_ = v_v_1185_;
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_val_1195_);
lean_inc(v_key_1194_);
lean_dec(v_v_1185_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
uint8_t v___x_1199_; 
v___x_1199_ = l_Lean_instBEqMVarId_beq(v_x_1174_, v_key_1194_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_del_object(v___x_1197_);
v___x_1200_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1194_, v_val_1195_, v_x_1174_, v_x_1175_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
v___y_1189_ = v___x_1201_;
goto v___jp_1188_;
}
else
{
lean_object* v___x_1203_; 
lean_dec(v_val_1195_);
lean_dec(v_key_1194_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v_x_1175_);
lean_ctor_set(v___x_1197_, 0, v_x_1174_);
v___x_1203_ = v___x_1197_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_x_1174_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_x_1175_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v___y_1189_ = v___x_1203_;
goto v___jp_1188_;
}
}
}
}
case 1:
{
lean_object* v_node_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1218_; 
v_node_1206_ = lean_ctor_get(v_v_1185_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_v_1185_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1208_ = v_v_1185_;
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_node_1206_);
lean_dec(v_v_1185_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1218_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1210_ = ((size_t)5ULL);
v___x_1211_ = lean_usize_shift_right(v_x_1172_, v___x_1210_);
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_x_1173_, v___x_1212_);
v___x_1214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_node_1206_, v___x_1211_, v___x_1213_, v_x_1174_, v_x_1175_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1214_);
v___x_1216_ = v___x_1208_;
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
v___y_1189_ = v___x_1216_;
goto v___jp_1188_;
}
}
}
default: 
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_x_1174_);
lean_ctor_set(v___x_1219_, 1, v_x_1175_);
v___y_1189_ = v___x_1219_;
goto v___jp_1188_;
}
}
v___jp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_array_fset(v_xs_x27_1187_, v_j_1179_, v___y_1189_);
lean_dec(v_j_1179_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1190_);
v___x_1192_ = v___x_1183_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
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
v___x_1235_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0);
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
size_t v_x_95741__boxed_1276_; size_t v_x_95742__boxed_1277_; lean_object* v_res_1278_; 
v_x_95741__boxed_1276_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_x_95742__boxed_1277_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_res_1278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1271_, v_x_95741__boxed_1276_, v_x_95742__boxed_1277_, v_x_1274_, v_x_1275_);
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
uint8_t v___y_95970__boxed_1368_; uint8_t v_suppressElabErrors_boxed_1369_; uint8_t v_res_1370_; lean_object* v_r_1371_; 
v___y_95970__boxed_1368_ = lean_unbox(v___y_1365_);
v_suppressElabErrors_boxed_1369_ = lean_unbox(v_suppressElabErrors_1366_);
v_res_1370_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v___y_95970__boxed_1368_, v_suppressElabErrors_boxed_1369_, v_x_1367_);
lean_dec(v_x_1367_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1373_, lean_object* v_msgData_1374_, uint8_t v_severity_1375_, uint8_t v_isSilent_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; uint8_t v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1444_; uint8_t v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; uint8_t v___y_1448_; lean_object* v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1455_; uint8_t v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1459_; lean_object* v___y_1460_; uint8_t v___y_1461_; uint8_t v___x_1466_; lean_object* v___y_1468_; lean_object* v___y_1469_; uint8_t v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; uint8_t v___y_1473_; uint8_t v___y_1474_; uint8_t v___y_1476_; uint8_t v___x_1491_; 
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
lean_ctor_set(v___x_1408_, 1, v___y_1388_);
lean_inc_ref(v___y_1385_);
lean_inc_ref(v___y_1386_);
v___x_1409_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1409_, 0, v___y_1386_);
lean_ctor_set(v___x_1409_, 1, v___y_1384_);
lean_ctor_set(v___x_1409_, 2, v___y_1387_);
lean_ctor_set(v___x_1409_, 3, v___y_1385_);
lean_ctor_set(v___x_1409_, 4, v___x_1408_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*5, v___y_1383_);
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*5 + 1, v___y_1389_);
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
lean_inc_ref_n(v___y_1421_, 2);
v___x_1433_ = l_Lean_FileMap_toPosition(v___y_1421_, v___y_1425_);
lean_dec(v___y_1425_);
v___x_1434_ = l_Lean_FileMap_toPosition(v___y_1421_, v___y_1426_);
lean_dec(v___y_1426_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
v___x_1436_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1423_ == 0)
{
lean_del_object(v___x_1431_);
lean_dec_ref(v___y_1419_);
v___y_1383_ = v___y_1420_;
v___y_1384_ = v___x_1433_;
v___y_1385_ = v___x_1436_;
v___y_1386_ = v___y_1422_;
v___y_1387_ = v___x_1435_;
v___y_1388_ = v_a_1429_;
v___y_1389_ = v___y_1424_;
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
v___y_1383_ = v___y_1420_;
v___y_1384_ = v___x_1433_;
v___y_1385_ = v___x_1436_;
v___y_1386_ = v___y_1422_;
v___y_1387_ = v___x_1435_;
v___y_1388_ = v_a_1429_;
v___y_1389_ = v___y_1424_;
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
v___x_1452_ = l_Lean_Syntax_getTailPos_x3f(v___y_1449_, v___y_1445_);
lean_dec(v___y_1449_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_inc(v___y_1451_);
v___y_1419_ = v___y_1444_;
v___y_1420_ = v___y_1445_;
v___y_1421_ = v___y_1446_;
v___y_1422_ = v___y_1447_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1450_;
v___y_1425_ = v___y_1451_;
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
v___y_1422_ = v___y_1447_;
v___y_1423_ = v___y_1448_;
v___y_1424_ = v___y_1450_;
v___y_1425_ = v___y_1451_;
v___y_1426_ = v_val_1453_;
goto v___jp_1418_;
}
}
v___jp_1454_:
{
lean_object* v_ref_1462_; lean_object* v___x_1463_; 
v_ref_1462_ = l_Lean_replaceRef(v_ref_1373_, v___y_1460_);
v___x_1463_ = l_Lean_Syntax_getPos_x3f(v_ref_1462_, v___y_1456_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___y_1444_ = v___y_1455_;
v___y_1445_ = v___y_1456_;
v___y_1446_ = v___y_1457_;
v___y_1447_ = v___y_1458_;
v___y_1448_ = v___y_1459_;
v___y_1449_ = v_ref_1462_;
v___y_1450_ = v___y_1461_;
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
v___y_1447_ = v___y_1458_;
v___y_1448_ = v___y_1459_;
v___y_1449_ = v_ref_1462_;
v___y_1450_ = v___y_1461_;
v___y_1451_ = v_val_1465_;
goto v___jp_1443_;
}
}
v___jp_1467_:
{
if (v___y_1474_ == 0)
{
v___y_1455_ = v___y_1471_;
v___y_1456_ = v___y_1473_;
v___y_1457_ = v___y_1468_;
v___y_1458_ = v___y_1469_;
v___y_1459_ = v___y_1470_;
v___y_1460_ = v___y_1472_;
v___y_1461_ = v_severity_1375_;
goto v___jp_1454_;
}
else
{
v___y_1455_ = v___y_1471_;
v___y_1456_ = v___y_1473_;
v___y_1457_ = v___y_1468_;
v___y_1458_ = v___y_1469_;
v___y_1459_ = v___y_1470_;
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
v___y_1468_ = v_fileMap_1478_;
v___y_1469_ = v_fileName_1477_;
v___y_1470_ = v_suppressElabErrors_1481_;
v___y_1471_ = v___f_1484_;
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
v___y_1468_ = v_fileMap_1478_;
v___y_1469_ = v_fileName_1477_;
v___y_1470_ = v_suppressElabErrors_1481_;
v___y_1471_ = v___f_1484_;
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
v___y_1890_ = v___x_2014_;
v___y_1891_ = v_a_2016_;
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
v___x_1852_ = l_Lean_Core_mkFreshUserName(v___y_1850_, v___y_1849_, v___y_1843_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc_n(v_a_1853_, 2);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = l_Lean_MVarId_rename(v___y_1841_, v___y_1851_, v_a_1853_, v___y_1847_, v___y_1842_, v___y_1849_, v___y_1843_);
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
v___x_1861_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1855_, v___f_1860_, v___y_1845_, v___y_1844_, v___y_1840_, v___y_1848_, v___y_1847_, v___y_1842_, v___y_1849_, v___y_1843_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref_known(v___x_1861_, 1);
v___y_1823_ = v___y_1846_;
v___y_1824_ = v___y_1839_;
v___y_1825_ = v___y_1842_;
goto v___jp_1822_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v___y_1846_);
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
lean_dec_ref(v___y_1846_);
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
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1841_);
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
lean_inc_ref(v___y_1891_);
v___x_1908_ = l_Lean_MVarId_note(v___x_1906_, v___x_1907_, v___y_1891_, v___y_1890_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
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
lean_dec_ref(v___y_1891_);
v___y_1823_ = v_snd_1920_;
v___y_1824_ = v_a_1905_;
v___y_1825_ = v___y_1897_;
goto v___jp_1822_;
}
else
{
if (lean_obj_tag(v___y_1891_) == 1)
{
lean_object* v_fvarId_1927_; lean_object* v_lctx_1928_; lean_object* v___x_1929_; 
v_fvarId_1927_ = lean_ctor_get(v___y_1891_, 0);
v_lctx_1928_ = lean_ctor_get(v___y_1896_, 2);
lean_inc(v_fvarId_1927_);
lean_inc_ref(v_lctx_1928_);
v___x_1929_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1928_, v_fvarId_1927_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_dec_ref_known(v___y_1891_, 1);
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
lean_dec_ref_known(v___y_1891_, 1);
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
v___x_1931_ = l_Lean_linter_unnecessarySimpa;
v___x_1932_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_1933_ = l_Lean_MessageData_ofExpr(v___y_1891_);
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
lean_dec_ref(v___y_1891_);
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
lean_dec_ref(v___y_1891_);
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
v___y_1839_ = v_a_1905_;
v___y_1840_ = v___y_1894_;
v___y_1841_ = v_snd_1958_;
v___y_1842_ = v___y_1897_;
v___y_1843_ = v___y_1899_;
v___y_1844_ = v___y_1893_;
v___y_1845_ = v___y_1892_;
v___y_1846_ = v_snd_1956_;
v___y_1847_ = v___y_1896_;
v___y_1848_ = v___y_1895_;
v___y_1849_ = v___y_1898_;
v___y_1850_ = v___x_1907_;
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
v___y_1839_ = v_a_1905_;
v___y_1840_ = v___y_1894_;
v___y_1841_ = v_snd_1958_;
v___y_1842_ = v___y_1897_;
v___y_1843_ = v___y_1899_;
v___y_1844_ = v___y_1893_;
v___y_1845_ = v___y_1892_;
v___y_1846_ = v_snd_1956_;
v___y_1847_ = v___y_1896_;
v___y_1848_ = v___y_1895_;
v___y_1849_ = v___y_1898_;
v___y_1850_ = v___x_1907_;
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
lean_dec_ref(v___y_1891_);
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
lean_dec_ref(v___y_1891_);
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
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
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
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
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
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
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
uint8_t v___x_96705__boxed_2155_; uint8_t v___x_96706__boxed_2156_; uint8_t v_useReducible_boxed_2157_; uint8_t v___x_96708__boxed_2158_; lean_object* v_res_2159_; 
v___x_96705__boxed_2155_ = lean_unbox(v___x_2134_);
v___x_96706__boxed_2156_ = lean_unbox(v___x_2135_);
v_useReducible_boxed_2157_ = lean_unbox(v_useReducible_2137_);
v___x_96708__boxed_2158_ = lean_unbox(v___x_2138_);
v_res_2159_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2132_, v_snd_2133_, v___x_96705__boxed_2155_, v___x_96706__boxed_2156_, v___x_2136_, v_useReducible_boxed_2157_, v___x_96708__boxed_2158_, v___x_2139_, v___x_2140_, v_simprocs_2141_, v_discharge_x3f_2142_, v_snd_2143_, v___x_2144_, v___f_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
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
v___x_2257_ = l_Lean_linter_unnecessarySimpa;
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
uint8_t v___x_97429__boxed_2327_; uint8_t v___x_97430__boxed_2328_; uint8_t v_useReducible_boxed_2329_; uint8_t v___x_97432__boxed_2330_; lean_object* v_res_2331_; 
v___x_97429__boxed_2327_ = lean_unbox(v___x_2309_);
v___x_97430__boxed_2328_ = lean_unbox(v___x_2311_);
v_useReducible_boxed_2329_ = lean_unbox(v_useReducible_2313_);
v___x_97432__boxed_2330_ = lean_unbox(v___x_2314_);
v_res_2331_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2303_, v_tk_2304_, v___x_2305_, v___x_2306_, v___x_2307_, v_simprocs_2308_, v___x_97429__boxed_2327_, v_usingArg_2310_, v___x_97430__boxed_2328_, v___x_2312_, v_useReducible_boxed_2329_, v___x_97432__boxed_2330_, v___x_2315_, v_usingTk_x3f_2316_, v_discharge_x3f_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
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
v___x_2341_ = lean_unsigned_to_nat(130u);
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
v___x_2363_ = lean_unsigned_to_nat(131u);
v___x_2364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2366_ = l_mkPanicMessageWithDecl(v___x_2365_, v___x_2364_, v___x_2363_, v___x_2362_, v___x_2361_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2368_, lean_object* v___x_2369_, lean_object* v___x_2370_, lean_object* v___x_2371_, lean_object* v___x_2372_, uint8_t v___x_2373_, lean_object* v___x_2374_, lean_object* v___x_2375_, uint8_t v_useReducible_2376_, lean_object* v___f_2377_, lean_object* v___x_2378_, lean_object* v___x_2379_, lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v___x_2382_, lean_object* v___x_2383_, lean_object* v_usingArg_2384_, lean_object* v___x_2385_, uint8_t v___x_2386_, lean_object* v_usingTk_x3f_2387_, lean_object* v_squeeze_2388_, lean_object* v_unfold_2389_, lean_object* v_args_2390_, lean_object* v_only_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___y_2403_; lean_object* v___y_2407_; lean_object* v_stx_2408_; lean_object* v___y_2409_; lean_object* v_ref_2410_; lean_object* v___y_2411_; lean_object* v___y_2430_; lean_object* v_stx_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v_options_2456_; lean_object* v_ref_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2866_; lean_object* v___y_2867_; uint8_t v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v_args_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2907_; uint8_t v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v_only_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; uint8_t v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; uint8_t v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; uint8_t v___y_3017_; lean_object* v___y_3019_; uint8_t v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3091_; 
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
lean_inc_n(v___y_2472_, 2);
v___x_2478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2478_, 0, v___y_2472_);
lean_ctor_set(v___x_2478_, 1, v___x_2463_);
lean_ctor_set(v___x_2478_, 2, v___x_2477_);
v___x_2479_ = l_Lean_Syntax_node5(v___y_2472_, v___x_2374_, v___y_2469_, v___y_2466_, v___y_2468_, v___y_2475_, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node2(v___y_2472_, v___y_2474_, v___y_2470_, v___x_2479_);
v___y_2430_ = v___y_2473_;
v_stx_2431_ = v___x_2480_;
v___y_2432_ = v___y_2467_;
v___y_2433_ = v___y_2471_;
goto v___jp_2429_;
}
v___jp_2481_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = l_Array_append___redArg(v___x_2464_, v___y_2492_);
lean_dec_ref(v___y_2492_);
lean_inc(v___y_2489_);
v___x_2494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2494_, 0, v___y_2489_);
lean_ctor_set(v___x_2494_, 1, v___x_2463_);
lean_ctor_set(v___x_2494_, 2, v___x_2493_);
if (lean_obj_tag(v___y_2486_) == 1)
{
lean_object* v_val_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_dec(v___x_2372_);
v_val_2495_ = lean_ctor_get(v___y_2486_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v___y_2486_, 1);
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2489_);
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___y_2489_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Array_mkArray2___redArg(v___x_2497_, v_val_2495_);
v___y_2466_ = v___y_2482_;
v___y_2467_ = v___y_2484_;
v___y_2468_ = v___y_2483_;
v___y_2469_ = v___y_2485_;
v___y_2470_ = v___y_2487_;
v___y_2471_ = v___y_2488_;
v___y_2472_ = v___y_2489_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2491_;
v___y_2475_ = v___x_2494_;
v___y_2476_ = v___x_2498_;
goto v___jp_2465_;
}
else
{
lean_object* v___x_2499_; 
lean_dec(v___y_2486_);
v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2466_ = v___y_2482_;
v___y_2467_ = v___y_2484_;
v___y_2468_ = v___y_2483_;
v___y_2469_ = v___y_2485_;
v___y_2470_ = v___y_2487_;
v___y_2471_ = v___y_2488_;
v___y_2472_ = v___y_2489_;
v___y_2473_ = v___y_2490_;
v___y_2474_ = v___y_2491_;
v___y_2475_ = v___x_2494_;
v___y_2476_ = v___x_2499_;
goto v___jp_2465_;
}
}
v___jp_2500_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = l_Array_append___redArg(v___x_2464_, v___y_2511_);
lean_dec_ref(v___y_2511_);
lean_inc(v___y_2508_);
v___x_2513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2513_, 0, v___y_2508_);
lean_ctor_set(v___x_2513_, 1, v___x_2463_);
lean_ctor_set(v___x_2513_, 2, v___x_2512_);
if (lean_obj_tag(v___y_2504_) == 1)
{
lean_object* v_val_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_val_2514_ = lean_ctor_get(v___y_2504_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v___y_2504_, 1);
v___x_2515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2516_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2515_);
v___x_2517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2508_, 4);
v___x_2518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___y_2508_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Array_append___redArg(v___x_2464_, v_val_2514_);
lean_dec(v_val_2514_);
v___x_2520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2520_, 0, v___y_2508_);
lean_ctor_set(v___x_2520_, 1, v___x_2463_);
lean_ctor_set(v___x_2520_, 2, v___x_2519_);
v___x_2521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___y_2508_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_Syntax_node3(v___y_2508_, v___x_2516_, v___x_2518_, v___x_2520_, v___x_2522_);
v___x_2524_ = l_Array_mkArray1___redArg(v___x_2523_);
v___y_2482_ = v___y_2501_;
v___y_2483_ = v___x_2513_;
v___y_2484_ = v___y_2502_;
v___y_2485_ = v___y_2503_;
v___y_2486_ = v___y_2506_;
v___y_2487_ = v___y_2505_;
v___y_2488_ = v___y_2507_;
v___y_2489_ = v___y_2508_;
v___y_2490_ = v___y_2509_;
v___y_2491_ = v___y_2510_;
v___y_2492_ = v___x_2524_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2525_; 
lean_dec(v___y_2504_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2525_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2482_ = v___y_2501_;
v___y_2483_ = v___x_2513_;
v___y_2484_ = v___y_2502_;
v___y_2485_ = v___y_2503_;
v___y_2486_ = v___y_2506_;
v___y_2487_ = v___y_2505_;
v___y_2488_ = v___y_2507_;
v___y_2489_ = v___y_2508_;
v___y_2490_ = v___y_2509_;
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
lean_inc(v___y_2533_);
v___x_2539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2539_, 0, v___y_2533_);
lean_ctor_set(v___x_2539_, 1, v___x_2463_);
lean_ctor_set(v___x_2539_, 2, v___x_2538_);
if (lean_obj_tag(v___y_2535_) == 1)
{
lean_object* v_val_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_val_2540_ = lean_ctor_get(v___y_2535_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v___y_2535_, 1);
v___x_2541_ = l_Lean_SourceInfo_fromRef(v_val_2540_, v___x_2373_);
lean_dec(v_val_2540_);
v___x_2542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = l_Array_mkArray1___redArg(v___x_2543_);
v___y_2501_ = v___x_2539_;
v___y_2502_ = v___y_2527_;
v___y_2503_ = v___y_2528_;
v___y_2504_ = v___y_2529_;
v___y_2505_ = v___y_2531_;
v___y_2506_ = v___y_2530_;
v___y_2507_ = v___y_2532_;
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
v___y_2510_ = v___y_2536_;
v___y_2511_ = v___x_2544_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2545_; 
lean_dec(v___y_2535_);
v___x_2545_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2501_ = v___x_2539_;
v___y_2502_ = v___y_2527_;
v___y_2503_ = v___y_2528_;
v___y_2504_ = v___y_2529_;
v___y_2505_ = v___y_2531_;
v___y_2506_ = v___y_2530_;
v___y_2507_ = v___y_2532_;
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
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
lean_inc_n(v___y_2549_, 3);
v___x_2562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2562_, 0, v___y_2549_);
lean_ctor_set(v___x_2562_, 1, v___x_2463_);
lean_ctor_set(v___x_2562_, 2, v___x_2561_);
v___x_2563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___y_2549_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node6(v___y_2549_, v___y_2554_, v___y_2555_, v___y_2558_, v___y_2550_, v___x_2562_, v___x_2564_, v___y_2548_);
v___x_2566_ = l_Lean_Syntax_node4(v___y_2549_, v___y_2556_, v___y_2551_, v___y_2559_, v___y_2557_, v___x_2565_);
v___y_2430_ = v___y_2553_;
v_stx_2431_ = v___x_2566_;
v___y_2432_ = v___y_2547_;
v___y_2433_ = v___y_2552_;
goto v___jp_2429_;
}
v___jp_2567_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = l_Array_append___redArg(v___x_2464_, v___y_2581_);
lean_dec_ref(v___y_2581_);
lean_inc(v___y_2570_);
v___x_2583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2583_, 0, v___y_2570_);
lean_ctor_set(v___x_2583_, 1, v___x_2463_);
lean_ctor_set(v___x_2583_, 2, v___x_2582_);
if (lean_obj_tag(v___y_2577_) == 1)
{
lean_object* v_val_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v___x_2372_);
v_val_2584_ = lean_ctor_get(v___y_2577_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v___y_2577_, 1);
v___x_2585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2586_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2585_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2570_, 4);
v___x_2588_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___y_2570_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Array_append___redArg(v___x_2464_, v_val_2584_);
lean_dec(v_val_2584_);
v___x_2590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___y_2570_);
lean_ctor_set(v___x_2590_, 1, v___x_2463_);
lean_ctor_set(v___x_2590_, 2, v___x_2589_);
v___x_2591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___y_2570_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = l_Lean_Syntax_node3(v___y_2570_, v___x_2586_, v___x_2588_, v___x_2590_, v___x_2592_);
v___x_2594_ = l_Array_mkArray1___redArg(v___x_2593_);
v___y_2547_ = v___y_2568_;
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___x_2583_;
v___y_2551_ = v___y_2571_;
v___y_2552_ = v___y_2572_;
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___y_2574_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2576_;
v___y_2557_ = v___y_2578_;
v___y_2558_ = v___y_2579_;
v___y_2559_ = v___y_2580_;
v___y_2560_ = v___x_2594_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2595_; 
lean_dec(v___y_2577_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2547_ = v___y_2568_;
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___x_2583_;
v___y_2551_ = v___y_2571_;
v___y_2552_ = v___y_2572_;
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___y_2574_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2576_;
v___y_2557_ = v___y_2578_;
v___y_2558_ = v___y_2579_;
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
lean_inc(v___y_2599_);
v___x_2612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2612_, 0, v___y_2599_);
lean_ctor_set(v___x_2612_, 1, v___x_2463_);
lean_ctor_set(v___x_2612_, 2, v___x_2611_);
if (lean_obj_tag(v___y_2603_) == 1)
{
lean_object* v_val_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_val_2613_ = lean_ctor_get(v___y_2603_, 0);
lean_inc(v_val_2613_);
lean_dec_ref_known(v___y_2603_, 1);
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
v___y_2572_ = v___y_2601_;
v___y_2573_ = v___y_2602_;
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
lean_dec(v___y_2603_);
v___x_2618_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2568_ = v___y_2597_;
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2599_;
v___y_2571_ = v___y_2600_;
v___y_2572_ = v___y_2601_;
v___y_2573_ = v___y_2602_;
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
lean_inc_n(v___y_2620_, 2);
v___x_2632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2632_, 0, v___y_2620_);
lean_ctor_set(v___x_2632_, 1, v___x_2463_);
lean_ctor_set(v___x_2632_, 2, v___x_2631_);
v___x_2633_ = l_Lean_Syntax_node5(v___y_2620_, v___x_2374_, v___y_2624_, v___y_2628_, v___y_2623_, v___y_2629_, v___x_2632_);
lean_inc(v___y_2622_);
v___x_2634_ = l_Lean_Syntax_node4(v___y_2620_, v___x_2375_, v___y_2627_, v___y_2622_, v___y_2622_, v___x_2633_);
v___y_2430_ = v___y_2626_;
v_stx_2431_ = v___x_2634_;
v___y_2432_ = v___y_2621_;
v___y_2433_ = v___y_2625_;
goto v___jp_2429_;
}
v___jp_2635_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = l_Array_append___redArg(v___x_2464_, v___y_2646_);
lean_dec_ref(v___y_2646_);
lean_inc(v___y_2636_);
v___x_2648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2648_, 0, v___y_2636_);
lean_ctor_set(v___x_2648_, 1, v___x_2463_);
lean_ctor_set(v___x_2648_, 2, v___x_2647_);
if (lean_obj_tag(v___y_2641_) == 1)
{
lean_object* v_val_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v___x_2372_);
v_val_2649_ = lean_ctor_get(v___y_2641_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v___y_2641_, 1);
v___x_2650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2636_);
v___x_2651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___y_2636_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Array_mkArray2___redArg(v___x_2651_, v_val_2649_);
v___y_2620_ = v___y_2636_;
v___y_2621_ = v___y_2637_;
v___y_2622_ = v___y_2639_;
v___y_2623_ = v___y_2638_;
v___y_2624_ = v___y_2640_;
v___y_2625_ = v___y_2642_;
v___y_2626_ = v___y_2644_;
v___y_2627_ = v___y_2643_;
v___y_2628_ = v___y_2645_;
v___y_2629_ = v___x_2648_;
v___y_2630_ = v___x_2652_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2653_; 
lean_dec(v___y_2641_);
v___x_2653_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2620_ = v___y_2636_;
v___y_2621_ = v___y_2637_;
v___y_2622_ = v___y_2639_;
v___y_2623_ = v___y_2638_;
v___y_2624_ = v___y_2640_;
v___y_2625_ = v___y_2642_;
v___y_2626_ = v___y_2644_;
v___y_2627_ = v___y_2643_;
v___y_2628_ = v___y_2645_;
v___y_2629_ = v___x_2648_;
v___y_2630_ = v___x_2653_;
goto v___jp_2619_;
}
}
v___jp_2654_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = l_Array_append___redArg(v___x_2464_, v___y_2665_);
lean_dec_ref(v___y_2665_);
lean_inc(v___y_2655_);
v___x_2667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2655_);
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
lean_inc_n(v___y_2655_, 4);
v___x_2672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___y_2655_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Array_append___redArg(v___x_2464_, v_val_2668_);
lean_dec(v_val_2668_);
v___x_2674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2674_, 0, v___y_2655_);
lean_ctor_set(v___x_2674_, 1, v___x_2463_);
lean_ctor_set(v___x_2674_, 2, v___x_2673_);
v___x_2675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___y_2655_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_Syntax_node3(v___y_2655_, v___x_2670_, v___x_2672_, v___x_2674_, v___x_2676_);
v___x_2678_ = l_Array_mkArray1___redArg(v___x_2677_);
v___y_2636_ = v___y_2655_;
v___y_2637_ = v___y_2656_;
v___y_2638_ = v___x_2667_;
v___y_2639_ = v___y_2657_;
v___y_2640_ = v___y_2658_;
v___y_2641_ = v___y_2660_;
v___y_2642_ = v___y_2661_;
v___y_2643_ = v___y_2663_;
v___y_2644_ = v___y_2662_;
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
v___y_2636_ = v___y_2655_;
v___y_2637_ = v___y_2656_;
v___y_2638_ = v___x_2667_;
v___y_2639_ = v___y_2657_;
v___y_2640_ = v___y_2658_;
v___y_2641_ = v___y_2660_;
v___y_2642_ = v___y_2661_;
v___y_2643_ = v___y_2663_;
v___y_2644_ = v___y_2662_;
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
lean_inc(v___y_2681_);
v___x_2693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2693_, 0, v___y_2681_);
lean_ctor_set(v___x_2693_, 1, v___x_2463_);
lean_ctor_set(v___x_2693_, 2, v___x_2692_);
if (lean_obj_tag(v___y_2690_) == 1)
{
lean_object* v_val_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_val_2694_ = lean_ctor_get(v___y_2690_, 0);
lean_inc(v_val_2694_);
lean_dec_ref_known(v___y_2690_, 1);
v___x_2695_ = l_Lean_SourceInfo_fromRef(v_val_2694_, v___x_2373_);
lean_dec(v_val_2694_);
v___x_2696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Array_mkArray1___redArg(v___x_2697_);
v___y_2655_ = v___y_2681_;
v___y_2656_ = v___y_2682_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2684_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2686_;
v___y_2661_ = v___y_2687_;
v___y_2662_ = v___y_2689_;
v___y_2663_ = v___y_2688_;
v___y_2664_ = v___x_2693_;
v___y_2665_ = v___x_2698_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2699_; 
lean_dec(v___y_2690_);
v___x_2699_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2655_ = v___y_2681_;
v___y_2656_ = v___y_2682_;
v___y_2657_ = v___y_2683_;
v___y_2658_ = v___y_2684_;
v___y_2659_ = v___y_2685_;
v___y_2660_ = v___y_2686_;
v___y_2661_ = v___y_2687_;
v___y_2662_ = v___y_2689_;
v___y_2663_ = v___y_2688_;
v___y_2664_ = v___x_2693_;
v___y_2665_ = v___x_2699_;
goto v___jp_2654_;
}
}
v___jp_2700_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2714_ = l_Array_append___redArg(v___x_2464_, v___y_2713_);
lean_dec_ref(v___y_2713_);
lean_inc_n(v___y_2708_, 3);
v___x_2715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2715_, 0, v___y_2708_);
lean_ctor_set(v___x_2715_, 1, v___x_2463_);
lean_ctor_set(v___x_2715_, 2, v___x_2714_);
v___x_2716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___y_2708_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = l_Lean_Syntax_node6(v___y_2708_, v___y_2703_, v___y_2709_, v___y_2711_, v___y_2704_, v___x_2715_, v___x_2717_, v___y_2712_);
lean_inc(v___y_2707_);
v___x_2719_ = l_Lean_Syntax_node4(v___y_2708_, v___y_2710_, v___y_2702_, v___y_2707_, v___y_2707_, v___x_2718_);
v___y_2430_ = v___y_2706_;
v_stx_2431_ = v___x_2719_;
v___y_2432_ = v___y_2701_;
v___y_2433_ = v___y_2705_;
goto v___jp_2429_;
}
v___jp_2720_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = l_Array_append___redArg(v___x_2464_, v___y_2733_);
lean_dec_ref(v___y_2733_);
lean_inc(v___y_2727_);
v___x_2735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2735_, 0, v___y_2727_);
lean_ctor_set(v___x_2735_, 1, v___x_2463_);
lean_ctor_set(v___x_2735_, 2, v___x_2734_);
if (lean_obj_tag(v___y_2729_) == 1)
{
lean_object* v_val_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v___x_2372_);
v_val_2736_ = lean_ctor_get(v___y_2729_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___y_2729_, 1);
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2738_ = l_Lean_Name_mkStr4(v___x_2369_, v___x_2370_, v___x_2371_, v___x_2737_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2727_, 4);
v___x_2740_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___y_2727_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Array_append___redArg(v___x_2464_, v_val_2736_);
lean_dec(v_val_2736_);
v___x_2742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2742_, 0, v___y_2727_);
lean_ctor_set(v___x_2742_, 1, v___x_2463_);
lean_ctor_set(v___x_2742_, 2, v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2744_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___y_2727_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = l_Lean_Syntax_node3(v___y_2727_, v___x_2738_, v___x_2740_, v___x_2742_, v___x_2744_);
v___x_2746_ = l_Array_mkArray1___redArg(v___x_2745_);
v___y_2701_ = v___y_2721_;
v___y_2702_ = v___y_2722_;
v___y_2703_ = v___y_2723_;
v___y_2704_ = v___x_2735_;
v___y_2705_ = v___y_2724_;
v___y_2706_ = v___y_2725_;
v___y_2707_ = v___y_2726_;
v___y_2708_ = v___y_2727_;
v___y_2709_ = v___y_2728_;
v___y_2710_ = v___y_2730_;
v___y_2711_ = v___y_2731_;
v___y_2712_ = v___y_2732_;
v___y_2713_ = v___x_2746_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2747_; 
lean_dec(v___y_2729_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___x_2747_ = lean_mk_empty_array_with_capacity(v___x_2372_);
lean_dec(v___x_2372_);
v___y_2701_ = v___y_2721_;
v___y_2702_ = v___y_2722_;
v___y_2703_ = v___y_2723_;
v___y_2704_ = v___x_2735_;
v___y_2705_ = v___y_2724_;
v___y_2706_ = v___y_2725_;
v___y_2707_ = v___y_2726_;
v___y_2708_ = v___y_2727_;
v___y_2709_ = v___y_2728_;
v___y_2710_ = v___y_2730_;
v___y_2711_ = v___y_2731_;
v___y_2712_ = v___y_2732_;
v___y_2713_ = v___x_2747_;
goto v___jp_2700_;
}
}
v___jp_2748_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = l_Array_append___redArg(v___x_2464_, v___y_2761_);
lean_dec_ref(v___y_2761_);
lean_inc(v___y_2756_);
v___x_2763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2756_);
lean_ctor_set(v___x_2763_, 1, v___x_2463_);
lean_ctor_set(v___x_2763_, 2, v___x_2762_);
if (lean_obj_tag(v___y_2754_) == 1)
{
lean_object* v_val_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_val_2764_ = lean_ctor_get(v___y_2754_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___y_2754_, 1);
v___x_2765_ = l_Lean_SourceInfo_fromRef(v_val_2764_, v___x_2373_);
lean_dec(v_val_2764_);
v___x_2766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = l_Array_mkArray1___redArg(v___x_2767_);
v___y_2721_ = v___y_2749_;
v___y_2722_ = v___y_2750_;
v___y_2723_ = v___y_2751_;
v___y_2724_ = v___y_2752_;
v___y_2725_ = v___y_2753_;
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
lean_dec(v___y_2754_);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_2721_ = v___y_2749_;
v___y_2722_ = v___y_2750_;
v___y_2723_ = v___y_2751_;
v___y_2724_ = v___y_2752_;
v___y_2725_ = v___y_2753_;
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
if (v___y_2780_ == 0)
{
if (v_useReducible_2376_ == 0)
{
lean_dec(v___x_2375_);
lean_dec(v___x_2374_);
if (lean_obj_tag(v___y_2781_) == 0)
{
lean_dec(v___y_2785_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___y_2436_ = v___y_2773_;
v___y_2437_ = v___y_2779_;
v___y_2438_ = v___y_2782_;
v___y_2439_ = v___y_2776_;
v___y_2440_ = v___y_2783_;
v___y_2441_ = v___y_2774_;
v___y_2442_ = v___y_2784_;
v___y_2443_ = v___y_2771_;
v___y_2444_ = v___y_2772_;
goto v___jp_2435_;
}
else
{
lean_object* v_val_2786_; lean_object* v___x_2787_; 
v_val_2786_ = lean_ctor_get(v___y_2781_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v___y_2781_, 1);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
v___x_2787_ = lean_apply_9(v___f_2377_, v___y_2779_, v___y_2782_, v___y_2776_, v___y_2783_, v___y_2774_, v___y_2784_, v___y_2771_, v___y_2772_, lean_box(0));
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
v___y_2750_ = v___x_2791_;
v___y_2751_ = v___x_2794_;
v___y_2752_ = v___y_2772_;
v___y_2753_ = v___y_2773_;
v___y_2754_ = v___y_2775_;
v___y_2755_ = v___x_2792_;
v___y_2756_ = v_a_2788_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___x_2790_;
v___y_2760_ = v_val_2786_;
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
v___y_2750_ = v___x_2791_;
v___y_2751_ = v___x_2794_;
v___y_2752_ = v___y_2772_;
v___y_2753_ = v___y_2773_;
v___y_2754_ = v___y_2775_;
v___y_2755_ = v___x_2792_;
v___y_2756_ = v_a_2788_;
v___y_2757_ = v___y_2777_;
v___y_2758_ = v___y_2778_;
v___y_2759_ = v___x_2790_;
v___y_2760_ = v_val_2786_;
v___y_2761_ = v___x_2798_;
goto v___jp_2748_;
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_val_2786_);
lean_dec(v___y_2785_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
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
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
v___x_2807_ = lean_apply_9(v___f_2377_, v___y_2779_, v___y_2782_, v___y_2776_, v___y_2783_, v___y_2774_, v___y_2784_, v___y_2771_, v___y_2772_, lean_box(0));
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
v___y_2681_ = v_a_2808_;
v___y_2682_ = v___y_2771_;
v___y_2683_ = v___x_2810_;
v___y_2684_ = v___y_2777_;
v___y_2685_ = v___y_2778_;
v___y_2686_ = v___y_2781_;
v___y_2687_ = v___y_2772_;
v___y_2688_ = v___x_2809_;
v___y_2689_ = v___y_2773_;
v___y_2690_ = v___y_2775_;
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
v___y_2681_ = v_a_2808_;
v___y_2682_ = v___y_2771_;
v___y_2683_ = v___x_2810_;
v___y_2684_ = v___y_2777_;
v___y_2685_ = v___y_2778_;
v___y_2686_ = v___y_2781_;
v___y_2687_ = v___y_2772_;
v___y_2688_ = v___x_2809_;
v___y_2689_ = v___y_2773_;
v___y_2690_ = v___y_2775_;
v___y_2691_ = v___x_2814_;
goto v___jp_2680_;
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v___y_2785_);
lean_dec(v___y_2781_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
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
if (lean_obj_tag(v___y_2781_) == 0)
{
lean_dec(v___y_2785_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec_ref(v___x_2378_);
lean_dec_ref(v___f_2377_);
lean_dec(v___x_2372_);
lean_dec_ref(v___x_2371_);
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___x_2369_);
v___y_2436_ = v___y_2773_;
v___y_2437_ = v___y_2779_;
v___y_2438_ = v___y_2782_;
v___y_2439_ = v___y_2776_;
v___y_2440_ = v___y_2783_;
v___y_2441_ = v___y_2774_;
v___y_2442_ = v___y_2784_;
v___y_2443_ = v___y_2771_;
v___y_2444_ = v___y_2772_;
goto v___jp_2435_;
}
else
{
lean_object* v_val_2823_; lean_object* v___x_2824_; 
v_val_2823_ = lean_ctor_get(v___y_2781_, 0);
lean_inc(v_val_2823_);
lean_dec_ref_known(v___y_2781_, 1);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
v___x_2824_ = lean_apply_9(v___f_2377_, v___y_2779_, v___y_2782_, v___y_2776_, v___y_2783_, v___y_2774_, v___y_2784_, v___y_2771_, v___y_2772_, lean_box(0));
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
v___y_2597_ = v___y_2771_;
v___y_2598_ = v_val_2823_;
v___y_2599_ = v_a_2825_;
v___y_2600_ = v___x_2828_;
v___y_2601_ = v___y_2772_;
v___y_2602_ = v___y_2773_;
v___y_2603_ = v___y_2775_;
v___y_2604_ = v___x_2834_;
v___y_2605_ = v___y_2777_;
v___y_2606_ = v___x_2827_;
v___y_2607_ = v___y_2778_;
v___y_2608_ = v___x_2832_;
v___y_2609_ = v___x_2829_;
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
v___y_2597_ = v___y_2771_;
v___y_2598_ = v_val_2823_;
v___y_2599_ = v_a_2825_;
v___y_2600_ = v___x_2828_;
v___y_2601_ = v___y_2772_;
v___y_2602_ = v___y_2773_;
v___y_2603_ = v___y_2775_;
v___y_2604_ = v___x_2834_;
v___y_2605_ = v___y_2777_;
v___y_2606_ = v___x_2827_;
v___y_2607_ = v___y_2778_;
v___y_2608_ = v___x_2832_;
v___y_2609_ = v___x_2829_;
v___y_2610_ = v___x_2838_;
goto v___jp_2596_;
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_val_2823_);
lean_dec(v___y_2785_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
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
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
v___x_2847_ = lean_apply_9(v___f_2377_, v___y_2779_, v___y_2782_, v___y_2776_, v___y_2783_, v___y_2774_, v___y_2784_, v___y_2771_, v___y_2772_, lean_box(0));
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
v___y_2527_ = v___y_2771_;
v___y_2528_ = v___y_2777_;
v___y_2529_ = v___y_2778_;
v___y_2530_ = v___y_2781_;
v___y_2531_ = v___x_2852_;
v___y_2532_ = v___y_2772_;
v___y_2533_ = v_a_2848_;
v___y_2534_ = v___y_2773_;
v___y_2535_ = v___y_2775_;
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
v___y_2527_ = v___y_2771_;
v___y_2528_ = v___y_2777_;
v___y_2529_ = v___y_2778_;
v___y_2530_ = v___y_2781_;
v___y_2531_ = v___x_2852_;
v___y_2532_ = v___y_2772_;
v___y_2533_ = v_a_2848_;
v___y_2534_ = v___y_2773_;
v___y_2535_ = v___y_2775_;
v___y_2536_ = v___x_2850_;
v___y_2537_ = v___x_2856_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v___y_2785_);
lean_dec(v___y_2781_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
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
v___x_2883_ = l_Lean_Syntax_getArg(v___y_2872_, v___x_2882_);
lean_dec(v___y_2872_);
v___x_2884_ = l_Lean_Syntax_matchesNull(v___x_2883_, v___x_2372_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v_args_2873_);
lean_dec(v___y_2871_);
lean_dec(v___y_2870_);
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
v___y_2430_ = v___y_2869_;
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
lean_dec_ref(v___y_2869_);
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
v___x_2896_ = l_Lean_Syntax_getOptional_x3f(v___y_2871_);
lean_dec(v___y_2871_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_box(0);
v___y_2771_ = v___y_2880_;
v___y_2772_ = v___y_2881_;
v___y_2773_ = v___y_2869_;
v___y_2774_ = v___y_2878_;
v___y_2775_ = v___y_2870_;
v___y_2776_ = v___y_2876_;
v___y_2777_ = v___y_2866_;
v___y_2778_ = v_args_2873_;
v___y_2779_ = v___y_2874_;
v___y_2780_ = v___y_2868_;
v___y_2781_ = v___y_2867_;
v___y_2782_ = v___y_2875_;
v___y_2783_ = v___y_2877_;
v___y_2784_ = v___y_2879_;
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
v___y_2771_ = v___y_2880_;
v___y_2772_ = v___y_2881_;
v___y_2773_ = v___y_2869_;
v___y_2774_ = v___y_2878_;
v___y_2775_ = v___y_2870_;
v___y_2776_ = v___y_2876_;
v___y_2777_ = v___y_2866_;
v___y_2778_ = v_args_2873_;
v___y_2779_ = v___y_2874_;
v___y_2780_ = v___y_2868_;
v___y_2781_ = v___y_2867_;
v___y_2782_ = v___y_2875_;
v___y_2783_ = v___y_2877_;
v___y_2784_ = v___y_2879_;
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
v___x_2922_ = l_Lean_Syntax_getArg(v___y_2912_, v___x_2379_);
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
lean_dec(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v___y_2909_);
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
v___y_2430_ = v___y_2910_;
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
lean_dec_ref(v___y_2910_);
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
v___y_2867_ = v___y_2909_;
v___y_2868_ = v___y_2908_;
v___y_2869_ = v___y_2910_;
v___y_2870_ = v_only_2913_;
v___y_2871_ = v___y_2911_;
v___y_2872_ = v___y_2912_;
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
v___y_2867_ = v___y_2909_;
v___y_2868_ = v___y_2908_;
v___y_2869_ = v___y_2910_;
v___y_2870_ = v_only_2913_;
v___y_2871_ = v___y_2911_;
v___y_2872_ = v___y_2912_;
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
v_usedTheorems_2945_ = lean_ctor_get(v___y_2942_, 0);
v___x_2946_ = l_Lean_Syntax_unsetTrailing(v___y_2943_);
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
v___y_2407_ = v___y_2942_;
v_stx_2408_ = v_a_2952_;
v___y_2409_ = v___y_2399_;
v_ref_2410_ = v_ref_2457_;
v___y_2411_ = v___y_2400_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v___y_2942_);
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
v___y_2407_ = v___y_2942_;
v_stx_2408_ = v_a_2965_;
v___y_2409_ = v___y_2399_;
v_ref_2410_ = v_ref_2457_;
v___y_2411_ = v___y_2400_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v___y_2942_);
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
v___y_2407_ = v___y_2942_;
v_stx_2408_ = v_a_2980_;
v___y_2409_ = v___y_2399_;
v_ref_2410_ = v_ref_2457_;
v___y_2411_ = v___y_2400_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v___y_2942_);
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
v___y_2907_ = v___x_2961_;
v___y_2908_ = v___y_2941_;
v___y_2909_ = v___y_2944_;
v___y_2910_ = v___y_2942_;
v___y_2911_ = v___x_2974_;
v___y_2912_ = v_a_2948_;
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
v___y_2907_ = v___x_2961_;
v___y_2908_ = v___y_2941_;
v___y_2909_ = v___y_2944_;
v___y_2910_ = v___y_2942_;
v___y_2911_ = v___x_2974_;
v___y_2912_ = v_a_2948_;
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
lean_dec_ref(v___y_2942_);
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
v___y_2942_ = v___y_3002_;
v___y_2943_ = v___y_3003_;
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
v___y_2942_ = v___y_3002_;
v___y_2943_ = v___y_3003_;
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
lean_dec(v___y_3016_);
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
v___y_2403_ = v___y_3015_;
goto v___jp_2402_;
}
else
{
v___y_3001_ = v___y_3014_;
v___y_3002_ = v___y_3015_;
v___y_3003_ = v___y_3016_;
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
v___x_3030_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3021_, v___f_3029_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_3021_);
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
v___y_3015_ = v_a_3031_;
v___y_3016_ = v___y_3022_;
v___y_3017_ = v___x_3033_;
goto v___jp_3013_;
}
else
{
v___y_3014_ = v___y_3020_;
v___y_3015_ = v_a_3031_;
v___y_3016_ = v___y_3022_;
v___y_3017_ = v___x_2386_;
goto v___jp_3013_;
}
}
else
{
v___y_3001_ = v___y_3020_;
v___y_3002_ = v_a_3031_;
v___y_3003_ = v___y_3022_;
goto v___jp_3000_;
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v___y_3022_);
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
v___x_3049_ = l_Lean_Syntax_node6(v___x_2459_, v___x_2461_, v___x_2462_, v___x_2385_, v___y_3043_, v___y_3044_, v___x_3047_, v___x_3048_);
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
v___y_3020_ = v___x_2458_;
v___y_3021_ = v_dischargeWrapper_3060_;
v___y_3022_ = v___x_3049_;
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
v___y_3020_ = v___x_2386_;
v___y_3021_ = v_dischargeWrapper_3063_;
v___y_3022_ = v___x_3049_;
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
v___y_3020_ = v___x_2386_;
v___y_3021_ = v_dischargeWrapper_3066_;
v___y_3022_ = v___x_3049_;
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
v___y_3043_ = v___y_3077_;
v___y_3044_ = v___x_3080_;
v___y_3045_ = v___x_3088_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_mk_empty_array_with_capacity(v___x_2372_);
v___y_3043_ = v___y_3077_;
v___y_3044_ = v___x_3080_;
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
uint8_t v___x_97845__boxed_3138_; uint8_t v_useReducible_boxed_3139_; uint8_t v___x_97856__boxed_3140_; lean_object* v_res_3141_; 
v___x_97845__boxed_3138_ = lean_unbox(v___x_3109_);
v_useReducible_boxed_3139_ = lean_unbox(v_useReducible_3112_);
v___x_97856__boxed_3140_ = lean_unbox(v___x_3122_);
v_res_3141_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3104_, v___x_3105_, v___x_3106_, v___x_3107_, v___x_3108_, v___x_97845__boxed_3138_, v___x_3110_, v___x_3111_, v_useReducible_boxed_3139_, v___f_3113_, v___x_3114_, v___x_3115_, v___x_3116_, v___x_3117_, v___x_3118_, v___x_3119_, v_usingArg_3120_, v___x_3121_, v___x_97856__boxed_3140_, v_usingTk_x3f_3123_, v_squeeze_3124_, v_unfold_3125_, v_args_3126_, v_only_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3167_, lean_object* v_stx_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_3179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_3181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3168_);
v___x_3183_ = l_Lean_Syntax_isOfKind(v_stx_3168_, v___x_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
lean_dec(v_stx_3168_);
v___x_3184_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3184_;
}
else
{
lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v_tk_3187_; lean_object* v___x_3188_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; uint8_t v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; uint8_t v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v_usingTk_x3f_3239_; lean_object* v_usingArg_3240_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v_args_3272_; lean_object* v___y_3284_; lean_object* v___y_3285_; uint8_t v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v_only_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v_unfold_3328_; lean_object* v_squeeze_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___f_3185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3186_ = lean_unsigned_to_nat(0u);
v_tk_3187_ = l_Lean_Syntax_getArg(v_stx_3168_, v___x_3186_);
v___x_3188_ = lean_unsigned_to_nat(1u);
v___x_3364_ = l_Lean_Syntax_getArg(v_stx_3168_, v___x_3188_);
v___x_3365_ = l_Lean_Syntax_isNone(v___x_3364_);
if (v___x_3365_ == 0)
{
uint8_t v___x_3366_; 
lean_inc(v___x_3364_);
v___x_3366_ = l_Lean_Syntax_matchesNull(v___x_3364_, v___x_3188_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; 
lean_dec(v___x_3364_);
lean_dec(v_tk_3187_);
lean_dec(v_stx_3168_);
v___x_3367_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3367_;
}
else
{
lean_object* v_squeeze_3368_; lean_object* v___x_3369_; 
v_squeeze_3368_ = l_Lean_Syntax_getArg(v___x_3364_, v___x_3186_);
lean_dec(v___x_3364_);
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_squeeze_3368_);
v_squeeze_3347_ = v___x_3369_;
v___y_3348_ = v_a_3169_;
v___y_3349_ = v_a_3170_;
v___y_3350_ = v_a_3171_;
v___y_3351_ = v_a_3172_;
v___y_3352_ = v_a_3173_;
v___y_3353_ = v_a_3174_;
v___y_3354_ = v_a_3175_;
v___y_3355_ = v_a_3176_;
goto v___jp_3346_;
}
}
else
{
lean_object* v___x_3370_; 
lean_dec(v___x_3364_);
v___x_3370_ = lean_box(0);
v_squeeze_3347_ = v___x_3370_;
v___y_3348_ = v_a_3169_;
v___y_3349_ = v_a_3170_;
v___y_3350_ = v_a_3171_;
v___y_3351_ = v_a_3172_;
v___y_3352_ = v_a_3173_;
v___y_3353_ = v_a_3174_;
v___y_3354_ = v_a_3175_;
v___y_3355_ = v_a_3176_;
goto v___jp_3346_;
}
v___jp_3189_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___f_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3212_ = lean_box(v___x_3183_);
v___x_3213_ = lean_box(v_useReducible_3167_);
v___x_3214_ = lean_box(v___y_3206_);
lean_inc(v___y_3208_);
lean_inc(v___y_3203_);
v___f_3215_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3215_, 0, v_tk_3187_);
lean_closure_set(v___f_3215_, 1, v___x_3178_);
lean_closure_set(v___f_3215_, 2, v___x_3179_);
lean_closure_set(v___f_3215_, 3, v___x_3180_);
lean_closure_set(v___f_3215_, 4, v___x_3186_);
lean_closure_set(v___f_3215_, 5, v___x_3212_);
lean_closure_set(v___f_3215_, 6, v___y_3203_);
lean_closure_set(v___f_3215_, 7, v___x_3182_);
lean_closure_set(v___f_3215_, 8, v___x_3213_);
lean_closure_set(v___f_3215_, 9, v___f_3185_);
lean_closure_set(v___f_3215_, 10, v___x_3181_);
lean_closure_set(v___f_3215_, 11, v___y_3207_);
lean_closure_set(v___f_3215_, 12, v___y_3190_);
lean_closure_set(v___f_3215_, 13, v___x_3188_);
lean_closure_set(v___f_3215_, 14, v___y_3208_);
lean_closure_set(v___f_3215_, 15, v___y_3192_);
lean_closure_set(v___f_3215_, 16, v___y_3205_);
lean_closure_set(v___f_3215_, 17, v___y_3198_);
lean_closure_set(v___f_3215_, 18, v___x_3214_);
lean_closure_set(v___f_3215_, 19, v___y_3196_);
lean_closure_set(v___f_3215_, 20, v___y_3200_);
lean_closure_set(v___f_3215_, 21, v___y_3201_);
lean_closure_set(v___f_3215_, 22, v___y_3193_);
lean_closure_set(v___f_3215_, 23, v___y_3199_);
lean_closure_set(v___f_3215_, 24, v___y_3211_);
v___x_3216_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3216_, 0, v___f_3215_);
v___x_3217_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3216_, v___y_3204_, v___y_3210_, v___y_3195_, v___y_3202_, v___y_3191_, v___y_3197_, v___y_3209_, v___y_3194_);
return v___x_3217_;
}
v___jp_3218_:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Syntax_getOptional_x3f(v___y_3232_);
lean_dec(v___y_3232_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_box(0);
v___y_3190_ = v___y_3219_;
v___y_3191_ = v___y_3220_;
v___y_3192_ = v___y_3221_;
v___y_3193_ = v___y_3222_;
v___y_3194_ = v___y_3223_;
v___y_3195_ = v___y_3224_;
v___y_3196_ = v_usingTk_x3f_3239_;
v___y_3197_ = v___y_3225_;
v___y_3198_ = v___y_3226_;
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3229_;
v___y_3202_ = v___y_3230_;
v___y_3203_ = v___y_3231_;
v___y_3204_ = v___y_3233_;
v___y_3205_ = v_usingArg_3240_;
v___y_3206_ = v___y_3234_;
v___y_3207_ = v___y_3236_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3238_;
v___y_3211_ = v___x_3242_;
goto v___jp_3189_;
}
else
{
lean_object* v_val_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
v_val_3243_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3241_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_val_3243_);
lean_dec(v___x_3241_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_val_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
v___y_3190_ = v___y_3219_;
v___y_3191_ = v___y_3220_;
v___y_3192_ = v___y_3221_;
v___y_3193_ = v___y_3222_;
v___y_3194_ = v___y_3223_;
v___y_3195_ = v___y_3224_;
v___y_3196_ = v_usingTk_x3f_3239_;
v___y_3197_ = v___y_3225_;
v___y_3198_ = v___y_3226_;
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3229_;
v___y_3202_ = v___y_3230_;
v___y_3203_ = v___y_3231_;
v___y_3204_ = v___y_3233_;
v___y_3205_ = v_usingArg_3240_;
v___y_3206_ = v___y_3234_;
v___y_3207_ = v___y_3236_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3238_;
v___y_3211_ = v___x_3248_;
goto v___jp_3189_;
}
}
}
}
v___jp_3251_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3273_ = lean_unsigned_to_nat(4u);
v___x_3274_ = l_Lean_Syntax_getArg(v___y_3257_, v___x_3273_);
lean_dec(v___y_3257_);
v___x_3275_ = l_Lean_Syntax_isNone(v___x_3274_);
if (v___x_3275_ == 0)
{
uint8_t v___x_3276_; 
lean_inc(v___x_3274_);
v___x_3276_ = l_Lean_Syntax_matchesNull(v___x_3274_, v___y_3261_);
lean_dec(v___y_3261_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; 
lean_dec(v___x_3274_);
lean_dec(v_args_3272_);
lean_dec(v___y_3266_);
lean_dec(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3254_);
lean_dec(v___y_3252_);
lean_dec(v_tk_3187_);
v___x_3277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3277_;
}
else
{
lean_object* v_usingTk_x3f_3278_; lean_object* v_usingArg_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_usingTk_x3f_3278_ = l_Lean_Syntax_getArg(v___x_3274_, v___x_3186_);
v_usingArg_3279_ = l_Lean_Syntax_getArg(v___x_3274_, v___x_3188_);
lean_dec(v___x_3274_);
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_usingTk_x3f_3278_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_usingArg_3279_);
v___y_3219_ = v___y_3252_;
v___y_3220_ = v___y_3253_;
v___y_3221_ = v___y_3254_;
v___y_3222_ = v_args_3272_;
v___y_3223_ = v___y_3255_;
v___y_3224_ = v___y_3256_;
v___y_3225_ = v___y_3258_;
v___y_3226_ = v___y_3259_;
v___y_3227_ = v___y_3260_;
v___y_3228_ = v___y_3262_;
v___y_3229_ = v___y_3263_;
v___y_3230_ = v___y_3264_;
v___y_3231_ = v___y_3265_;
v___y_3232_ = v___y_3266_;
v___y_3233_ = v___y_3267_;
v___y_3234_ = v___y_3268_;
v___y_3235_ = v___y_3269_;
v___y_3236_ = v___x_3273_;
v___y_3237_ = v___y_3270_;
v___y_3238_ = v___y_3271_;
v_usingTk_x3f_3239_ = v___x_3280_;
v_usingArg_3240_ = v___x_3281_;
goto v___jp_3218_;
}
}
else
{
lean_object* v___x_3282_; 
lean_dec(v___x_3274_);
lean_dec(v___y_3261_);
v___x_3282_ = lean_box(0);
v___y_3219_ = v___y_3252_;
v___y_3220_ = v___y_3253_;
v___y_3221_ = v___y_3254_;
v___y_3222_ = v_args_3272_;
v___y_3223_ = v___y_3255_;
v___y_3224_ = v___y_3256_;
v___y_3225_ = v___y_3258_;
v___y_3226_ = v___y_3259_;
v___y_3227_ = v___y_3260_;
v___y_3228_ = v___y_3262_;
v___y_3229_ = v___y_3263_;
v___y_3230_ = v___y_3264_;
v___y_3231_ = v___y_3265_;
v___y_3232_ = v___y_3266_;
v___y_3233_ = v___y_3267_;
v___y_3234_ = v___y_3268_;
v___y_3235_ = v___y_3269_;
v___y_3236_ = v___x_3273_;
v___y_3237_ = v___y_3270_;
v___y_3238_ = v___y_3271_;
v_usingTk_x3f_3239_ = v___x_3282_;
v_usingArg_3240_ = v___x_3282_;
goto v___jp_3218_;
}
}
v___jp_3283_:
{
lean_object* v___x_3305_; uint8_t v___x_3306_; 
v___x_3305_ = l_Lean_Syntax_getArg(v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
v___x_3306_ = l_Lean_Syntax_isNone(v___x_3305_);
if (v___x_3306_ == 0)
{
uint8_t v___x_3307_; 
lean_inc(v___x_3305_);
v___x_3307_ = l_Lean_Syntax_matchesNull(v___x_3305_, v___x_3188_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_dec(v___x_3305_);
lean_dec(v_only_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec(v_tk_3187_);
v___x_3308_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3308_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3309_ = l_Lean_Syntax_getArg(v___x_3305_, v___x_3186_);
lean_dec(v___x_3305_);
v___x_3310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3309_);
v___x_3311_ = l_Lean_Syntax_isOfKind(v___x_3309_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; 
lean_dec(v___x_3309_);
lean_dec(v_only_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v___y_3292_);
lean_dec(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec(v_tk_3187_);
v___x_3312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3312_;
}
else
{
lean_object* v___x_3313_; lean_object* v_args_3314_; lean_object* v___x_3315_; 
v___x_3313_ = l_Lean_Syntax_getArg(v___x_3309_, v___x_3188_);
lean_dec(v___x_3309_);
v_args_3314_ = l_Lean_Syntax_getArgs(v___x_3313_);
lean_dec(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3315_, 0, v_args_3314_);
v___y_3252_ = v___y_3284_;
v___y_3253_ = v___y_3301_;
v___y_3254_ = v___y_3285_;
v___y_3255_ = v___y_3304_;
v___y_3256_ = v___y_3299_;
v___y_3257_ = v___y_3292_;
v___y_3258_ = v___y_3302_;
v___y_3259_ = v___y_3288_;
v___y_3260_ = v_only_3296_;
v___y_3261_ = v___y_3294_;
v___y_3262_ = v___y_3289_;
v___y_3263_ = v___y_3290_;
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___y_3291_;
v___y_3266_ = v___y_3295_;
v___y_3267_ = v___y_3297_;
v___y_3268_ = v___y_3286_;
v___y_3269_ = v___y_3287_;
v___y_3270_ = v___y_3303_;
v___y_3271_ = v___y_3298_;
v_args_3272_ = v___x_3315_;
goto v___jp_3251_;
}
}
}
else
{
lean_object* v___x_3316_; 
lean_dec(v___x_3305_);
v___x_3316_ = lean_box(0);
v___y_3252_ = v___y_3284_;
v___y_3253_ = v___y_3301_;
v___y_3254_ = v___y_3285_;
v___y_3255_ = v___y_3304_;
v___y_3256_ = v___y_3299_;
v___y_3257_ = v___y_3292_;
v___y_3258_ = v___y_3302_;
v___y_3259_ = v___y_3288_;
v___y_3260_ = v_only_3296_;
v___y_3261_ = v___y_3294_;
v___y_3262_ = v___y_3289_;
v___y_3263_ = v___y_3290_;
v___y_3264_ = v___y_3300_;
v___y_3265_ = v___y_3291_;
v___y_3266_ = v___y_3295_;
v___y_3267_ = v___y_3297_;
v___y_3268_ = v___y_3286_;
v___y_3269_ = v___y_3287_;
v___y_3270_ = v___y_3303_;
v___y_3271_ = v___y_3298_;
v_args_3272_ = v___x_3316_;
goto v___jp_3251_;
}
}
v___jp_3317_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3329_ = lean_unsigned_to_nat(3u);
v___x_3330_ = l_Lean_Syntax_getArg(v_stx_3168_, v___x_3329_);
lean_dec(v_stx_3168_);
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3330_);
v___x_3332_ = l_Lean_Syntax_isOfKind(v___x_3330_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_dec(v___x_3330_);
lean_dec(v_unfold_3328_);
lean_dec(v___y_3322_);
lean_dec(v___y_3318_);
lean_dec(v_tk_3187_);
v___x_3333_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3333_;
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3334_ = l_Lean_Syntax_getArg(v___x_3330_, v___x_3186_);
v___x_3335_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3334_);
v___x_3336_ = l_Lean_Syntax_isOfKind(v___x_3334_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
lean_dec(v___x_3334_);
lean_dec(v___x_3330_);
lean_dec(v_unfold_3328_);
lean_dec(v___y_3322_);
lean_dec(v___y_3318_);
lean_dec(v_tk_3187_);
v___x_3337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3337_;
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3338_ = l_Lean_Syntax_getArg(v___x_3330_, v___x_3188_);
v___x_3339_ = l_Lean_Syntax_getArg(v___x_3330_, v___y_3318_);
v___x_3340_ = l_Lean_Syntax_isNone(v___x_3339_);
if (v___x_3340_ == 0)
{
uint8_t v___x_3341_; 
lean_inc(v___x_3339_);
v___x_3341_ = l_Lean_Syntax_matchesNull(v___x_3339_, v___x_3188_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; 
lean_dec(v___x_3339_);
lean_dec(v___x_3338_);
lean_dec(v___x_3334_);
lean_dec(v___x_3330_);
lean_dec(v_unfold_3328_);
lean_dec(v___y_3322_);
lean_dec(v___y_3318_);
lean_dec(v_tk_3187_);
v___x_3342_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3342_;
}
else
{
lean_object* v_only_3343_; lean_object* v___x_3344_; 
v_only_3343_ = l_Lean_Syntax_getArg(v___x_3339_, v___x_3186_);
lean_dec(v___x_3339_);
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_only_3343_);
lean_inc(v___y_3318_);
v___y_3284_ = v___x_3329_;
v___y_3285_ = v___y_3318_;
v___y_3286_ = v___x_3336_;
v___y_3287_ = v___x_3335_;
v___y_3288_ = v___x_3334_;
v___y_3289_ = v___y_3322_;
v___y_3290_ = v_unfold_3328_;
v___y_3291_ = v___x_3331_;
v___y_3292_ = v___x_3330_;
v___y_3293_ = v___x_3329_;
v___y_3294_ = v___y_3318_;
v___y_3295_ = v___x_3338_;
v_only_3296_ = v___x_3344_;
v___y_3297_ = v___y_3324_;
v___y_3298_ = v___y_3323_;
v___y_3299_ = v___y_3321_;
v___y_3300_ = v___y_3320_;
v___y_3301_ = v___y_3327_;
v___y_3302_ = v___y_3326_;
v___y_3303_ = v___y_3325_;
v___y_3304_ = v___y_3319_;
goto v___jp_3283_;
}
}
else
{
lean_object* v___x_3345_; 
lean_dec(v___x_3339_);
v___x_3345_ = lean_box(0);
lean_inc(v___y_3318_);
v___y_3284_ = v___x_3329_;
v___y_3285_ = v___y_3318_;
v___y_3286_ = v___x_3336_;
v___y_3287_ = v___x_3335_;
v___y_3288_ = v___x_3334_;
v___y_3289_ = v___y_3322_;
v___y_3290_ = v_unfold_3328_;
v___y_3291_ = v___x_3331_;
v___y_3292_ = v___x_3330_;
v___y_3293_ = v___x_3329_;
v___y_3294_ = v___y_3318_;
v___y_3295_ = v___x_3338_;
v_only_3296_ = v___x_3345_;
v___y_3297_ = v___y_3324_;
v___y_3298_ = v___y_3323_;
v___y_3299_ = v___y_3321_;
v___y_3300_ = v___y_3320_;
v___y_3301_ = v___y_3327_;
v___y_3302_ = v___y_3326_;
v___y_3303_ = v___y_3325_;
v___y_3304_ = v___y_3319_;
goto v___jp_3283_;
}
}
}
}
v___jp_3346_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3356_ = lean_unsigned_to_nat(2u);
v___x_3357_ = l_Lean_Syntax_getArg(v_stx_3168_, v___x_3356_);
v___x_3358_ = l_Lean_Syntax_isNone(v___x_3357_);
if (v___x_3358_ == 0)
{
uint8_t v___x_3359_; 
lean_inc(v___x_3357_);
v___x_3359_ = l_Lean_Syntax_matchesNull(v___x_3357_, v___x_3188_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_dec(v___x_3357_);
lean_dec(v_squeeze_3347_);
lean_dec(v_tk_3187_);
lean_dec(v_stx_3168_);
v___x_3360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3360_;
}
else
{
lean_object* v_unfold_3361_; lean_object* v___x_3362_; 
v_unfold_3361_ = l_Lean_Syntax_getArg(v___x_3357_, v___x_3186_);
lean_dec(v___x_3357_);
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_unfold_3361_);
v___y_3318_ = v___x_3356_;
v___y_3319_ = v___y_3355_;
v___y_3320_ = v___y_3351_;
v___y_3321_ = v___y_3350_;
v___y_3322_ = v_squeeze_3347_;
v___y_3323_ = v___y_3349_;
v___y_3324_ = v___y_3348_;
v___y_3325_ = v___y_3354_;
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3352_;
v_unfold_3328_ = v___x_3362_;
goto v___jp_3317_;
}
}
else
{
lean_object* v___x_3363_; 
lean_dec(v___x_3357_);
v___x_3363_ = lean_box(0);
v___y_3318_ = v___x_3356_;
v___y_3319_ = v___y_3355_;
v___y_3320_ = v___y_3351_;
v___y_3321_ = v___y_3350_;
v___y_3322_ = v_squeeze_3347_;
v___y_3323_ = v___y_3349_;
v___y_3324_ = v___y_3348_;
v___y_3325_ = v___y_3354_;
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3352_;
v_unfold_3328_ = v___x_3363_;
goto v___jp_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3371_, lean_object* v_stx_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
uint8_t v_useReducible_boxed_3382_; lean_object* v_res_3383_; 
v_useReducible_boxed_3382_ = lean_unbox(v_useReducible_3371_);
v_res_3383_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3382_, v_stx_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3384_, lean_object* v_val_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3384_, v_val_3385_, v___y_3391_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3396_, lean_object* v_val_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3396_, v_val_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3408_, v___y_3416_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v_00_u03b1_3430_, lean_object* v_msg_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_3431_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v_00_u03b1_3442_, lean_object* v_msg_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_3442_, v_msg_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_00_u03b1_3454_, lean_object* v_x_3455_, lean_object* v_mkInfoTree_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_3455_, v_mkInfoTree_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_00_u03b1_3467_, lean_object* v_x_3468_, lean_object* v_mkInfoTree_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_3467_, v_x_3468_, v_mkInfoTree_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3480_, lean_object* v_x_3481_, lean_object* v_x_3482_, lean_object* v_x_3483_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3481_, v_x_3482_, v_x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3485_, lean_object* v_m_3486_, lean_object* v_a_3487_){
_start:
{
uint8_t v___x_3488_; 
v___x_3488_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3486_, v_a_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3489_, lean_object* v_m_3490_, lean_object* v_a_3491_){
_start:
{
uint8_t v_res_3492_; lean_object* v_r_3493_; 
v_res_3492_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_3489_, v_m_3490_, v_a_3491_);
lean_dec_ref(v_a_3491_);
lean_dec_ref(v_m_3490_);
v_r_3493_ = lean_box(v_res_3492_);
return v_r_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3494_, lean_object* v_m_3495_, lean_object* v_a_3496_, lean_object* v_b_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_m_3495_, v_a_3496_, v_b_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3499_, v___y_3500_, v___y_3506_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(v_mvarId_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
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
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3523_, v___y_3524_, v___y_3530_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_mvarId_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v_mvarId_3535_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3547_, lean_object* v_x_3548_, size_t v_x_3549_, size_t v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_3548_, v_x_3549_, v_x_3550_, v_x_3551_, v_x_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3554_, lean_object* v_x_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_){
_start:
{
size_t v_x_100058__boxed_3560_; size_t v_x_100059__boxed_3561_; lean_object* v_res_3562_; 
v_x_100058__boxed_3560_ = lean_unbox_usize(v_x_3556_);
lean_dec(v_x_3556_);
v_x_100059__boxed_3561_ = lean_unbox_usize(v_x_3557_);
lean_dec(v_x_3557_);
v_res_3562_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_3554_, v_x_3555_, v_x_100058__boxed_3560_, v_x_100059__boxed_3561_, v_x_3558_, v_x_3559_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(lean_object* v_ref_3563_, lean_object* v_msgData_3564_, uint8_t v_severity_3565_, uint8_t v_isSilent_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_3563_, v_msgData_3564_, v_severity_3565_, v_isSilent_3566_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3577_, lean_object* v_msgData_3578_, lean_object* v_severity_3579_, lean_object* v_isSilent_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
uint8_t v_severity_boxed_3590_; uint8_t v_isSilent_boxed_3591_; lean_object* v_res_3592_; 
v_severity_boxed_3590_ = lean_unbox(v_severity_3579_);
v_isSilent_boxed_3591_ = lean_unbox(v_isSilent_3580_);
v_res_3592_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(v_ref_3577_, v_msgData_3578_, v_severity_boxed_3590_, v_isSilent_boxed_3591_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v_ref_3577_);
return v_res_3592_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3593_, lean_object* v_a_3594_, lean_object* v_x_3595_){
_start:
{
uint8_t v___x_3596_; 
v___x_3596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3594_, v_x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3597_, lean_object* v_a_3598_, lean_object* v_x_3599_){
_start:
{
uint8_t v_res_3600_; lean_object* v_r_3601_; 
v_res_3600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3597_, v_a_3598_, v_x_3599_);
lean_dec(v_x_3599_);
lean_dec_ref(v_a_3598_);
v_r_3601_ = lean_box(v_res_3600_);
return v_r_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3602_, lean_object* v_data_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3605_, lean_object* v_n_3606_, lean_object* v_k_3607_, lean_object* v_v_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3606_, v_k_3607_, v_v_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3610_, size_t v_depth_3611_, lean_object* v_keys_3612_, lean_object* v_vals_3613_, lean_object* v_heq_3614_, lean_object* v_i_3615_, lean_object* v_entries_3616_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3611_, v_keys_3612_, v_vals_3613_, v_i_3615_, v_entries_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3618_, lean_object* v_depth_3619_, lean_object* v_keys_3620_, lean_object* v_vals_3621_, lean_object* v_heq_3622_, lean_object* v_i_3623_, lean_object* v_entries_3624_){
_start:
{
size_t v_depth_boxed_3625_; lean_object* v_res_3626_; 
v_depth_boxed_3625_ = lean_unbox_usize(v_depth_3619_);
lean_dec(v_depth_3619_);
v_res_3626_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3618_, v_depth_boxed_3625_, v_keys_3620_, v_vals_3621_, v_heq_3622_, v_i_3623_, v_entries_3624_);
lean_dec_ref(v_vals_3621_);
lean_dec_ref(v_keys_3620_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3627_, lean_object* v_i_3628_, lean_object* v_source_3629_, lean_object* v_target_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3628_, v_source_3629_, v_target_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_, lean_object* v_x_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3633_, v_x_3634_, v_x_3635_, v_x_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3638_, lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3639_, v_x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
uint8_t v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = 1;
v___x_3653_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_3652_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3674_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3677_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3678_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3674_, v___x_3675_, v___x_3676_, v___x_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3709_ = l_Lean_addBuiltinDeclarationRanges(v___x_3707_, v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_3716_);
lean_dec(v_x_3716_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v___x_3770_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_3729_);
v___x_3771_ = l_Lean_Syntax_isOfKind(v_stx_3729_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; 
lean_dec(v_stx_3729_);
v___x_3772_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; uint8_t v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; uint8_t v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; uint8_t v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; uint8_t v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v_tk_3900_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v_args_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___x_3960_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v_only_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v_unfold_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v_squeeze_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v___x_3773_ = lean_unsigned_to_nat(0u);
v_tk_3900_ = l_Lean_Syntax_getArg(v_stx_3729_, v___x_3773_);
v___x_3960_ = lean_unsigned_to_nat(1u);
v___x_4036_ = l_Lean_Syntax_getArg(v_stx_3729_, v___x_3960_);
v___x_4037_ = l_Lean_Syntax_isNone(v___x_4036_);
if (v___x_4037_ == 0)
{
uint8_t v___x_4038_; 
lean_inc(v___x_4036_);
v___x_4038_ = l_Lean_Syntax_matchesNull(v___x_4036_, v___x_3960_);
if (v___x_4038_ == 0)
{
lean_object* v___x_4039_; 
lean_dec(v___x_4036_);
lean_dec(v_tk_3900_);
lean_dec(v_stx_3729_);
v___x_4039_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4039_;
}
else
{
lean_object* v_squeeze_4040_; lean_object* v___x_4041_; 
v_squeeze_4040_ = l_Lean_Syntax_getArg(v___x_4036_, v___x_3773_);
lean_dec(v___x_4036_);
v___x_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4041_, 0, v_squeeze_4040_);
v_squeeze_4019_ = v___x_4041_;
v___y_4020_ = v_a_3730_;
v___y_4021_ = v_a_3731_;
v___y_4022_ = v_a_3732_;
v___y_4023_ = v_a_3733_;
v___y_4024_ = v_a_3734_;
v___y_4025_ = v_a_3735_;
v___y_4026_ = v_a_3736_;
v___y_4027_ = v_a_3737_;
goto v___jp_4018_;
}
}
else
{
lean_object* v___x_4042_; 
lean_dec(v___x_4036_);
v___x_4042_ = lean_box(0);
v_squeeze_4019_ = v___x_4042_;
v___y_4020_ = v_a_3730_;
v___y_4021_ = v_a_3731_;
v___y_4022_ = v_a_3732_;
v___y_4023_ = v_a_3733_;
v___y_4024_ = v_a_3734_;
v___y_4025_ = v_a_3735_;
v___y_4026_ = v_a_3736_;
v___y_4027_ = v_a_3737_;
goto v___jp_4018_;
}
v___jp_3774_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_inc_ref(v___y_3787_);
v___x_3797_ = l_Array_append___redArg(v___y_3787_, v___y_3796_);
lean_dec_ref(v___y_3796_);
lean_inc(v___y_3781_);
lean_inc(v___y_3795_);
v___x_3798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3798_, 0, v___y_3795_);
lean_ctor_set(v___x_3798_, 1, v___y_3781_);
lean_ctor_set(v___x_3798_, 2, v___x_3797_);
if (lean_obj_tag(v___y_3783_) == 1)
{
lean_object* v_val_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v_val_3799_ = lean_ctor_get(v___y_3783_, 0);
lean_inc(v_val_3799_);
lean_dec_ref_known(v___y_3783_, 1);
v___x_3800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3795_, 4);
v___x_3802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___y_3795_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
lean_inc_ref(v___y_3787_);
v___x_3803_ = l_Array_append___redArg(v___y_3787_, v_val_3799_);
lean_dec(v_val_3799_);
lean_inc(v___y_3781_);
v___x_3804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3804_, 0, v___y_3795_);
lean_ctor_set(v___x_3804_, 1, v___y_3781_);
lean_ctor_set(v___x_3804_, 2, v___x_3803_);
v___x_3805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___y_3795_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = l_Lean_Syntax_node3(v___y_3795_, v___x_3800_, v___x_3802_, v___x_3804_, v___x_3806_);
v___x_3808_ = l_Array_mkArray1___redArg(v___x_3807_);
v___y_3740_ = v___y_3775_;
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3777_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3782_;
v___y_3748_ = v___x_3798_;
v___y_3749_ = v___y_3784_;
v___y_3750_ = v___y_3785_;
v___y_3751_ = v___y_3786_;
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3790_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3788_;
v___y_3756_ = v___y_3791_;
v___y_3757_ = v___y_3792_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3794_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v___x_3808_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3809_; 
lean_dec(v___y_3783_);
v___x_3809_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3740_ = v___y_3775_;
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3777_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3782_;
v___y_3748_ = v___x_3798_;
v___y_3749_ = v___y_3784_;
v___y_3750_ = v___y_3785_;
v___y_3751_ = v___y_3786_;
v___y_3752_ = v___y_3787_;
v___y_3753_ = v___y_3790_;
v___y_3754_ = v___y_3789_;
v___y_3755_ = v___y_3788_;
v___y_3756_ = v___y_3791_;
v___y_3757_ = v___y_3792_;
v___y_3758_ = v___y_3793_;
v___y_3759_ = v___y_3794_;
v___y_3760_ = v___y_3795_;
v___y_3761_ = v___x_3809_;
goto v___jp_3739_;
}
}
v___jp_3810_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_inc_ref(v___y_3824_);
v___x_3833_ = l_Array_append___redArg(v___y_3824_, v___y_3832_);
lean_dec_ref(v___y_3832_);
lean_inc(v___y_3817_);
lean_inc(v___y_3831_);
v___x_3834_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3834_, 0, v___y_3831_);
lean_ctor_set(v___x_3834_, 1, v___y_3817_);
lean_ctor_set(v___x_3834_, 2, v___x_3833_);
if (lean_obj_tag(v___y_3822_) == 1)
{
lean_object* v_val_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_val_3835_ = lean_ctor_get(v___y_3822_, 0);
lean_inc(v_val_3835_);
lean_dec_ref_known(v___y_3822_, 1);
v___x_3836_ = l_Lean_SourceInfo_fromRef(v_val_3835_, v___x_3771_);
lean_dec(v_val_3835_);
v___x_3837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3836_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = l_Array_mkArray1___redArg(v___x_3838_);
v___y_3775_ = v___y_3811_;
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3813_;
v___y_3778_ = v___y_3814_;
v___y_3779_ = v___y_3815_;
v___y_3780_ = v___y_3816_;
v___y_3781_ = v___y_3817_;
v___y_3782_ = v___y_3818_;
v___y_3783_ = v___y_3819_;
v___y_3784_ = v___y_3820_;
v___y_3785_ = v___y_3821_;
v___y_3786_ = v___y_3823_;
v___y_3787_ = v___y_3824_;
v___y_3788_ = v___y_3827_;
v___y_3789_ = v___y_3826_;
v___y_3790_ = v___y_3825_;
v___y_3791_ = v___y_3828_;
v___y_3792_ = v___y_3829_;
v___y_3793_ = v___x_3834_;
v___y_3794_ = v___y_3830_;
v___y_3795_ = v___y_3831_;
v___y_3796_ = v___x_3839_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3822_);
lean_dec(v___y_3822_);
v___y_3775_ = v___y_3811_;
v___y_3776_ = v___y_3812_;
v___y_3777_ = v___y_3813_;
v___y_3778_ = v___y_3814_;
v___y_3779_ = v___y_3815_;
v___y_3780_ = v___y_3816_;
v___y_3781_ = v___y_3817_;
v___y_3782_ = v___y_3818_;
v___y_3783_ = v___y_3819_;
v___y_3784_ = v___y_3820_;
v___y_3785_ = v___y_3821_;
v___y_3786_ = v___y_3823_;
v___y_3787_ = v___y_3824_;
v___y_3788_ = v___y_3827_;
v___y_3789_ = v___y_3826_;
v___y_3790_ = v___y_3825_;
v___y_3791_ = v___y_3828_;
v___y_3792_ = v___y_3829_;
v___y_3793_ = v___x_3834_;
v___y_3794_ = v___y_3830_;
v___y_3795_ = v___y_3831_;
v___y_3796_ = v___x_3840_;
goto v___jp_3774_;
}
}
v___jp_3841_:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_inc_ref(v___y_3853_);
v___x_3863_ = l_Array_append___redArg(v___y_3853_, v___y_3862_);
lean_dec_ref(v___y_3862_);
lean_inc(v___y_3847_);
lean_inc(v___y_3861_);
v___x_3864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3864_, 0, v___y_3861_);
lean_ctor_set(v___x_3864_, 1, v___y_3847_);
lean_ctor_set(v___x_3864_, 2, v___x_3863_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_3854_) == 0)
{
lean_object* v___x_3866_; 
v___x_3866_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3811_ = v___y_3842_;
v___y_3812_ = v___y_3843_;
v___y_3813_ = v___y_3844_;
v___y_3814_ = v___x_3864_;
v___y_3815_ = v___y_3845_;
v___y_3816_ = v___y_3846_;
v___y_3817_ = v___y_3847_;
v___y_3818_ = v___x_3865_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3850_;
v___y_3822_ = v___y_3851_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3853_;
v___y_3825_ = v___y_3857_;
v___y_3826_ = v___y_3856_;
v___y_3827_ = v___y_3855_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3859_;
v___y_3830_ = v___y_3860_;
v___y_3831_ = v___y_3861_;
v___y_3832_ = v___x_3866_;
goto v___jp_3810_;
}
else
{
lean_object* v_val_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_val_3867_ = lean_ctor_get(v___y_3854_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v___y_3854_, 1);
v___x_3868_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3869_ = lean_array_push(v___x_3868_, v_val_3867_);
v___y_3811_ = v___y_3842_;
v___y_3812_ = v___y_3843_;
v___y_3813_ = v___y_3844_;
v___y_3814_ = v___x_3864_;
v___y_3815_ = v___y_3845_;
v___y_3816_ = v___y_3846_;
v___y_3817_ = v___y_3847_;
v___y_3818_ = v___x_3865_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3850_;
v___y_3822_ = v___y_3851_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3853_;
v___y_3825_ = v___y_3857_;
v___y_3826_ = v___y_3856_;
v___y_3827_ = v___y_3855_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3859_;
v___y_3830_ = v___y_3860_;
v___y_3831_ = v___y_3861_;
v___y_3832_ = v___x_3869_;
goto v___jp_3810_;
}
}
v___jp_3870_:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_inc_ref(v___y_3881_);
v___x_3892_ = l_Array_append___redArg(v___y_3881_, v___y_3891_);
lean_dec_ref(v___y_3891_);
lean_inc(v___y_3877_);
lean_inc(v___y_3890_);
v___x_3893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3893_, 0, v___y_3890_);
lean_ctor_set(v___x_3893_, 1, v___y_3877_);
lean_ctor_set(v___x_3893_, 2, v___x_3892_);
if (lean_obj_tag(v___y_3876_) == 1)
{
lean_object* v_val_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v_val_3894_ = lean_ctor_get(v___y_3876_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v___y_3876_, 1);
v___x_3895_ = l_Lean_SourceInfo_fromRef(v_val_3894_, v___x_3771_);
lean_dec(v_val_3894_);
v___x_3896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_3897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = l_Array_mkArray1___redArg(v___x_3897_);
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___y_3875_;
v___y_3847_ = v___y_3877_;
v___y_3848_ = v___y_3878_;
v___y_3849_ = v___y_3879_;
v___y_3850_ = v___x_3893_;
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3882_;
v___y_3853_ = v___y_3881_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3886_;
v___y_3856_ = v___y_3885_;
v___y_3857_ = v___y_3884_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___y_3889_;
v___y_3861_ = v___y_3890_;
v___y_3862_ = v___x_3898_;
goto v___jp_3841_;
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3876_);
lean_dec(v___y_3876_);
v___y_3842_ = v___y_3871_;
v___y_3843_ = v___y_3872_;
v___y_3844_ = v___y_3873_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___y_3875_;
v___y_3847_ = v___y_3877_;
v___y_3848_ = v___y_3878_;
v___y_3849_ = v___y_3879_;
v___y_3850_ = v___x_3893_;
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3882_;
v___y_3853_ = v___y_3881_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3886_;
v___y_3856_ = v___y_3885_;
v___y_3857_ = v___y_3884_;
v___y_3858_ = v___y_3887_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v___y_3889_;
v___y_3861_ = v___y_3890_;
v___y_3862_ = v___x_3899_;
goto v___jp_3841_;
}
}
v___jp_3901_:
{
lean_object* v_ref_3917_; uint8_t v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v_ref_3917_ = lean_ctor_get(v___y_3910_, 5);
v___x_3918_ = 0;
v___x_3919_ = l_Lean_SourceInfo_fromRef(v_ref_3917_, v___x_3918_);
v___x_3920_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3922_ = l_Lean_SourceInfo_fromRef(v_tk_3900_, v___x_3771_);
lean_dec(v_tk_3900_);
v___x_3923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
lean_ctor_set(v___x_3923_, 1, v___x_3920_);
v___x_3924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_3925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_3914_) == 1)
{
lean_object* v_val_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_val_3926_ = lean_ctor_get(v___y_3914_, 0);
lean_inc(v_val_3926_);
lean_dec_ref_known(v___y_3914_, 1);
v___x_3927_ = l_Lean_SourceInfo_fromRef(v_val_3926_, v___x_3771_);
lean_dec(v_val_3926_);
v___x_3928_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_3929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = l_Array_mkArray1___redArg(v___x_3929_);
v___y_3871_ = v___y_3902_;
v___y_3872_ = v___x_3923_;
v___y_3873_ = v___y_3903_;
v___y_3874_ = v___y_3904_;
v___y_3875_ = v___y_3905_;
v___y_3876_ = v___y_3906_;
v___y_3877_ = v___x_3924_;
v___y_3878_ = v___y_3907_;
v___y_3879_ = v___x_3921_;
v___y_3880_ = v___y_3908_;
v___y_3881_ = v___x_3925_;
v___y_3882_ = v___y_3909_;
v___y_3883_ = v___y_3916_;
v___y_3884_ = v___y_3910_;
v___y_3885_ = v___y_3911_;
v___y_3886_ = v___x_3918_;
v___y_3887_ = v___y_3912_;
v___y_3888_ = v___y_3913_;
v___y_3889_ = v___y_3915_;
v___y_3890_ = v___x_3919_;
v___y_3891_ = v___x_3930_;
goto v___jp_3870_;
}
else
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3914_);
lean_dec(v___y_3914_);
v___y_3871_ = v___y_3902_;
v___y_3872_ = v___x_3923_;
v___y_3873_ = v___y_3903_;
v___y_3874_ = v___y_3904_;
v___y_3875_ = v___y_3905_;
v___y_3876_ = v___y_3906_;
v___y_3877_ = v___x_3924_;
v___y_3878_ = v___y_3907_;
v___y_3879_ = v___x_3921_;
v___y_3880_ = v___y_3908_;
v___y_3881_ = v___x_3925_;
v___y_3882_ = v___y_3909_;
v___y_3883_ = v___y_3916_;
v___y_3884_ = v___y_3910_;
v___y_3885_ = v___y_3911_;
v___y_3886_ = v___x_3918_;
v___y_3887_ = v___y_3912_;
v___y_3888_ = v___y_3913_;
v___y_3889_ = v___y_3915_;
v___y_3890_ = v___x_3919_;
v___y_3891_ = v___x_3931_;
goto v___jp_3870_;
}
}
v___jp_3932_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = lean_unsigned_to_nat(5u);
v___x_3949_ = l_Lean_Syntax_getArg(v___y_3935_, v___x_3948_);
lean_dec(v___y_3935_);
v___x_3950_ = l_Lean_Syntax_getOptional_x3f(v___y_3933_);
lean_dec(v___y_3933_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v___x_3951_; 
v___x_3951_ = lean_box(0);
v___y_3902_ = v___y_3947_;
v___y_3903_ = v___y_3945_;
v___y_3904_ = v___x_3949_;
v___y_3905_ = v___y_3941_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v_args_3939_;
v___y_3908_ = v___y_3938_;
v___y_3909_ = v___y_3944_;
v___y_3910_ = v___y_3946_;
v___y_3911_ = v___y_3942_;
v___y_3912_ = v___y_3934_;
v___y_3913_ = v___y_3943_;
v___y_3914_ = v___y_3937_;
v___y_3915_ = v___y_3940_;
v___y_3916_ = v___x_3951_;
goto v___jp_3901_;
}
else
{
lean_object* v_val_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
v_val_3952_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___x_3950_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_val_3952_);
lean_dec(v___x_3950_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_val_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
v___y_3902_ = v___y_3947_;
v___y_3903_ = v___y_3945_;
v___y_3904_ = v___x_3949_;
v___y_3905_ = v___y_3941_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v_args_3939_;
v___y_3908_ = v___y_3938_;
v___y_3909_ = v___y_3944_;
v___y_3910_ = v___y_3946_;
v___y_3911_ = v___y_3942_;
v___y_3912_ = v___y_3934_;
v___y_3913_ = v___y_3943_;
v___y_3914_ = v___y_3937_;
v___y_3915_ = v___y_3940_;
v___y_3916_ = v___x_3957_;
goto v___jp_3901_;
}
}
}
}
v___jp_3961_:
{
lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3977_ = l_Lean_Syntax_getArg(v___y_3964_, v___y_3962_);
v___x_3978_ = l_Lean_Syntax_isNone(v___x_3977_);
if (v___x_3978_ == 0)
{
uint8_t v___x_3979_; 
lean_inc(v___x_3977_);
v___x_3979_ = l_Lean_Syntax_matchesNull(v___x_3977_, v___x_3960_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
lean_dec(v___x_3977_);
lean_dec(v_only_3968_);
lean_dec(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec(v_tk_3900_);
v___x_3980_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3980_;
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3981_ = l_Lean_Syntax_getArg(v___x_3977_, v___x_3773_);
lean_dec(v___x_3977_);
v___x_3982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3981_);
v___x_3983_ = l_Lean_Syntax_isOfKind(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; 
lean_dec(v___x_3981_);
lean_dec(v_only_3968_);
lean_dec(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec(v_tk_3900_);
v___x_3984_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3984_;
}
else
{
lean_object* v___x_3985_; lean_object* v_args_3986_; lean_object* v___x_3987_; 
v___x_3985_ = l_Lean_Syntax_getArg(v___x_3981_, v___x_3960_);
lean_dec(v___x_3981_);
v_args_3986_ = l_Lean_Syntax_getArgs(v___x_3985_);
lean_dec(v___x_3985_);
v___x_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3987_, 0, v_args_3986_);
v___y_3933_ = v___y_3963_;
v___y_3934_ = v___y_3965_;
v___y_3935_ = v___y_3964_;
v___y_3936_ = v___y_3966_;
v___y_3937_ = v___y_3967_;
v___y_3938_ = v_only_3968_;
v_args_3939_ = v___x_3987_;
v___y_3940_ = v___y_3969_;
v___y_3941_ = v___y_3970_;
v___y_3942_ = v___y_3971_;
v___y_3943_ = v___y_3972_;
v___y_3944_ = v___y_3973_;
v___y_3945_ = v___y_3974_;
v___y_3946_ = v___y_3975_;
v___y_3947_ = v___y_3976_;
goto v___jp_3932_;
}
}
}
else
{
lean_object* v___x_3988_; 
lean_dec(v___x_3977_);
v___x_3988_ = lean_box(0);
v___y_3933_ = v___y_3963_;
v___y_3934_ = v___y_3965_;
v___y_3935_ = v___y_3964_;
v___y_3936_ = v___y_3966_;
v___y_3937_ = v___y_3967_;
v___y_3938_ = v_only_3968_;
v_args_3939_ = v___x_3988_;
v___y_3940_ = v___y_3969_;
v___y_3941_ = v___y_3970_;
v___y_3942_ = v___y_3971_;
v___y_3943_ = v___y_3972_;
v___y_3944_ = v___y_3973_;
v___y_3945_ = v___y_3974_;
v___y_3946_ = v___y_3975_;
v___y_3947_ = v___y_3976_;
goto v___jp_3932_;
}
}
v___jp_3989_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_4001_ = lean_unsigned_to_nat(3u);
v___x_4002_ = l_Lean_Syntax_getArg(v_stx_3729_, v___x_4001_);
lean_dec(v_stx_3729_);
v___x_4003_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4002_);
v___x_4004_ = l_Lean_Syntax_isOfKind(v___x_4002_, v___x_4003_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; 
lean_dec(v___x_4002_);
lean_dec(v_unfold_3992_);
lean_dec(v___y_3991_);
lean_dec(v_tk_3900_);
v___x_4005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4005_;
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4006_ = l_Lean_Syntax_getArg(v___x_4002_, v___x_3773_);
v___x_4007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4006_);
v___x_4008_ = l_Lean_Syntax_isOfKind(v___x_4006_, v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; 
lean_dec(v___x_4006_);
lean_dec(v___x_4002_);
lean_dec(v_unfold_3992_);
lean_dec(v___y_3991_);
lean_dec(v_tk_3900_);
v___x_4009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4009_;
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; uint8_t v___x_4012_; 
v___x_4010_ = l_Lean_Syntax_getArg(v___x_4002_, v___x_3960_);
v___x_4011_ = l_Lean_Syntax_getArg(v___x_4002_, v___y_3990_);
v___x_4012_ = l_Lean_Syntax_isNone(v___x_4011_);
if (v___x_4012_ == 0)
{
uint8_t v___x_4013_; 
lean_inc(v___x_4011_);
v___x_4013_ = l_Lean_Syntax_matchesNull(v___x_4011_, v___x_3960_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
lean_dec(v___x_4011_);
lean_dec(v___x_4010_);
lean_dec(v___x_4006_);
lean_dec(v___x_4002_);
lean_dec(v_unfold_3992_);
lean_dec(v___y_3991_);
lean_dec(v_tk_3900_);
v___x_4014_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4014_;
}
else
{
lean_object* v_only_4015_; lean_object* v___x_4016_; 
v_only_4015_ = l_Lean_Syntax_getArg(v___x_4011_, v___x_3773_);
lean_dec(v___x_4011_);
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v_only_4015_);
v___y_3962_ = v___x_4001_;
v___y_3963_ = v___x_4010_;
v___y_3964_ = v___x_4002_;
v___y_3965_ = v___x_4006_;
v___y_3966_ = v_unfold_3992_;
v___y_3967_ = v___y_3991_;
v_only_3968_ = v___x_4016_;
v___y_3969_ = v___y_3993_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___y_3996_;
v___y_3973_ = v___y_3997_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3999_;
v___y_3976_ = v___y_4000_;
goto v___jp_3961_;
}
}
else
{
lean_object* v___x_4017_; 
lean_dec(v___x_4011_);
v___x_4017_ = lean_box(0);
v___y_3962_ = v___x_4001_;
v___y_3963_ = v___x_4010_;
v___y_3964_ = v___x_4002_;
v___y_3965_ = v___x_4006_;
v___y_3966_ = v_unfold_3992_;
v___y_3967_ = v___y_3991_;
v_only_3968_ = v___x_4017_;
v___y_3969_ = v___y_3993_;
v___y_3970_ = v___y_3994_;
v___y_3971_ = v___y_3995_;
v___y_3972_ = v___y_3996_;
v___y_3973_ = v___y_3997_;
v___y_3974_ = v___y_3998_;
v___y_3975_ = v___y_3999_;
v___y_3976_ = v___y_4000_;
goto v___jp_3961_;
}
}
}
}
v___jp_4018_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; 
v___x_4028_ = lean_unsigned_to_nat(2u);
v___x_4029_ = l_Lean_Syntax_getArg(v_stx_3729_, v___x_4028_);
v___x_4030_ = l_Lean_Syntax_isNone(v___x_4029_);
if (v___x_4030_ == 0)
{
uint8_t v___x_4031_; 
lean_inc(v___x_4029_);
v___x_4031_ = l_Lean_Syntax_matchesNull(v___x_4029_, v___x_3960_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; 
lean_dec(v___x_4029_);
lean_dec(v_squeeze_4019_);
lean_dec(v_tk_3900_);
lean_dec(v_stx_3729_);
v___x_4032_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4032_;
}
else
{
lean_object* v_unfold_4033_; lean_object* v___x_4034_; 
v_unfold_4033_ = l_Lean_Syntax_getArg(v___x_4029_, v___x_3773_);
lean_dec(v___x_4029_);
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v_unfold_4033_);
v___y_3990_ = v___x_4028_;
v___y_3991_ = v_squeeze_4019_;
v_unfold_3992_ = v___x_4034_;
v___y_3993_ = v___y_4020_;
v___y_3994_ = v___y_4021_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4023_;
v___y_3997_ = v___y_4024_;
v___y_3998_ = v___y_4025_;
v___y_3999_ = v___y_4026_;
v___y_4000_ = v___y_4027_;
goto v___jp_3989_;
}
}
else
{
lean_object* v___x_4035_; 
lean_dec(v___x_4029_);
v___x_4035_ = lean_box(0);
v___y_3990_ = v___x_4028_;
v___y_3991_ = v_squeeze_4019_;
v_unfold_3992_ = v___x_4035_;
v___y_3993_ = v___y_4020_;
v___y_3994_ = v___y_4021_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4023_;
v___y_3997_ = v___y_4024_;
v___y_3998_ = v___y_4025_;
v___y_3999_ = v___y_4026_;
v___y_4000_ = v___y_4027_;
goto v___jp_3989_;
}
}
}
v___jp_3739_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_inc_ref(v___y_3752_);
v___x_3762_ = l_Array_append___redArg(v___y_3752_, v___y_3761_);
lean_dec_ref(v___y_3761_);
lean_inc_n(v___y_3746_, 2);
lean_inc_n(v___y_3760_, 4);
v___x_3763_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3763_, 0, v___y_3760_);
lean_ctor_set(v___x_3763_, 1, v___y_3746_);
lean_ctor_set(v___x_3763_, 2, v___x_3762_);
v___x_3764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___y_3760_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_Syntax_node2(v___y_3760_, v___y_3746_, v___x_3765_, v___y_3744_);
lean_inc(v___y_3747_);
v___x_3767_ = l_Lean_Syntax_node5(v___y_3760_, v___y_3747_, v___y_3756_, v___y_3758_, v___y_3748_, v___x_3763_, v___x_3766_);
lean_inc(v___y_3749_);
v___x_3768_ = l_Lean_Syntax_node4(v___y_3760_, v___y_3749_, v___y_3741_, v___y_3750_, v___y_3743_, v___x_3767_);
v___x_3769_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3755_, v___x_3768_, v___y_3759_, v___y_3745_, v___y_3754_, v___y_3757_, v___y_3751_, v___y_3742_, v___y_3753_, v___y_3740_);
return v___x_3769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4062_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4063_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4065_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4066_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4062_, v___x_4063_, v___x_4064_, v___x_4065_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4068_;
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
