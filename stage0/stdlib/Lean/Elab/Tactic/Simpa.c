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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* v___f_253_; lean_object* v___x_79970__overap_254_; lean_object* v___x_255_; 
v___f_253_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0));
v___x_79970__overap_254_ = lean_panic_fn_borrowed(v___f_253_, v_msg_243_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_255_ = lean_apply_9(v___x_79970__overap_254_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, lean_box(0));
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
uint8_t v___x_92575__boxed_587_; uint8_t v___x_92576__boxed_588_; uint8_t v_useReducible_boxed_589_; uint8_t v___x_92580__boxed_590_; lean_object* v_res_591_; 
v___x_92575__boxed_587_ = lean_unbox(v___x_570_);
v___x_92576__boxed_588_ = lean_unbox(v___x_571_);
v_useReducible_boxed_589_ = lean_unbox(v_useReducible_576_);
v___x_92580__boxed_590_ = lean_unbox(v___x_577_);
v_res_591_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_568_, v_a_569_, v___x_92575__boxed_587_, v___x_92576__boxed_588_, v_a_572_, v_mvarCounter_573_, v___x_574_, v___x_575_, v_useReducible_boxed_589_, v___x_92580__boxed_590_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
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
v___x_625_ = lean_st_ref_set(v___y_600_, v___x_624_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
return v_x_644_;
}
else
{
lean_object* v_key_646_; lean_object* v_value_647_; lean_object* v_tail_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_671_; 
v_key_646_ = lean_ctor_get(v_x_645_, 0);
v_value_647_ = lean_ctor_get(v_x_645_, 1);
v_tail_648_ = lean_ctor_get(v_x_645_, 2);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_671_ == 0)
{
v___x_650_ = v_x_645_;
v_isShared_651_ = v_isSharedCheck_671_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_tail_648_);
lean_inc(v_value_647_);
lean_inc(v_key_646_);
lean_dec(v_x_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_671_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v_fold_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_652_ = lean_array_get_size(v_x_644_);
v___x_653_ = l_Lean_Expr_hash(v_key_646_);
v___x_654_ = 32ULL;
v___x_655_ = lean_uint64_shift_right(v___x_653_, v___x_654_);
v_fold_656_ = lean_uint64_xor(v___x_653_, v___x_655_);
v___x_657_ = 16ULL;
v___x_658_ = lean_uint64_shift_right(v_fold_656_, v___x_657_);
v___x_659_ = lean_uint64_xor(v_fold_656_, v___x_658_);
v___x_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = lean_usize_of_nat(v___x_652_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_sub(v___x_661_, v___x_662_);
v___x_664_ = lean_usize_land(v___x_660_, v___x_663_);
v___x_665_ = lean_array_uget_borrowed(v_x_644_, v___x_664_);
lean_inc(v___x_665_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 2, v___x_665_);
v___x_667_ = v___x_650_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_key_646_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_value_647_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___x_665_);
v___x_667_ = v_reuseFailAlloc_670_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = lean_array_uset(v_x_644_, v___x_664_, v___x_667_);
v_x_644_ = v___x_668_;
v_x_645_ = v_tail_648_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(lean_object* v_i_672_, lean_object* v_source_673_, lean_object* v_target_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_source_673_);
v___x_676_ = lean_nat_dec_lt(v_i_672_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec_ref(v_source_673_);
lean_dec(v_i_672_);
return v_target_674_;
}
else
{
lean_object* v_es_677_; lean_object* v___x_678_; lean_object* v_source_679_; lean_object* v_target_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_es_677_ = lean_array_fget(v_source_673_, v_i_672_);
v___x_678_ = lean_box(0);
v_source_679_ = lean_array_fset(v_source_673_, v_i_672_, v___x_678_);
v_target_680_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_674_, v_es_677_);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_i_672_, v___x_681_);
lean_dec(v_i_672_);
v_i_672_ = v___x_682_;
v_source_673_ = v_source_679_;
v_target_674_ = v_target_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_data_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_nbuckets_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_685_ = lean_array_get_size(v_data_684_);
v___x_686_ = lean_unsigned_to_nat(2u);
v_nbuckets_687_ = lean_nat_mul(v___x_685_, v___x_686_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_box(0);
v___x_690_ = lean_mk_array(v_nbuckets_687_, v___x_689_);
v___x_691_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_688_, v_data_684_, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(lean_object* v_a_692_, lean_object* v_x_693_){
_start:
{
if (lean_obj_tag(v_x_693_) == 0)
{
uint8_t v___x_694_; 
v___x_694_ = 0;
return v___x_694_;
}
else
{
lean_object* v_key_695_; lean_object* v_tail_696_; uint8_t v___x_697_; 
v_key_695_ = lean_ctor_get(v_x_693_, 0);
v_tail_696_ = lean_ctor_get(v_x_693_, 2);
v___x_697_ = lean_expr_eqv(v_key_695_, v_a_692_);
if (v___x_697_ == 0)
{
v_x_693_ = v_tail_696_;
goto _start;
}
else
{
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_699_, v_x_700_);
lean_dec(v_x_700_);
lean_dec_ref(v_a_699_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(lean_object* v_m_703_, lean_object* v_a_704_, lean_object* v_b_705_){
_start:
{
lean_object* v_size_706_; lean_object* v_buckets_707_; lean_object* v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; uint64_t v_fold_712_; uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; lean_object* v_bkt_721_; uint8_t v___x_722_; 
v_size_706_ = lean_ctor_get(v_m_703_, 0);
v_buckets_707_ = lean_ctor_get(v_m_703_, 1);
v___x_708_ = lean_array_get_size(v_buckets_707_);
v___x_709_ = l_Lean_Expr_hash(v_a_704_);
v___x_710_ = 32ULL;
v___x_711_ = lean_uint64_shift_right(v___x_709_, v___x_710_);
v_fold_712_ = lean_uint64_xor(v___x_709_, v___x_711_);
v___x_713_ = 16ULL;
v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
v___x_716_ = lean_uint64_to_usize(v___x_715_);
v___x_717_ = lean_usize_of_nat(v___x_708_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
v_bkt_721_ = lean_array_uget_borrowed(v_buckets_707_, v___x_720_);
v___x_722_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_704_, v_bkt_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_743_; 
lean_inc_ref(v_buckets_707_);
lean_inc(v_size_706_);
v_isSharedCheck_743_ = !lean_is_exclusive(v_m_703_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; lean_object* v_unused_745_; 
v_unused_744_ = lean_ctor_get(v_m_703_, 1);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_m_703_, 0);
lean_dec(v_unused_745_);
v___x_724_ = v_m_703_;
v_isShared_725_ = v_isSharedCheck_743_;
goto v_resetjp_723_;
}
else
{
lean_dec(v_m_703_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_743_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v_size_x27_727_; lean_object* v___x_728_; lean_object* v_buckets_x27_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v_size_x27_727_ = lean_nat_add(v_size_706_, v___x_726_);
lean_dec(v_size_706_);
lean_inc(v_bkt_721_);
v___x_728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_728_, 0, v_a_704_);
lean_ctor_set(v___x_728_, 1, v_b_705_);
lean_ctor_set(v___x_728_, 2, v_bkt_721_);
v_buckets_x27_729_ = lean_array_uset(v_buckets_707_, v___x_720_, v___x_728_);
v___x_730_ = lean_unsigned_to_nat(4u);
v___x_731_ = lean_nat_mul(v_size_x27_727_, v___x_730_);
v___x_732_ = lean_unsigned_to_nat(3u);
v___x_733_ = lean_nat_div(v___x_731_, v___x_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_array_get_size(v_buckets_x27_729_);
v___x_735_ = lean_nat_dec_le(v___x_733_, v___x_734_);
lean_dec(v___x_733_);
if (v___x_735_ == 0)
{
lean_object* v_val_736_; lean_object* v___x_738_; 
v_val_736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_729_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v_val_736_);
lean_ctor_set(v___x_724_, 0, v_size_x27_727_);
v___x_738_ = v___x_724_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_size_x27_727_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_val_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v___x_741_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v_buckets_x27_729_);
lean_ctor_set(v___x_724_, 0, v_size_x27_727_);
v___x_741_ = v___x_724_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_size_x27_727_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_buckets_x27_729_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
else
{
lean_dec(v_b_705_);
lean_dec_ref(v_a_704_);
return v_m_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(lean_object* v_mvarId_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; lean_object* v_mctx_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_750_ = lean_st_ref_get(v___y_748_);
v_mctx_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc_ref(v_mctx_751_);
lean_dec(v___x_750_);
v___x_752_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_751_, v_mvarId_746_);
lean_dec_ref(v_mctx_751_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___y_747_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg___boxed(lean_object* v_mvarId_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec(v_mvarId_756_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(lean_object* v_mvarId_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; lean_object* v_mctx_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_765_ = lean_st_ref_get(v___y_763_);
v_mctx_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc_ref(v_mctx_766_);
lean_dec(v___x_765_);
v___x_767_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_766_, v_mvarId_761_);
lean_dec_ref(v_mctx_766_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___y_762_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(lean_object* v_mvarId_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec(v_mvarId_771_);
return v_res_775_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_buckets_778_; lean_object* v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v_fold_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_buckets_778_ = lean_ctor_get(v_m_776_, 1);
v___x_779_ = lean_array_get_size(v_buckets_778_);
v___x_780_ = l_Lean_Expr_hash(v_a_777_);
v___x_781_ = 32ULL;
v___x_782_ = lean_uint64_shift_right(v___x_780_, v___x_781_);
v_fold_783_ = lean_uint64_xor(v___x_780_, v___x_782_);
v___x_784_ = 16ULL;
v___x_785_ = lean_uint64_shift_right(v_fold_783_, v___x_784_);
v___x_786_ = lean_uint64_xor(v_fold_783_, v___x_785_);
v___x_787_ = lean_uint64_to_usize(v___x_786_);
v___x_788_ = lean_usize_of_nat(v___x_779_);
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_sub(v___x_788_, v___x_789_);
v___x_791_ = lean_usize_land(v___x_787_, v___x_790_);
v___x_792_ = lean_array_uget_borrowed(v_buckets_778_, v___x_791_);
v___x_793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_777_, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_m_794_, lean_object* v_a_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_794_, v_a_795_);
lean_dec_ref(v_a_795_);
lean_dec_ref(v_m_794_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_802_, lean_object* v_e_803_, lean_object* v_a_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_d_815_; lean_object* v_b_816_; lean_object* v___y_817_; uint8_t v___x_823_; 
v___x_823_ = l_Lean_Expr_hasExprMVar(v_e_803_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec_ref(v_e_803_);
v___x_824_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_a_804_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_804_, v_e_803_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_box(0);
lean_inc_ref(v_e_803_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_a_804_, v_e_803_, v___x_828_);
switch(lean_obj_tag(v_e_803_))
{
case 11:
{
lean_object* v_struct_830_; 
v_struct_830_ = lean_ctor_get(v_e_803_, 2);
lean_inc_ref(v_struct_830_);
lean_dec_ref_known(v_e_803_, 3);
v_e_803_ = v_struct_830_;
v_a_804_ = v___x_829_;
goto _start;
}
case 7:
{
lean_object* v_binderType_832_; lean_object* v_body_833_; 
v_binderType_832_ = lean_ctor_get(v_e_803_, 1);
lean_inc_ref(v_binderType_832_);
v_body_833_ = lean_ctor_get(v_e_803_, 2);
lean_inc_ref(v_body_833_);
lean_dec_ref_known(v_e_803_, 3);
v_d_815_ = v_binderType_832_;
v_b_816_ = v_body_833_;
v___y_817_ = v___x_829_;
goto v___jp_814_;
}
case 6:
{
lean_object* v_binderType_834_; lean_object* v_body_835_; 
v_binderType_834_ = lean_ctor_get(v_e_803_, 1);
lean_inc_ref(v_binderType_834_);
v_body_835_ = lean_ctor_get(v_e_803_, 2);
lean_inc_ref(v_body_835_);
lean_dec_ref_known(v_e_803_, 3);
v_d_815_ = v_binderType_834_;
v_b_816_ = v_body_835_;
v___y_817_ = v___x_829_;
goto v___jp_814_;
}
case 8:
{
lean_object* v_type_836_; lean_object* v_value_837_; lean_object* v_body_838_; lean_object* v___x_839_; 
v_type_836_ = lean_ctor_get(v_e_803_, 1);
lean_inc_ref(v_type_836_);
v_value_837_ = lean_ctor_get(v_e_803_, 2);
lean_inc_ref(v_value_837_);
v_body_838_ = lean_ctor_get(v_e_803_, 3);
lean_inc_ref(v_body_838_);
lean_dec_ref_known(v_e_803_, 4);
v___x_839_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_802_, v_type_836_, v___x_829_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v_fst_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
v_fst_841_ = lean_ctor_get(v_a_840_, 0);
if (lean_obj_tag(v_fst_841_) == 0)
{
lean_dec(v_a_840_);
lean_dec_ref(v_body_838_);
lean_dec_ref(v_value_837_);
return v___x_839_;
}
else
{
lean_object* v_snd_842_; lean_object* v___x_843_; 
lean_dec_ref_known(v___x_839_, 1);
v_snd_842_ = lean_ctor_get(v_a_840_, 1);
lean_inc(v_snd_842_);
lean_dec(v_a_840_);
v___x_843_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_802_, v_value_837_, v_snd_842_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v_fst_845_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
v_fst_845_ = lean_ctor_get(v_a_844_, 0);
if (lean_obj_tag(v_fst_845_) == 0)
{
lean_dec(v_a_844_);
lean_dec_ref(v_body_838_);
return v___x_843_;
}
else
{
lean_object* v_snd_846_; 
lean_dec_ref_known(v___x_843_, 1);
v_snd_846_ = lean_ctor_get(v_a_844_, 1);
lean_inc(v_snd_846_);
lean_dec(v_a_844_);
v_e_803_ = v_body_838_;
v_a_804_ = v_snd_846_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_838_);
return v___x_843_;
}
}
}
else
{
lean_dec_ref(v_body_838_);
lean_dec_ref(v_value_837_);
return v___x_839_;
}
}
case 10:
{
lean_object* v_expr_848_; 
v_expr_848_ = lean_ctor_get(v_e_803_, 1);
lean_inc_ref(v_expr_848_);
lean_dec_ref_known(v_e_803_, 2);
v_e_803_ = v_expr_848_;
v_a_804_ = v___x_829_;
goto _start;
}
case 5:
{
lean_object* v_fn_850_; lean_object* v_arg_851_; lean_object* v___x_852_; 
v_fn_850_ = lean_ctor_get(v_e_803_, 0);
lean_inc_ref(v_fn_850_);
v_arg_851_ = lean_ctor_get(v_e_803_, 1);
lean_inc_ref(v_arg_851_);
lean_dec_ref_known(v_e_803_, 2);
v___x_852_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_802_, v_fn_850_, v___x_829_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v_fst_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
v_fst_854_ = lean_ctor_get(v_a_853_, 0);
if (lean_obj_tag(v_fst_854_) == 0)
{
lean_dec(v_a_853_);
lean_dec_ref(v_arg_851_);
return v___x_852_;
}
else
{
lean_object* v_snd_855_; 
lean_dec_ref_known(v___x_852_, 1);
v_snd_855_ = lean_ctor_get(v_a_853_, 1);
lean_inc(v_snd_855_);
lean_dec(v_a_853_);
v_e_803_ = v_arg_851_;
v_a_804_ = v_snd_855_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_851_);
return v___x_852_;
}
}
case 2:
{
lean_object* v_mvarId_857_; lean_object* v___x_858_; 
v_mvarId_857_ = lean_ctor_get(v_e_803_, 0);
lean_inc(v_mvarId_857_);
lean_dec_ref_known(v_e_803_, 1);
v___x_858_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_802_, v_mvarId_857_, v___x_829_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
return v___x_858_;
}
default: 
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref(v_e_803_);
v___x_859_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_829_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec_ref(v_e_803_);
v___x_862_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v_a_804_);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
v___jp_814_:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_802_, v_d_815_, v___y_817_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_fst_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
v_fst_820_ = lean_ctor_get(v_a_819_, 0);
if (lean_obj_tag(v_fst_820_) == 0)
{
lean_dec(v_a_819_);
lean_dec_ref(v_b_816_);
return v___x_818_;
}
else
{
lean_object* v_snd_821_; 
lean_dec_ref_known(v___x_818_, 1);
v_snd_821_ = lean_ctor_get(v_a_819_, 1);
lean_inc(v_snd_821_);
lean_dec(v_a_819_);
v_e_803_ = v_b_816_;
v_a_804_ = v_snd_821_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_816_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(lean_object* v_mvarId_865_, lean_object* v_mvarId_x27_866_, lean_object* v_a_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_instBEqMVarId_beq(v_mvarId_865_, v_mvarId_x27_866_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_866_, v_a_867_, v___y_873_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_962_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_962_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_962_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_962_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_fst_883_; 
v_fst_883_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_fst_883_);
if (lean_obj_tag(v_fst_883_) == 0)
{
lean_object* v_snd_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_mvarId_x27_866_);
v_snd_884_ = lean_ctor_get(v_a_879_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_a_879_, 0);
lean_dec(v_unused_903_);
v___x_886_ = v_a_879_;
v_isShared_887_ = v_isSharedCheck_902_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_snd_884_);
lean_dec(v_a_879_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_902_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_901_; 
v_a_888_ = lean_ctor_get(v_fst_883_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_fst_883_);
if (v_isSharedCheck_901_ == 0)
{
v___x_890_ = v_fst_883_;
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v_fst_883_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_900_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_893_);
v___x_895_ = v___x_886_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_snd_884_);
v___x_895_ = v_reuseFailAlloc_899_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_895_);
v___x_897_ = v___x_881_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
else
{
lean_object* v_a_904_; 
lean_del_object(v___x_881_);
v_a_904_ = lean_ctor_get(v_fst_883_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v_fst_883_, 1);
if (lean_obj_tag(v_a_904_) == 0)
{
lean_object* v_snd_905_; lean_object* v___x_906_; 
v_snd_905_ = lean_ctor_get(v_a_879_, 1);
lean_inc(v_snd_905_);
lean_dec(v_a_879_);
v___x_906_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_866_, v_snd_905_, v___y_873_);
lean_dec(v_mvarId_x27_866_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_950_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_950_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_950_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_950_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_fst_911_; 
v_fst_911_ = lean_ctor_get(v_a_907_, 0);
lean_inc(v_fst_911_);
if (lean_obj_tag(v_fst_911_) == 0)
{
lean_object* v_snd_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_930_; 
v_snd_912_ = lean_ctor_get(v_a_907_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_a_907_, 0);
lean_dec(v_unused_931_);
v___x_914_ = v_a_907_;
v_isShared_915_ = v_isSharedCheck_930_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snd_912_);
lean_dec(v_a_907_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_930_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_929_; 
v_a_916_ = lean_ctor_get(v_fst_911_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_fst_911_);
if (v_isSharedCheck_929_ == 0)
{
v___x_918_ = v_fst_911_;
v_isShared_919_ = v_isSharedCheck_929_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v_fst_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_929_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_928_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_921_);
v___x_923_ = v___x_914_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_snd_912_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_923_);
v___x_925_ = v___x_909_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
else
{
lean_object* v_a_932_; 
v_a_932_ = lean_ctor_get(v_fst_911_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v_fst_911_, 1);
if (lean_obj_tag(v_a_932_) == 0)
{
lean_object* v_snd_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_944_; 
v_snd_933_ = lean_ctor_get(v_a_907_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_a_907_, 0);
lean_dec(v_unused_945_);
v___x_935_ = v_a_907_;
v_isShared_936_ = v_isSharedCheck_944_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_snd_933_);
lean_dec(v_a_907_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_944_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0));
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_snd_933_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_939_);
v___x_941_ = v___x_909_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
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
lean_object* v_val_946_; lean_object* v_snd_947_; lean_object* v_mvarIdPending_948_; 
lean_del_object(v___x_909_);
v_val_946_ = lean_ctor_get(v_a_932_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v_a_932_, 1);
v_snd_947_ = lean_ctor_get(v_a_907_, 1);
lean_inc(v_snd_947_);
lean_dec(v_a_907_);
v_mvarIdPending_948_ = lean_ctor_get(v_val_946_, 1);
lean_inc(v_mvarIdPending_948_);
lean_dec(v_val_946_);
v_mvarId_x27_866_ = v_mvarIdPending_948_;
v_a_867_ = v_snd_947_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_906_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_906_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
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
else
{
lean_object* v_snd_959_; lean_object* v_val_960_; lean_object* v___x_961_; 
lean_dec(v_mvarId_x27_866_);
v_snd_959_ = lean_ctor_get(v_a_879_, 1);
lean_inc(v_snd_959_);
lean_dec(v_a_879_);
v_val_960_ = lean_ctor_get(v_a_904_, 0);
lean_inc(v_val_960_);
lean_dec_ref_known(v_a_904_, 1);
v___x_961_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_865_, v_val_960_, v_snd_959_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_mvarId_x27_866_);
v_a_963_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_878_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_878_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec(v_mvarId_x27_866_);
v___x_971_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1));
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v_a_867_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(lean_object* v_mvarId_974_, lean_object* v_mvarId_x27_975_, lean_object* v_a_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_974_, v_mvarId_x27_975_, v_a_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_mvarId_974_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_987_, lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_987_, v_e_988_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v_mvarId_987_);
return v_res_999_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_box(0);
v___x_1001_ = lean_unsigned_to_nat(16u);
v___x_1002_ = lean_mk_array(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1006_, lean_object* v_e_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = l_Lean_Expr_hasExprMVar(v_e_1007_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec_ref(v_e_1007_);
v___x_1018_ = 1;
v___x_1019_ = lean_box(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1022_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1006_, v_e_1007_, v___x_1021_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_fst_1027_; 
v_fst_1027_ = lean_ctor_get(v_a_1023_, 0);
lean_inc(v_fst_1027_);
lean_dec(v_a_1023_);
if (lean_obj_tag(v_fst_1027_) == 0)
{
uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_dec_ref_known(v_fst_1027_, 1);
v___x_1028_ = 0;
v___x_1029_ = lean_box(v___x_1028_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_dec_ref_known(v_fst_1027_, 1);
v___x_1033_ = lean_box(v___x_1017_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1033_);
v___x_1035_ = v___x_1025_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
v_a_1038_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1022_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1022_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1046_, lean_object* v_e_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1046_, v_e_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v_mvarId_1046_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(lean_object* v_msgData_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; lean_object* v_env_1065_; lean_object* v___x_1066_; lean_object* v_mctx_1067_; lean_object* v_lctx_1068_; lean_object* v_options_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1064_ = lean_st_ref_get(v___y_1062_);
v_env_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_env_1065_);
lean_dec(v___x_1064_);
v___x_1066_ = lean_st_ref_get(v___y_1060_);
v_mctx_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_ref(v_mctx_1067_);
lean_dec(v___x_1066_);
v_lctx_1068_ = lean_ctor_get(v___y_1059_, 2);
v_options_1069_ = lean_ctor_get(v___y_1061_, 2);
lean_inc_ref(v_options_1069_);
lean_inc_ref(v_lctx_1068_);
v___x_1070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1070_, 0, v_env_1065_);
lean_ctor_set(v___x_1070_, 1, v_mctx_1067_);
lean_ctor_set(v___x_1070_, 2, v_lctx_1068_);
lean_ctor_set(v___x_1070_, 3, v_options_1069_);
v___x_1071_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_msgData_1058_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(lean_object* v_msgData_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msgData_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v_msg_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_ref_1086_; lean_object* v___x_1087_; lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_ref_1086_ = lean_ctor_get(v___y_1083_, 5);
v___x_1087_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msg_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_inc(v_ref_1086_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_ref_1086_);
lean_ctor_set(v___x_1092_, 1, v_a_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set_tag(v___x_1090_, 1);
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v_msg_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(lean_object* v_x_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v_ks_1108_; lean_object* v_vs_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1133_; 
v_ks_1108_ = lean_ctor_get(v_x_1104_, 0);
v_vs_1109_ = lean_ctor_get(v_x_1104_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1104_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1111_ = v_x_1104_;
v_isShared_1112_ = v_isSharedCheck_1133_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_vs_1109_);
lean_inc(v_ks_1108_);
lean_dec(v_x_1104_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1133_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_array_get_size(v_ks_1108_);
v___x_1114_ = lean_nat_dec_lt(v_x_1105_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_dec(v_x_1105_);
v___x_1115_ = lean_array_push(v_ks_1108_, v_x_1106_);
v___x_1116_ = lean_array_push(v_vs_1109_, v_x_1107_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1116_);
lean_ctor_set(v___x_1111_, 0, v___x_1115_);
v___x_1118_ = v___x_1111_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
else
{
lean_object* v_k_x27_1120_; uint8_t v___x_1121_; 
v_k_x27_1120_ = lean_array_fget_borrowed(v_ks_1108_, v_x_1105_);
v___x_1121_ = l_Lean_instBEqMVarId_beq(v_x_1106_, v_k_x27_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1123_; 
if (v_isShared_1112_ == 0)
{
v___x_1123_ = v___x_1111_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_ks_1108_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_vs_1109_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_x_1105_, v___x_1124_);
lean_dec(v_x_1105_);
v_x_1104_ = v___x_1123_;
v_x_1105_ = v___x_1125_;
goto _start;
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1128_ = lean_array_fset(v_ks_1108_, v_x_1105_, v_x_1106_);
v___x_1129_ = lean_array_fset(v_vs_1109_, v_x_1105_, v_x_1107_);
lean_dec(v_x_1105_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1129_);
lean_ctor_set(v___x_1111_, 0, v___x_1128_);
v___x_1131_ = v___x_1111_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(lean_object* v_n_1134_, lean_object* v_k_1135_, lean_object* v_v_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_1134_, v___x_1137_, v_k_1135_, v_v_1136_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(lean_object* v_x_1140_, size_t v_x_1141_, size_t v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
lean_object* v_es_1145_; size_t v___x_1146_; size_t v___x_1147_; lean_object* v_j_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_es_1145_ = lean_ctor_get(v_x_1140_, 0);
v___x_1146_ = ((size_t)31ULL);
v___x_1147_ = lean_usize_land(v_x_1141_, v___x_1146_);
v_j_1148_ = lean_usize_to_nat(v___x_1147_);
v___x_1149_ = lean_array_get_size(v_es_1145_);
v___x_1150_ = lean_nat_dec_lt(v_j_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_dec(v_j_1148_);
lean_dec(v_x_1144_);
lean_dec(v_x_1143_);
return v_x_1140_;
}
else
{
lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1189_; 
lean_inc_ref(v_es_1145_);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v_x_1140_, 0);
lean_dec(v_unused_1190_);
v___x_1152_ = v_x_1140_;
v_isShared_1153_ = v_isSharedCheck_1189_;
goto v_resetjp_1151_;
}
else
{
lean_dec(v_x_1140_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1189_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_v_1154_; lean_object* v___x_1155_; lean_object* v_xs_x27_1156_; lean_object* v___y_1158_; 
v_v_1154_ = lean_array_fget(v_es_1145_, v_j_1148_);
v___x_1155_ = lean_box(0);
v_xs_x27_1156_ = lean_array_fset(v_es_1145_, v_j_1148_, v___x_1155_);
switch(lean_obj_tag(v_v_1154_))
{
case 0:
{
lean_object* v_key_1163_; lean_object* v_val_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1174_; 
v_key_1163_ = lean_ctor_get(v_v_1154_, 0);
v_val_1164_ = lean_ctor_get(v_v_1154_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_v_1154_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1166_ = v_v_1154_;
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_val_1164_);
lean_inc(v_key_1163_);
lean_dec(v_v_1154_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1174_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
uint8_t v___x_1168_; 
v___x_1168_ = l_Lean_instBEqMVarId_beq(v_x_1143_, v_key_1163_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_del_object(v___x_1166_);
v___x_1169_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1163_, v_val_1164_, v_x_1143_, v_x_1144_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
v___y_1158_ = v___x_1170_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1172_; 
lean_dec(v_val_1164_);
lean_dec(v_key_1163_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_x_1144_);
lean_ctor_set(v___x_1166_, 0, v_x_1143_);
v___x_1172_ = v___x_1166_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_x_1143_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_x_1144_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v___y_1158_ = v___x_1172_;
goto v___jp_1157_;
}
}
}
}
case 1:
{
lean_object* v_node_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1187_; 
v_node_1175_ = lean_ctor_get(v_v_1154_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_v_1154_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1177_ = v_v_1154_;
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_node_1175_);
lean_dec(v_v_1154_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1179_ = ((size_t)5ULL);
v___x_1180_ = lean_usize_shift_right(v_x_1141_, v___x_1179_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_x_1142_, v___x_1181_);
v___x_1183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_node_1175_, v___x_1180_, v___x_1182_, v_x_1143_, v_x_1144_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1183_);
v___x_1185_ = v___x_1177_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
v___y_1158_ = v___x_1185_;
goto v___jp_1157_;
}
}
}
default: 
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_x_1143_);
lean_ctor_set(v___x_1188_, 1, v_x_1144_);
v___y_1158_ = v___x_1188_;
goto v___jp_1157_;
}
}
v___jp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_array_fset(v_xs_x27_1156_, v_j_1148_, v___y_1158_);
lean_dec(v_j_1148_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1159_);
v___x_1161_ = v___x_1152_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
else
{
lean_object* v_ks_1191_; lean_object* v_vs_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1212_; 
v_ks_1191_ = lean_ctor_get(v_x_1140_, 0);
v_vs_1192_ = lean_ctor_get(v_x_1140_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1194_ = v_x_1140_;
v_isShared_1195_ = v_isSharedCheck_1212_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_vs_1192_);
lean_inc(v_ks_1191_);
lean_dec(v_x_1140_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1212_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_ks_1191_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_vs_1192_);
v___x_1197_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v_newNode_1198_; uint8_t v___y_1200_; size_t v___x_1206_; uint8_t v___x_1207_; 
v_newNode_1198_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1197_, v_x_1143_, v_x_1144_);
v___x_1206_ = ((size_t)7ULL);
v___x_1207_ = lean_usize_dec_le(v___x_1206_, v_x_1142_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1198_);
v___x_1209_ = lean_unsigned_to_nat(4u);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
lean_dec(v___x_1208_);
v___y_1200_ = v___x_1210_;
goto v___jp_1199_;
}
else
{
v___y_1200_ = v___x_1207_;
goto v___jp_1199_;
}
v___jp_1199_:
{
if (v___y_1200_ == 0)
{
lean_object* v_ks_1201_; lean_object* v_vs_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_ks_1201_ = lean_ctor_get(v_newNode_1198_, 0);
lean_inc_ref(v_ks_1201_);
v_vs_1202_ = lean_ctor_get(v_newNode_1198_, 1);
lean_inc_ref(v_vs_1202_);
lean_dec_ref(v_newNode_1198_);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1142_, v_ks_1201_, v_vs_1202_, v___x_1203_, v___x_1204_);
lean_dec_ref(v_vs_1202_);
lean_dec_ref(v_ks_1201_);
return v___x_1205_;
}
else
{
return v_newNode_1198_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1213_, lean_object* v_keys_1214_, lean_object* v_vals_1215_, lean_object* v_i_1216_, lean_object* v_entries_1217_){
_start:
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_array_get_size(v_keys_1214_);
v___x_1219_ = lean_nat_dec_lt(v_i_1216_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_dec(v_i_1216_);
return v_entries_1217_;
}
else
{
lean_object* v_k_1220_; lean_object* v_v_1221_; uint64_t v___x_1222_; size_t v_h_1223_; size_t v___x_1224_; lean_object* v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v_h_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_k_1220_ = lean_array_fget_borrowed(v_keys_1214_, v_i_1216_);
v_v_1221_ = lean_array_fget_borrowed(v_vals_1215_, v_i_1216_);
v___x_1222_ = l_Lean_instHashableMVarId_hash(v_k_1220_);
v_h_1223_ = lean_uint64_to_usize(v___x_1222_);
v___x_1224_ = ((size_t)5ULL);
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_sub(v_depth_1213_, v___x_1226_);
v___x_1228_ = lean_usize_mul(v___x_1224_, v___x_1227_);
v_h_1229_ = lean_usize_shift_right(v_h_1223_, v___x_1228_);
v___x_1230_ = lean_nat_add(v_i_1216_, v___x_1225_);
lean_dec(v_i_1216_);
lean_inc(v_v_1221_);
lean_inc(v_k_1220_);
v___x_1231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_entries_1217_, v_h_1229_, v_depth_1213_, v_k_1220_, v_v_1221_);
v_i_1216_ = v___x_1230_;
v_entries_1217_ = v___x_1231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1233_, lean_object* v_keys_1234_, lean_object* v_vals_1235_, lean_object* v_i_1236_, lean_object* v_entries_1237_){
_start:
{
size_t v_depth_boxed_1238_; lean_object* v_res_1239_; 
v_depth_boxed_1238_ = lean_unbox_usize(v_depth_1233_);
lean_dec(v_depth_1233_);
v_res_1239_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1238_, v_keys_1234_, v_vals_1235_, v_i_1236_, v_entries_1237_);
lean_dec_ref(v_vals_1235_);
lean_dec_ref(v_keys_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
size_t v_x_93851__boxed_1245_; size_t v_x_93852__boxed_1246_; lean_object* v_res_1247_; 
v_x_93851__boxed_1245_ = lean_unbox_usize(v_x_1241_);
lean_dec(v_x_1241_);
v_x_93852__boxed_1246_ = lean_unbox_usize(v_x_1242_);
lean_dec(v_x_1242_);
v_res_1247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1240_, v_x_93851__boxed_1245_, v_x_93852__boxed_1246_, v_x_1243_, v_x_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint64_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1251_ = l_Lean_instHashableMVarId_hash(v_x_1249_);
v___x_1252_ = lean_uint64_to_usize(v___x_1251_);
v___x_1253_ = ((size_t)1ULL);
v___x_1254_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1248_, v___x_1252_, v___x_1253_, v_x_1249_, v_x_1250_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_1255_, lean_object* v_val_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v_mctx_1260_; lean_object* v_cache_1261_; lean_object* v_zetaDeltaFVarIds_1262_; lean_object* v_postponed_1263_; lean_object* v_diag_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1292_; 
v___x_1259_ = lean_st_ref_take(v___y_1257_);
v_mctx_1260_ = lean_ctor_get(v___x_1259_, 0);
v_cache_1261_ = lean_ctor_get(v___x_1259_, 1);
v_zetaDeltaFVarIds_1262_ = lean_ctor_get(v___x_1259_, 2);
v_postponed_1263_ = lean_ctor_get(v___x_1259_, 3);
v_diag_1264_ = lean_ctor_get(v___x_1259_, 4);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1266_ = v___x_1259_;
v_isShared_1267_ = v_isSharedCheck_1292_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_diag_1264_);
lean_inc(v_postponed_1263_);
lean_inc(v_zetaDeltaFVarIds_1262_);
lean_inc(v_cache_1261_);
lean_inc(v_mctx_1260_);
lean_dec(v___x_1259_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1292_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_depth_1268_; lean_object* v_levelAssignDepth_1269_; lean_object* v_lmvarCounter_1270_; lean_object* v_mvarCounter_1271_; lean_object* v_lDecls_1272_; lean_object* v_decls_1273_; lean_object* v_userNames_1274_; lean_object* v_lAssignment_1275_; lean_object* v_eAssignment_1276_; lean_object* v_dAssignment_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1291_; 
v_depth_1268_ = lean_ctor_get(v_mctx_1260_, 0);
v_levelAssignDepth_1269_ = lean_ctor_get(v_mctx_1260_, 1);
v_lmvarCounter_1270_ = lean_ctor_get(v_mctx_1260_, 2);
v_mvarCounter_1271_ = lean_ctor_get(v_mctx_1260_, 3);
v_lDecls_1272_ = lean_ctor_get(v_mctx_1260_, 4);
v_decls_1273_ = lean_ctor_get(v_mctx_1260_, 5);
v_userNames_1274_ = lean_ctor_get(v_mctx_1260_, 6);
v_lAssignment_1275_ = lean_ctor_get(v_mctx_1260_, 7);
v_eAssignment_1276_ = lean_ctor_get(v_mctx_1260_, 8);
v_dAssignment_1277_ = lean_ctor_get(v_mctx_1260_, 9);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_mctx_1260_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1279_ = v_mctx_1260_;
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_dAssignment_1277_);
lean_inc(v_eAssignment_1276_);
lean_inc(v_lAssignment_1275_);
lean_inc(v_userNames_1274_);
lean_inc(v_decls_1273_);
lean_inc(v_lDecls_1272_);
lean_inc(v_mvarCounter_1271_);
lean_inc(v_lmvarCounter_1270_);
lean_inc(v_levelAssignDepth_1269_);
lean_inc(v_depth_1268_);
lean_dec(v_mctx_1260_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_1276_, v_mvarId_1255_, v_val_1256_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 8, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_depth_1268_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_levelAssignDepth_1269_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_lmvarCounter_1270_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_mvarCounter_1271_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_lDecls_1272_);
lean_ctor_set(v_reuseFailAlloc_1290_, 5, v_decls_1273_);
lean_ctor_set(v_reuseFailAlloc_1290_, 6, v_userNames_1274_);
lean_ctor_set(v_reuseFailAlloc_1290_, 7, v_lAssignment_1275_);
lean_ctor_set(v_reuseFailAlloc_1290_, 8, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1290_, 9, v_dAssignment_1277_);
v___x_1283_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1283_);
v___x_1285_ = v___x_1266_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_cache_1261_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_zetaDeltaFVarIds_1262_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_postponed_1263_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_diag_1264_);
v___x_1285_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_st_ref_set(v___y_1257_, v___x_1285_);
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_1293_, lean_object* v_val_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_1293_, v_val_1294_, v___y_1295_);
lean_dec(v___y_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v___y_1306_, uint8_t v_suppressElabErrors_1307_, lean_object* v_x_1308_){
_start:
{
if (lean_obj_tag(v_x_1308_) == 1)
{
lean_object* v_pre_1309_; 
v_pre_1309_ = lean_ctor_get(v_x_1308_, 0);
switch(lean_obj_tag(v_pre_1309_))
{
case 1:
{
lean_object* v_pre_1310_; 
v_pre_1310_ = lean_ctor_get(v_pre_1309_, 0);
switch(lean_obj_tag(v_pre_1310_))
{
case 0:
{
lean_object* v_str_1311_; lean_object* v_str_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_str_1311_ = lean_ctor_get(v_x_1308_, 1);
v_str_1312_ = lean_ctor_get(v_pre_1309_, 1);
v___x_1313_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1314_ = lean_string_dec_eq(v_str_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1316_ = lean_string_dec_eq(v_str_1312_, v___x_1315_);
if (v___x_1316_ == 0)
{
return v___y_1306_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1318_ = lean_string_dec_eq(v_str_1311_, v___x_1317_);
if (v___x_1318_ == 0)
{
return v___y_1306_;
}
else
{
return v_suppressElabErrors_1307_;
}
}
}
else
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1320_ = lean_string_dec_eq(v_str_1311_, v___x_1319_);
if (v___x_1320_ == 0)
{
return v___y_1306_;
}
else
{
return v_suppressElabErrors_1307_;
}
}
}
case 1:
{
lean_object* v_pre_1321_; 
v_pre_1321_ = lean_ctor_get(v_pre_1310_, 0);
if (lean_obj_tag(v_pre_1321_) == 0)
{
lean_object* v_str_1322_; lean_object* v_str_1323_; lean_object* v_str_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_str_1322_ = lean_ctor_get(v_x_1308_, 1);
v_str_1323_ = lean_ctor_get(v_pre_1309_, 1);
v_str_1324_ = lean_ctor_get(v_pre_1310_, 1);
v___x_1325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1326_ = lean_string_dec_eq(v_str_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
return v___y_1306_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1328_ = lean_string_dec_eq(v_str_1323_, v___x_1327_);
if (v___x_1328_ == 0)
{
return v___y_1306_;
}
else
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1330_ = lean_string_dec_eq(v_str_1322_, v___x_1329_);
if (v___x_1330_ == 0)
{
return v___y_1306_;
}
else
{
return v_suppressElabErrors_1307_;
}
}
}
}
else
{
return v___y_1306_;
}
}
default: 
{
return v___y_1306_;
}
}
}
case 0:
{
lean_object* v_str_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_str_1331_ = lean_ctor_get(v_x_1308_, 1);
v___x_1332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1333_ = lean_string_dec_eq(v_str_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
return v___y_1306_;
}
else
{
return v_suppressElabErrors_1307_;
}
}
default: 
{
return v___y_1306_;
}
}
}
else
{
return v___y_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v___y_1334_, lean_object* v_suppressElabErrors_1335_, lean_object* v_x_1336_){
_start:
{
uint8_t v___y_94080__boxed_1337_; uint8_t v_suppressElabErrors_boxed_1338_; uint8_t v_res_1339_; lean_object* v_r_1340_; 
v___y_94080__boxed_1337_ = lean_unbox(v___y_1334_);
v_suppressElabErrors_boxed_1338_ = lean_unbox(v_suppressElabErrors_1335_);
v_res_1339_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v___y_94080__boxed_1337_, v_suppressElabErrors_boxed_1338_, v_x_1336_);
lean_dec(v_x_1336_);
v_r_1340_ = lean_box(v_res_1339_);
return v_r_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1342_, lean_object* v_msgData_1343_, uint8_t v_severity_1344_, uint8_t v_isSilent_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; uint8_t v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1388_; lean_object* v___y_1389_; uint8_t v___y_1390_; uint8_t v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v___y_1416_; uint8_t v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; uint8_t v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; uint8_t v___x_1435_; lean_object* v___y_1437_; lean_object* v___y_1438_; uint8_t v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; uint8_t v___y_1442_; uint8_t v___y_1443_; uint8_t v___y_1445_; uint8_t v___x_1460_; 
v___x_1435_ = 2;
v___x_1460_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1344_, v___x_1435_);
if (v___x_1460_ == 0)
{
v___y_1445_ = v___x_1460_;
goto v___jp_1444_;
}
else
{
uint8_t v___x_1461_; 
lean_inc_ref(v_msgData_1343_);
v___x_1461_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1343_);
v___y_1445_ = v___x_1461_;
goto v___jp_1444_;
}
v___jp_1351_:
{
lean_object* v___x_1361_; lean_object* v_currNamespace_1362_; lean_object* v_openDecls_1363_; lean_object* v_env_1364_; lean_object* v_nextMacroScope_1365_; lean_object* v_ngen_1366_; lean_object* v_auxDeclNGen_1367_; lean_object* v_traceState_1368_; lean_object* v_cache_1369_; lean_object* v_messages_1370_; lean_object* v_infoState_1371_; lean_object* v_snapshotTasks_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1386_; 
v___x_1361_ = lean_st_ref_take(v___y_1360_);
v_currNamespace_1362_ = lean_ctor_get(v___y_1359_, 6);
v_openDecls_1363_ = lean_ctor_get(v___y_1359_, 7);
v_env_1364_ = lean_ctor_get(v___x_1361_, 0);
v_nextMacroScope_1365_ = lean_ctor_get(v___x_1361_, 1);
v_ngen_1366_ = lean_ctor_get(v___x_1361_, 2);
v_auxDeclNGen_1367_ = lean_ctor_get(v___x_1361_, 3);
v_traceState_1368_ = lean_ctor_get(v___x_1361_, 4);
v_cache_1369_ = lean_ctor_get(v___x_1361_, 5);
v_messages_1370_ = lean_ctor_get(v___x_1361_, 6);
v_infoState_1371_ = lean_ctor_get(v___x_1361_, 7);
v_snapshotTasks_1372_ = lean_ctor_get(v___x_1361_, 8);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1374_ = v___x_1361_;
v_isShared_1375_ = v_isSharedCheck_1386_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snapshotTasks_1372_);
lean_inc(v_infoState_1371_);
lean_inc(v_messages_1370_);
lean_inc(v_cache_1369_);
lean_inc(v_traceState_1368_);
lean_inc(v_auxDeclNGen_1367_);
lean_inc(v_ngen_1366_);
lean_inc(v_nextMacroScope_1365_);
lean_inc(v_env_1364_);
lean_dec(v___x_1361_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1386_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_inc(v_openDecls_1363_);
lean_inc(v_currNamespace_1362_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_currNamespace_1362_);
lean_ctor_set(v___x_1376_, 1, v_openDecls_1363_);
v___x_1377_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___y_1353_);
lean_inc_ref(v___y_1356_);
lean_inc_ref(v___y_1357_);
v___x_1378_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1378_, 0, v___y_1357_);
lean_ctor_set(v___x_1378_, 1, v___y_1358_);
lean_ctor_set(v___x_1378_, 2, v___y_1352_);
lean_ctor_set(v___x_1378_, 3, v___y_1356_);
lean_ctor_set(v___x_1378_, 4, v___x_1377_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*5, v___y_1354_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*5 + 1, v___y_1355_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*5 + 2, v_isSilent_1345_);
v___x_1379_ = l_Lean_MessageLog_add(v___x_1378_, v_messages_1370_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 6, v___x_1379_);
v___x_1381_ = v___x_1374_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_env_1364_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_nextMacroScope_1365_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_ngen_1366_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_auxDeclNGen_1367_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_traceState_1368_);
lean_ctor_set(v_reuseFailAlloc_1385_, 5, v_cache_1369_);
lean_ctor_set(v_reuseFailAlloc_1385_, 6, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1385_, 7, v_infoState_1371_);
lean_ctor_set(v_reuseFailAlloc_1385_, 8, v_snapshotTasks_1372_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_st_ref_set(v___y_1360_, v___x_1381_);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
v___jp_1387_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1411_; 
v___x_1396_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1343_);
v___x_1397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v___x_1396_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_inc_ref_n(v___y_1389_, 2);
v___x_1402_ = l_Lean_FileMap_toPosition(v___y_1389_, v___y_1392_);
lean_dec(v___y_1392_);
v___x_1403_ = l_Lean_FileMap_toPosition(v___y_1389_, v___y_1395_);
lean_dec(v___y_1395_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
v___x_1405_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1390_ == 0)
{
lean_del_object(v___x_1400_);
lean_dec_ref(v___y_1388_);
v___y_1352_ = v___x_1404_;
v___y_1353_ = v_a_1398_;
v___y_1354_ = v___y_1391_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___x_1405_;
v___y_1357_ = v___y_1394_;
v___y_1358_ = v___x_1402_;
v___y_1359_ = v___y_1348_;
v___y_1360_ = v___y_1349_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1406_; 
lean_inc(v_a_1398_);
v___x_1406_ = l_Lean_MessageData_hasTag(v___y_1388_, v_a_1398_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec_ref_known(v___x_1404_, 1);
lean_dec_ref(v___x_1402_);
lean_dec(v_a_1398_);
v___x_1407_ = lean_box(0);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1407_);
v___x_1409_ = v___x_1400_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_del_object(v___x_1400_);
v___y_1352_ = v___x_1404_;
v___y_1353_ = v_a_1398_;
v___y_1354_ = v___y_1391_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___x_1405_;
v___y_1357_ = v___y_1394_;
v___y_1358_ = v___x_1402_;
v___y_1359_ = v___y_1348_;
v___y_1360_ = v___y_1349_;
goto v___jp_1351_;
}
}
}
}
v___jp_1412_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Syntax_getTailPos_x3f(v___y_1414_, v___y_1417_);
lean_dec(v___y_1414_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_inc(v___y_1420_);
v___y_1388_ = v___y_1413_;
v___y_1389_ = v___y_1415_;
v___y_1390_ = v___y_1416_;
v___y_1391_ = v___y_1417_;
v___y_1392_ = v___y_1420_;
v___y_1393_ = v___y_1418_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1420_;
goto v___jp_1387_;
}
else
{
lean_object* v_val_1422_; 
v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___y_1388_ = v___y_1413_;
v___y_1389_ = v___y_1415_;
v___y_1390_ = v___y_1416_;
v___y_1391_ = v___y_1417_;
v___y_1392_ = v___y_1420_;
v___y_1393_ = v___y_1418_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v_val_1422_;
goto v___jp_1387_;
}
}
v___jp_1423_:
{
lean_object* v_ref_1431_; lean_object* v___x_1432_; 
v_ref_1431_ = l_Lean_replaceRef(v_ref_1342_, v___y_1425_);
v___x_1432_ = l_Lean_Syntax_getPos_x3f(v_ref_1431_, v___y_1428_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___y_1413_ = v___y_1424_;
v___y_1414_ = v_ref_1431_;
v___y_1415_ = v___y_1426_;
v___y_1416_ = v___y_1427_;
v___y_1417_ = v___y_1428_;
v___y_1418_ = v___y_1430_;
v___y_1419_ = v___y_1429_;
v___y_1420_ = v___x_1433_;
goto v___jp_1412_;
}
else
{
lean_object* v_val_1434_; 
v_val_1434_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v___x_1432_, 1);
v___y_1413_ = v___y_1424_;
v___y_1414_ = v_ref_1431_;
v___y_1415_ = v___y_1426_;
v___y_1416_ = v___y_1427_;
v___y_1417_ = v___y_1428_;
v___y_1418_ = v___y_1430_;
v___y_1419_ = v___y_1429_;
v___y_1420_ = v_val_1434_;
goto v___jp_1412_;
}
}
v___jp_1436_:
{
if (v___y_1443_ == 0)
{
v___y_1424_ = v___y_1440_;
v___y_1425_ = v___y_1437_;
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___y_1439_;
v___y_1428_ = v___y_1442_;
v___y_1429_ = v___y_1441_;
v___y_1430_ = v_severity_1344_;
goto v___jp_1423_;
}
else
{
v___y_1424_ = v___y_1440_;
v___y_1425_ = v___y_1437_;
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___y_1439_;
v___y_1428_ = v___y_1442_;
v___y_1429_ = v___y_1441_;
v___y_1430_ = v___x_1435_;
goto v___jp_1423_;
}
}
v___jp_1444_:
{
if (v___y_1445_ == 0)
{
lean_object* v_fileName_1446_; lean_object* v_fileMap_1447_; lean_object* v_options_1448_; lean_object* v_ref_1449_; uint8_t v_suppressElabErrors_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; uint8_t v___x_1454_; uint8_t v___x_1455_; 
v_fileName_1446_ = lean_ctor_get(v___y_1348_, 0);
v_fileMap_1447_ = lean_ctor_get(v___y_1348_, 1);
v_options_1448_ = lean_ctor_get(v___y_1348_, 2);
v_ref_1449_ = lean_ctor_get(v___y_1348_, 5);
v_suppressElabErrors_1450_ = lean_ctor_get_uint8(v___y_1348_, sizeof(void*)*14 + 1);
v___x_1451_ = lean_box(v___y_1445_);
v___x_1452_ = lean_box(v_suppressElabErrors_1450_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1453_, 0, v___x_1451_);
lean_closure_set(v___f_1453_, 1, v___x_1452_);
v___x_1454_ = 1;
v___x_1455_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1344_, v___x_1454_);
if (v___x_1455_ == 0)
{
v___y_1437_ = v_ref_1449_;
v___y_1438_ = v_fileMap_1447_;
v___y_1439_ = v_suppressElabErrors_1450_;
v___y_1440_ = v___f_1453_;
v___y_1441_ = v_fileName_1446_;
v___y_1442_ = v___y_1445_;
v___y_1443_ = v___x_1455_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1456_ = l_Lean_warningAsError;
v___x_1457_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_1448_, v___x_1456_);
v___y_1437_ = v_ref_1449_;
v___y_1438_ = v_fileMap_1447_;
v___y_1439_ = v_suppressElabErrors_1450_;
v___y_1440_ = v___f_1453_;
v___y_1441_ = v_fileName_1446_;
v___y_1442_ = v___y_1445_;
v___y_1443_ = v___x_1457_;
goto v___jp_1436_;
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_msgData_1343_);
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1462_, lean_object* v_msgData_1463_, lean_object* v_severity_1464_, lean_object* v_isSilent_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v_severity_boxed_1471_; uint8_t v_isSilent_boxed_1472_; lean_object* v_res_1473_; 
v_severity_boxed_1471_ = lean_unbox(v_severity_1464_);
v_isSilent_boxed_1472_ = lean_unbox(v_isSilent_1465_);
v_res_1473_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1462_, v_msgData_1463_, v_severity_boxed_1471_, v_isSilent_boxed_1472_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v_ref_1462_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(lean_object* v_ref_1474_, lean_object* v_msgData_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = 1;
v___x_1486_ = 0;
v___x_1487_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1474_, v_msgData_1475_, v___x_1485_, v___x_1486_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(lean_object* v_ref_1488_, lean_object* v_msgData_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_ref_1488_, v_msgData_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v_ref_1488_);
return v_res_1499_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0));
v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2));
v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_linterOption_1506_, lean_object* v_stx_1507_, lean_object* v_msg_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_name_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1536_; 
v_name_1518_ = lean_ctor_get(v_linterOption_1506_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_linterOption_1506_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_linterOption_1506_, 1);
lean_dec(v_unused_1537_);
v___x_1520_ = v_linterOption_1506_;
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_name_1518_);
lean_dec(v_linterOption_1506_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1536_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
lean_inc(v_name_1518_);
v___x_1523_ = l_Lean_MessageData_ofName(v_name_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 7);
lean_ctor_set(v___x_1520_, 1, v___x_1523_);
lean_ctor_set(v___x_1520_, 0, v___x_1522_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_disable_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1526_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v_disable_1528_ = l_Lean_MessageData_note(v___x_1527_);
v___x_1529_ = l_Lean_Linter_linterMessageTag;
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_msg_1508_);
lean_ctor_set(v___x_1530_, 1, v_disable_1528_);
v___x_1531_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_name_1518_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
lean_inc(v_stx_1507_);
v___x_1533_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_stx_1507_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_stx_1507_, v___x_1533_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v_stx_1507_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_linterOption_1538_, lean_object* v_stx_1539_, lean_object* v_msg_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_linterOption_1538_, v_stx_1539_, v_msg_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object* v___y_1551_, lean_object* v_mkInfoTree_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v_a_1560_, lean_object* v_a_x3f_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v_infoState_1564_; lean_object* v_trees_1565_; lean_object* v___x_1566_; 
v___x_1563_ = lean_st_ref_get(v___y_1551_);
v_infoState_1564_ = lean_ctor_get(v___x_1563_, 7);
lean_inc_ref(v_infoState_1564_);
lean_dec(v___x_1563_);
v_trees_1565_ = lean_ctor_get(v_infoState_1564_, 2);
lean_inc_ref(v_trees_1565_);
lean_dec_ref(v_infoState_1564_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1559_);
lean_inc(v___y_1558_);
lean_inc_ref(v___y_1557_);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
v___x_1566_ = lean_apply_10(v_mkInfoTree_1552_, v_trees_1565_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1551_, lean_box(0));
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1605_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1605_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1605_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v_infoState_1572_; lean_object* v_env_1573_; lean_object* v_nextMacroScope_1574_; lean_object* v_ngen_1575_; lean_object* v_auxDeclNGen_1576_; lean_object* v_traceState_1577_; lean_object* v_cache_1578_; lean_object* v_messages_1579_; lean_object* v_snapshotTasks_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1604_; 
v___x_1571_ = lean_st_ref_take(v___y_1551_);
v_infoState_1572_ = lean_ctor_get(v___x_1571_, 7);
v_env_1573_ = lean_ctor_get(v___x_1571_, 0);
v_nextMacroScope_1574_ = lean_ctor_get(v___x_1571_, 1);
v_ngen_1575_ = lean_ctor_get(v___x_1571_, 2);
v_auxDeclNGen_1576_ = lean_ctor_get(v___x_1571_, 3);
v_traceState_1577_ = lean_ctor_get(v___x_1571_, 4);
v_cache_1578_ = lean_ctor_get(v___x_1571_, 5);
v_messages_1579_ = lean_ctor_get(v___x_1571_, 6);
v_snapshotTasks_1580_ = lean_ctor_get(v___x_1571_, 8);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1582_ = v___x_1571_;
v_isShared_1583_ = v_isSharedCheck_1604_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_snapshotTasks_1580_);
lean_inc(v_infoState_1572_);
lean_inc(v_messages_1579_);
lean_inc(v_cache_1578_);
lean_inc(v_traceState_1577_);
lean_inc(v_auxDeclNGen_1576_);
lean_inc(v_ngen_1575_);
lean_inc(v_nextMacroScope_1574_);
lean_inc(v_env_1573_);
lean_dec(v___x_1571_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1604_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v_enabled_1584_; lean_object* v_assignment_1585_; lean_object* v_lazyAssignment_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1602_; 
v_enabled_1584_ = lean_ctor_get_uint8(v_infoState_1572_, sizeof(void*)*3);
v_assignment_1585_ = lean_ctor_get(v_infoState_1572_, 0);
v_lazyAssignment_1586_ = lean_ctor_get(v_infoState_1572_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_infoState_1572_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v_infoState_1572_, 2);
lean_dec(v_unused_1603_);
v___x_1588_ = v_infoState_1572_;
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_lazyAssignment_1586_);
lean_inc(v_assignment_1585_);
lean_dec(v_infoState_1572_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1602_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = l_Lean_PersistentArray_push___redArg(v_a_1560_, v_a_1567_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 2, v___x_1590_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_assignment_1585_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_lazyAssignment_1586_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v___x_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1601_, sizeof(void*)*3, v_enabled_1584_);
v___x_1592_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 7, v___x_1592_);
v___x_1594_ = v___x_1582_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_env_1573_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_nextMacroScope_1574_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_ngen_1575_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_auxDeclNGen_1576_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_traceState_1577_);
lean_ctor_set(v_reuseFailAlloc_1600_, 5, v_cache_1578_);
lean_ctor_set(v_reuseFailAlloc_1600_, 6, v_messages_1579_);
lean_ctor_set(v_reuseFailAlloc_1600_, 7, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1600_, 8, v_snapshotTasks_1580_);
v___x_1594_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = lean_st_ref_set(v___y_1551_, v___x_1594_);
v___x_1596_ = lean_box(0);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1596_);
v___x_1598_ = v___x_1569_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v_a_1560_);
v_a_1606_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1566_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1566_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object* v___y_1614_, lean_object* v_mkInfoTree_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v_a_1623_, lean_object* v_a_x3f_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1614_, v_mkInfoTree_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v_a_1623_, v_a_x3f_1624_);
lean_dec(v_a_x3f_1624_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1614_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object* v_x_1627_, lean_object* v_mkInfoTree_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_infoState_1639_; uint8_t v_enabled_1640_; 
v___x_1638_ = lean_st_ref_get(v___y_1636_);
v_infoState_1639_ = lean_ctor_get(v___x_1638_, 7);
lean_inc_ref(v_infoState_1639_);
lean_dec(v___x_1638_);
v_enabled_1640_ = lean_ctor_get_uint8(v_infoState_1639_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1639_);
if (v_enabled_1640_ == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v_mkInfoTree_1628_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
v___x_1641_ = lean_apply_9(v_x_1627_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, lean_box(0));
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; lean_object* v_a_1643_; lean_object* v_r_1644_; 
v___x_1642_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1636_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1642_);
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
v_r_1644_ = lean_apply_9(v_x_1627_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, lean_box(0));
if (lean_obj_tag(v_r_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1669_; 
v_a_1645_ = lean_ctor_get(v_r_1644_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_r_1644_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1647_ = v_r_1644_;
v_isShared_1648_ = v_isSharedCheck_1669_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v_r_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1669_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
lean_inc(v_a_1645_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1636_, v_mkInfoTree_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v_a_1643_, v___x_1650_);
lean_dec_ref(v___x_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1651_, 0);
lean_dec(v_unused_1659_);
v___x_1653_ = v___x_1651_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v___x_1651_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v_a_1645_);
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1645_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_a_1645_);
v_a_1660_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1651_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1651_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_a_1670_ = lean_ctor_get(v_r_1644_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v_r_1644_, 1);
v___x_1671_ = lean_box(0);
v___x_1672_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1636_, v_mkInfoTree_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v_a_1643_, v___x_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v___x_1672_, 0);
lean_dec(v_unused_1680_);
v___x_1674_ = v___x_1672_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v___x_1672_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set_tag(v___x_1674_, 1);
lean_ctor_set(v___x_1674_, 0, v_a_1670_);
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1670_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1670_);
v_a_1681_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1672_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1672_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object* v_x_1689_, lean_object* v_mkInfoTree_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_1689_, v_mkInfoTree_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; lean_object* v_env_1705_; lean_object* v___x_1706_; lean_object* v_toEnvExtension_1707_; lean_object* v_asyncMode_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_merged_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v___x_1704_ = lean_st_ref_get(v___y_1702_);
v_env_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc_ref(v_env_1705_);
lean_dec(v___x_1704_);
v___x_1706_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1707_ = lean_ctor_get(v___x_1706_, 0);
v_asyncMode_1708_ = lean_ctor_get(v_toEnvExtension_1707_, 2);
v___x_1709_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1710_ = lean_box(0);
v___x_1711_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1709_, v___x_1706_, v_env_1705_, v_asyncMode_1708_, v___x_1710_);
v_merged_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v___x_1711_, 1);
lean_dec(v_unused_1721_);
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_merged_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_merged_1712_);
lean_ctor_set(v___x_1714_, 0, v_o_1701_);
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_o_1701_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_merged_1712_);
v___x_1717_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_1722_, v___y_1723_);
lean_dec(v___y_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_options_1735_; lean_object* v___x_1736_; 
v_options_1735_ = lean_ctor_get(v___y_1732_, 2);
lean_inc_ref(v_options_1735_);
v___x_1736_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_1735_, v___y_1733_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1746_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2));
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6));
v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
return v___x_1758_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8));
v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10));
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_usingArg_1768_, lean_object* v_snd_1769_, uint8_t v___x_1770_, uint8_t v___x_1771_, lean_object* v___x_1772_, uint8_t v_useReducible_1773_, uint8_t v___x_1774_, lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v_simprocs_1777_, lean_object* v_discharge_x3f_1778_, lean_object* v_snd_1779_, lean_object* v___x_1780_, lean_object* v___f_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; 
if (lean_obj_tag(v_usingArg_1768_) == 1)
{
lean_object* v_val_1972_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___x_2024_; lean_object* v_infoState_2025_; uint8_t v_enabled_2026_; 
v_val_1972_ = lean_ctor_get(v_usingArg_1768_, 0);
lean_inc(v_val_1972_);
lean_dec_ref_known(v_usingArg_1768_, 1);
v___x_2024_ = lean_st_ref_get(v___y_1789_);
v_infoState_2025_ = lean_ctor_get(v___x_2024_, 7);
lean_inc_ref(v_infoState_2025_);
lean_dec(v___x_2024_);
v_enabled_2026_ = lean_ctor_get_uint8(v_infoState_2025_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2025_);
if (v_enabled_2026_ == 0)
{
lean_dec_ref(v___f_1781_);
v___y_1974_ = v___y_1782_;
v___y_1975_ = v___y_1783_;
v___y_1976_ = v___y_1784_;
v___y_1977_ = v___y_1785_;
v___y_1978_ = v___y_1786_;
v___y_1979_ = v___y_1787_;
v___y_1980_ = v___y_1788_;
v___y_1981_ = v___y_1789_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_2027_; lean_object* v_a_2028_; lean_object* v___f_2029_; lean_object* v___x_2030_; 
v___x_2027_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1789_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___f_2029_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2029_, 0, v_a_2028_);
v___x_2030_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_2029_, v___f_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_dec_ref_known(v___x_2030_, 1);
v___y_1974_ = v___y_1782_;
v___y_1975_ = v___y_1783_;
v___y_1976_ = v___y_1784_;
v___y_1977_ = v___y_1785_;
v___y_1978_ = v___y_1786_;
v___y_1979_ = v___y_1787_;
v___y_1980_ = v___y_1788_;
v___y_1981_ = v___y_1789_;
goto v___jp_1973_;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_val_1972_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
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
}
v___jp_1973_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_st_ref_get(v___y_1979_);
v___x_1983_ = lean_box(0);
v___x_1984_ = l_Lean_Elab_Tactic_elabTerm(v_val_1972_, v___x_1983_, v___x_1770_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc_n(v_a_1985_, 2);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_1769_, v_a_1985_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_mctx_1987_; lean_object* v_a_1988_; uint8_t v___x_1989_; 
v_mctx_1987_ = lean_ctor_get(v___x_1982_, 0);
lean_inc_ref(v_mctx_1987_);
lean_dec(v___x_1982_);
v_a_1988_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1989_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v_mctx_1987_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
v___x_1990_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
v___x_1991_ = l_Lean_indentExpr(v_a_1985_);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_Expr_mvar___override(v_snd_1769_);
v___x_1996_ = l_Lean_MessageData_ofExpr(v___x_1995_);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1994_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_1997_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
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
else
{
lean_object* v_mvarCounter_2007_; 
v_mvarCounter_2007_ = lean_ctor_get(v_mctx_1987_, 3);
lean_inc(v_mvarCounter_2007_);
lean_dec_ref(v_mctx_1987_);
lean_inc(v_a_1985_);
v___y_1856_ = v___x_1983_;
v___y_1857_ = v_a_1985_;
v___y_1858_ = v_mvarCounter_2007_;
v___y_1859_ = v___x_1983_;
v___y_1860_ = v_a_1985_;
v___y_1861_ = v___y_1974_;
v___y_1862_ = v___y_1975_;
v___y_1863_ = v___y_1976_;
v___y_1864_ = v___y_1977_;
v___y_1865_ = v___y_1978_;
v___y_1866_ = v___y_1979_;
v___y_1867_ = v___y_1980_;
v___y_1868_ = v___y_1981_;
goto v___jp_1855_;
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1985_);
lean_dec(v___x_1982_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_2008_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1986_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1986_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v___x_1982_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_2016_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1984_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1984_);
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
else
{
lean_object* v_lctx_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v___f_1781_);
lean_dec_ref(v___x_1772_);
lean_dec(v_usingArg_1768_);
v_lctx_2039_ = lean_ctor_get(v___y_1786_, 2);
v___x_2040_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13));
v___x_2041_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2039_, v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 1)
{
lean_object* v_val_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_LocalDecl_fvarId(v_val_2042_);
lean_dec(v_val_2042_);
v___x_2044_ = lean_mk_empty_array_with_capacity(v___x_1775_);
v___x_2045_ = lean_array_push(v___x_2044_, v___x_2043_);
lean_inc_ref(v_snd_1779_);
v___x_2046_ = l_Lean_Meta_simpGoal(v_snd_1769_, v___x_1776_, v_simprocs_1777_, v_discharge_x3f_1778_, v___x_1771_, v___x_2045_, v_snd_1779_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2075_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2075_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2075_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_fst_2051_; 
v_fst_2051_ = lean_ctor_get(v_a_2047_, 0);
if (lean_obj_tag(v_fst_2051_) == 1)
{
lean_object* v_val_2052_; lean_object* v_snd_2053_; lean_object* v_snd_2054_; lean_object* v___x_2055_; 
lean_del_object(v___x_2049_);
lean_dec_ref(v_snd_1779_);
v_val_2052_ = lean_ctor_get(v_fst_2051_, 0);
lean_inc(v_val_2052_);
v_snd_2053_ = lean_ctor_get(v_a_2047_, 1);
lean_inc(v_snd_2053_);
lean_dec(v_a_2047_);
v_snd_2054_ = lean_ctor_get(v_val_2052_, 1);
lean_inc(v_snd_2054_);
lean_dec(v_val_2052_);
v___x_2055_ = l_Lean_MVarId_assumption(v_snd_2054_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v___x_2055_, 0);
lean_dec(v_unused_2063_);
v___x_2057_ = v___x_2055_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v___x_2055_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_snd_2053_);
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_snd_2053_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_snd_2053_);
v_a_2064_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2055_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2055_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v___x_2073_; 
lean_dec(v_a_2047_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v_snd_1779_);
v___x_2073_ = v___x_2049_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_snd_1779_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref(v_snd_1779_);
v_a_2076_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2046_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2046_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v___x_2084_; 
lean_dec(v___x_2041_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
v___x_2084_ = l_Lean_MVarId_assumption(v_snd_1769_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v___x_2084_, 0);
lean_dec(v_unused_2092_);
v___x_2086_ = v___x_2084_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_dec(v___x_2084_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v_snd_1779_);
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_snd_1779_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec_ref(v_snd_1779_);
v_a_2093_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2084_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2084_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
v___jp_1791_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v___x_1795_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_1769_, v___y_1793_, v___y_1794_);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v___x_1795_, 0);
lean_dec(v_unused_1803_);
v___x_1797_ = v___x_1795_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_dec(v___x_1795_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___y_1792_);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___y_1792_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
v___jp_1804_:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Core_mkFreshUserName(v___y_1815_, v___y_1813_, v___y_1810_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc_n(v_a_1822_, 2);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = l_Lean_MVarId_rename(v___y_1812_, v___y_1820_, v_a_1822_, v___y_1809_, v___y_1814_, v___y_1813_, v___y_1810_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_n(v_a_1824_, 2);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1825_ = lean_box(v___x_1770_);
v___x_1826_ = lean_box(v___x_1771_);
v___x_1827_ = lean_box(v_useReducible_1773_);
v___x_1828_ = lean_box(v___x_1774_);
v___f_1829_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 19, 10);
lean_closure_set(v___f_1829_, 0, v_a_1824_);
lean_closure_set(v___f_1829_, 1, v_a_1822_);
lean_closure_set(v___f_1829_, 2, v___x_1825_);
lean_closure_set(v___f_1829_, 3, v___x_1826_);
lean_closure_set(v___f_1829_, 4, v___y_1806_);
lean_closure_set(v___f_1829_, 5, v___y_1807_);
lean_closure_set(v___f_1829_, 6, v___x_1772_);
lean_closure_set(v___f_1829_, 7, v___y_1805_);
lean_closure_set(v___f_1829_, 8, v___x_1827_);
lean_closure_set(v___f_1829_, 9, v___x_1828_);
v___x_1830_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1824_, v___f_1829_, v___y_1817_, v___y_1808_, v___y_1818_, v___y_1816_, v___y_1809_, v___y_1814_, v___y_1813_, v___y_1810_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_dec_ref_known(v___x_1830_, 1);
v___y_1792_ = v___y_1811_;
v___y_1793_ = v___y_1819_;
v___y_1794_ = v___y_1814_;
goto v___jp_1791_;
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v___y_1819_);
lean_dec_ref(v___y_1811_);
lean_dec(v_snd_1769_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_a_1822_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_1839_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1823_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1823_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_1847_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1821_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1821_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
v___jp_1855_:
{
lean_object* v___x_1869_; 
lean_inc(v_snd_1769_);
v___x_1869_ = l_Lean_MVarId_getType(v_snd_1769_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
lean_inc(v_snd_1769_);
v___x_1871_ = l_Lean_MVarId_getTag(v_snd_1769_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1870_, v_a_1872_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v___x_1875_ = l_Lean_Expr_mvarId_x21(v_a_1874_);
v___x_1876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1));
lean_inc_ref(v___y_1860_);
v___x_1877_ = l_Lean_MVarId_note(v___x_1875_, v___x_1876_, v___y_1860_, v___y_1859_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v_fst_1879_; lean_object* v_snd_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1939_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v_fst_1879_ = lean_ctor_get(v_a_1878_, 0);
v_snd_1880_ = lean_ctor_get(v_a_1878_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_a_1878_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1882_ = v_a_1878_;
v_isShared_1883_ = v_isSharedCheck_1939_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_snd_1880_);
lean_inc(v_fst_1879_);
lean_dec(v_a_1878_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1939_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_mk_empty_array_with_capacity(v___x_1775_);
lean_inc(v_fst_1879_);
v___x_1885_ = lean_array_push(v___x_1884_, v_fst_1879_);
v___x_1886_ = l_Lean_Meta_simpGoal(v_snd_1880_, v___x_1776_, v_simprocs_1777_, v_discharge_x3f_1778_, v___x_1771_, v___x_1885_, v_snd_1779_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_fst_1888_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v_fst_1888_ = lean_ctor_get(v_a_1887_, 0);
if (lean_obj_tag(v_fst_1888_) == 0)
{
lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_fst_1879_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___x_1772_);
v_snd_1889_ = lean_ctor_get(v_a_1887_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_a_1887_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_a_1887_, 0);
lean_dec(v_unused_1923_);
v___x_1891_ = v_a_1887_;
v_isShared_1892_ = v_isSharedCheck_1922_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_dec(v_a_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1922_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v_a_1894_; uint8_t v___x_1895_; 
v___x_1893_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref(v___x_1893_);
v___x_1895_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1894_);
lean_dec(v_a_1894_);
if (v___x_1895_ == 0)
{
lean_del_object(v___x_1891_);
lean_del_object(v___x_1882_);
lean_dec_ref(v___y_1860_);
v___y_1792_ = v_snd_1889_;
v___y_1793_ = v_a_1874_;
v___y_1794_ = v___y_1866_;
goto v___jp_1791_;
}
else
{
if (lean_obj_tag(v___y_1860_) == 1)
{
lean_object* v_fvarId_1896_; lean_object* v_lctx_1897_; lean_object* v___x_1898_; 
v_fvarId_1896_ = lean_ctor_get(v___y_1860_, 0);
v_lctx_1897_ = lean_ctor_get(v___y_1865_, 2);
lean_inc(v_fvarId_1896_);
lean_inc_ref(v_lctx_1897_);
v___x_1898_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1897_, v_fvarId_1896_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_dec_ref_known(v___y_1860_, 1);
lean_del_object(v___x_1891_);
lean_del_object(v___x_1882_);
v___y_1792_ = v_snd_1889_;
v___y_1793_ = v_a_1874_;
v___y_1794_ = v___y_1866_;
goto v___jp_1791_;
}
else
{
lean_dec_ref_known(v___x_1898_, 1);
if (v___x_1774_ == 0)
{
lean_dec_ref_known(v___y_1860_, 1);
lean_del_object(v___x_1891_);
lean_del_object(v___x_1882_);
v___y_1792_ = v_snd_1889_;
v___y_1793_ = v_a_1874_;
v___y_1794_ = v___y_1866_;
goto v___jp_1791_;
}
else
{
lean_object* v_ref_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v_ref_1899_ = lean_ctor_get(v___y_1867_, 5);
v___x_1900_ = l_Lean_linter_unnecessarySimpa;
v___x_1901_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_1902_ = l_Lean_MessageData_ofExpr(v___y_1860_);
lean_inc_ref(v___x_1902_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 7);
lean_ctor_set(v___x_1891_, 1, v___x_1902_);
lean_ctor_set(v___x_1891_, 0, v___x_1901_);
v___x_1904_ = v___x_1891_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 7);
lean_ctor_set(v___x_1882_, 1, v___x_1905_);
lean_ctor_set(v___x_1882_, 0, v___x_1904_);
v___x_1907_ = v___x_1882_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1902_);
v___x_1909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
lean_inc(v_ref_1899_);
v___x_1911_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_1900_, v_ref_1899_, v___x_1910_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_dec_ref_known(v___x_1911_, 1);
v___y_1792_ = v_snd_1889_;
v___y_1793_ = v_a_1874_;
v___y_1794_ = v___y_1866_;
goto v___jp_1791_;
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_snd_1889_);
lean_dec(v_a_1874_);
lean_dec(v_snd_1769_);
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
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
lean_del_object(v___x_1891_);
lean_del_object(v___x_1882_);
lean_dec_ref(v___y_1860_);
v___y_1792_ = v_snd_1889_;
v___y_1793_ = v_a_1874_;
v___y_1794_ = v___y_1866_;
goto v___jp_1791_;
}
}
}
}
else
{
lean_object* v_val_1924_; lean_object* v_snd_1925_; lean_object* v_fst_1926_; lean_object* v_snd_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
lean_del_object(v___x_1882_);
lean_dec_ref(v___y_1860_);
v_val_1924_ = lean_ctor_get(v_fst_1888_, 0);
lean_inc(v_val_1924_);
v_snd_1925_ = lean_ctor_get(v_a_1887_, 1);
lean_inc(v_snd_1925_);
lean_dec(v_a_1887_);
v_fst_1926_ = lean_ctor_get(v_val_1924_, 0);
lean_inc(v_fst_1926_);
v_snd_1927_ = lean_ctor_get(v_val_1924_, 1);
lean_inc(v_snd_1927_);
lean_dec(v_val_1924_);
v___x_1928_ = lean_array_get_size(v_fst_1926_);
v___x_1929_ = lean_nat_dec_lt(v___x_1780_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_dec(v_fst_1926_);
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___y_1857_;
v___y_1807_ = v___y_1858_;
v___y_1808_ = v___y_1862_;
v___y_1809_ = v___y_1865_;
v___y_1810_ = v___y_1868_;
v___y_1811_ = v_snd_1925_;
v___y_1812_ = v_snd_1927_;
v___y_1813_ = v___y_1867_;
v___y_1814_ = v___y_1866_;
v___y_1815_ = v___x_1876_;
v___y_1816_ = v___y_1864_;
v___y_1817_ = v___y_1861_;
v___y_1818_ = v___y_1863_;
v___y_1819_ = v_a_1874_;
v___y_1820_ = v_fst_1879_;
goto v___jp_1804_;
}
else
{
lean_object* v___x_1930_; 
lean_dec(v_fst_1879_);
v___x_1930_ = lean_array_fget(v_fst_1926_, v___x_1780_);
lean_dec(v_fst_1926_);
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___y_1857_;
v___y_1807_ = v___y_1858_;
v___y_1808_ = v___y_1862_;
v___y_1809_ = v___y_1865_;
v___y_1810_ = v___y_1868_;
v___y_1811_ = v_snd_1925_;
v___y_1812_ = v_snd_1927_;
v___y_1813_ = v___y_1867_;
v___y_1814_ = v___y_1866_;
v___y_1815_ = v___x_1876_;
v___y_1816_ = v___y_1864_;
v___y_1817_ = v___y_1861_;
v___y_1818_ = v___y_1863_;
v___y_1819_ = v_a_1874_;
v___y_1820_ = v___x_1930_;
goto v___jp_1804_;
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_del_object(v___x_1882_);
lean_dec(v_fst_1879_);
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_1931_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1886_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1886_);
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
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_a_1874_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_1940_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1877_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1877_);
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
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_1948_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1873_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1873_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_a_1870_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_1956_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1871_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1871_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v_snd_1779_);
lean_dec(v_discharge_x3f_1778_);
lean_dec_ref(v_simprocs_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1772_);
lean_dec(v_snd_1769_);
v_a_1964_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1869_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1869_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2101_ = _args[0];
lean_object* v_snd_2102_ = _args[1];
lean_object* v___x_2103_ = _args[2];
lean_object* v___x_2104_ = _args[3];
lean_object* v___x_2105_ = _args[4];
lean_object* v_useReducible_2106_ = _args[5];
lean_object* v___x_2107_ = _args[6];
lean_object* v___x_2108_ = _args[7];
lean_object* v___x_2109_ = _args[8];
lean_object* v_simprocs_2110_ = _args[9];
lean_object* v_discharge_x3f_2111_ = _args[10];
lean_object* v_snd_2112_ = _args[11];
lean_object* v___x_2113_ = _args[12];
lean_object* v___f_2114_ = _args[13];
lean_object* v___y_2115_ = _args[14];
lean_object* v___y_2116_ = _args[15];
lean_object* v___y_2117_ = _args[16];
lean_object* v___y_2118_ = _args[17];
lean_object* v___y_2119_ = _args[18];
lean_object* v___y_2120_ = _args[19];
lean_object* v___y_2121_ = _args[20];
lean_object* v___y_2122_ = _args[21];
lean_object* v___y_2123_ = _args[22];
_start:
{
uint8_t v___x_94815__boxed_2124_; uint8_t v___x_94816__boxed_2125_; uint8_t v_useReducible_boxed_2126_; uint8_t v___x_94818__boxed_2127_; lean_object* v_res_2128_; 
v___x_94815__boxed_2124_ = lean_unbox(v___x_2103_);
v___x_94816__boxed_2125_ = lean_unbox(v___x_2104_);
v_useReducible_boxed_2126_ = lean_unbox(v_useReducible_2106_);
v___x_94818__boxed_2127_ = lean_unbox(v___x_2107_);
v_res_2128_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2101_, v_snd_2102_, v___x_94815__boxed_2124_, v___x_94816__boxed_2125_, v___x_2105_, v_useReducible_boxed_2126_, v___x_94818__boxed_2127_, v___x_2108_, v___x_2109_, v_simprocs_2110_, v_discharge_x3f_2111_, v_snd_2112_, v___x_2113_, v___f_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___x_2113_);
lean_dec(v___x_2108_);
return v_res_2128_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2129_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_unsigned_to_nat(32u);
v___x_2133_ = lean_mk_empty_array_with_capacity(v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2139_ = l_Lean_MessageData_ofFormat(v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v___x_2140_, lean_object* v_tk_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v___x_2144_, lean_object* v_simprocs_2145_, uint8_t v___x_2146_, lean_object* v_usingArg_2147_, uint8_t v___x_2148_, lean_object* v___x_2149_, uint8_t v_useReducible_2150_, uint8_t v___x_2151_, lean_object* v___x_2152_, lean_object* v_usingTk_x3f_2153_, lean_object* v_discharge_x3f_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___y_2165_; 
if (lean_obj_tag(v_usingTk_x3f_2153_) == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = lean_box(0);
v___y_2165_ = v___x_2270_;
goto v___jp_2164_;
}
else
{
lean_object* v_val_2271_; 
v_val_2271_ = lean_ctor_get(v_usingTk_x3f_2153_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v_usingTk_x3f_2153_, 1);
v___y_2165_ = v_val_2271_;
goto v___jp_2164_;
}
v___jp_2164_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2166_ = lean_mk_empty_array_with_capacity(v___x_2140_);
v___x_2167_ = lean_array_push(v___x_2166_, v_tk_2141_);
v___x_2168_ = lean_array_push(v___x_2167_, v___y_2165_);
v___x_2169_ = lean_box(2);
v___x_2170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2142_);
lean_ctor_set(v___x_2170_, 2, v___x_2168_);
v___x_2171_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2170_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2156_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = lean_mk_empty_array_with_capacity(v___x_2143_);
v___x_2176_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
lean_inc_n(v___x_2143_, 3);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2143_);
v___x_2178_ = lean_unsigned_to_nat(32u);
v___x_2179_ = lean_mk_empty_array_with_capacity(v___x_2178_);
v___x_2180_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
v___x_2181_ = ((size_t)5ULL);
v___x_2182_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2182_, 0, v___x_2180_);
lean_ctor_set(v___x_2182_, 1, v___x_2179_);
lean_ctor_set(v___x_2182_, 2, v___x_2143_);
lean_ctor_set(v___x_2182_, 3, v___x_2143_);
lean_ctor_set_usize(v___x_2182_, 4, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2176_);
lean_ctor_set(v___x_2183_, 1, v___x_2176_);
lean_ctor_set(v___x_2183_, 2, v___x_2176_);
lean_ctor_set(v___x_2183_, 3, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2177_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
lean_inc_ref(v___x_2184_);
lean_inc(v_discharge_x3f_2154_);
lean_inc_ref(v_simprocs_2145_);
lean_inc_ref(v___x_2144_);
v___x_2185_ = l_Lean_Meta_simpGoal(v_a_2174_, v___x_2144_, v_simprocs_2145_, v_discharge_x3f_2154_, v___x_2146_, v___x_2175_, v___x_2184_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v_fst_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v_fst_2187_ = lean_ctor_get(v_a_2186_, 0);
if (lean_obj_tag(v_fst_2187_) == 1)
{
lean_object* v_val_2188_; lean_object* v_snd_2189_; lean_object* v_snd_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref_known(v___x_2184_, 2);
v_val_2188_ = lean_ctor_get(v_fst_2187_, 0);
lean_inc(v_val_2188_);
v_snd_2189_ = lean_ctor_get(v_a_2186_, 1);
lean_inc(v_snd_2189_);
lean_dec(v_a_2186_);
v_snd_2190_ = lean_ctor_get(v_val_2188_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_val_2188_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v_val_2188_, 0);
lean_dec(v_unused_2215_);
v___x_2192_ = v_val_2188_;
v_isShared_2193_ = v_isSharedCheck_2214_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_snd_2190_);
lean_dec(v_val_2188_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2214_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_box(0);
lean_inc(v_snd_2190_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 1);
lean_ctor_set(v___x_2192_, 1, v___x_2194_);
lean_ctor_set(v___x_2192_, 0, v_snd_2190_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_snd_2190_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2196_, v___y_2156_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___f_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___y_2203_; lean_object* v___x_2204_; 
lean_dec_ref_known(v___x_2197_, 1);
v___f_2198_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2198_, 0, v_a_2172_);
v___x_2199_ = lean_box(v___x_2146_);
v___x_2200_ = lean_box(v___x_2148_);
v___x_2201_ = lean_box(v_useReducible_2150_);
v___x_2202_ = lean_box(v___x_2151_);
lean_inc(v_snd_2190_);
v___y_2203_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 23, 14);
lean_closure_set(v___y_2203_, 0, v_usingArg_2147_);
lean_closure_set(v___y_2203_, 1, v_snd_2190_);
lean_closure_set(v___y_2203_, 2, v___x_2199_);
lean_closure_set(v___y_2203_, 3, v___x_2200_);
lean_closure_set(v___y_2203_, 4, v___x_2149_);
lean_closure_set(v___y_2203_, 5, v___x_2201_);
lean_closure_set(v___y_2203_, 6, v___x_2202_);
lean_closure_set(v___y_2203_, 7, v___x_2152_);
lean_closure_set(v___y_2203_, 8, v___x_2144_);
lean_closure_set(v___y_2203_, 9, v_simprocs_2145_);
lean_closure_set(v___y_2203_, 10, v_discharge_x3f_2154_);
lean_closure_set(v___y_2203_, 11, v_snd_2189_);
lean_closure_set(v___y_2203_, 12, v___x_2143_);
lean_closure_set(v___y_2203_, 13, v___f_2198_);
v___x_2204_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_2190_, v___y_2203_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2204_;
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_snd_2190_);
lean_dec(v_snd_2189_);
lean_dec(v_a_2172_);
lean_dec(v_discharge_x3f_2154_);
lean_dec(v___x_2152_);
lean_dec_ref(v___x_2149_);
lean_dec(v_usingArg_2147_);
lean_dec_ref(v_simprocs_2145_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v_a_2205_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2197_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2197_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_a_2186_);
lean_dec(v_a_2172_);
lean_dec(v_discharge_x3f_2154_);
lean_dec(v___x_2152_);
lean_dec_ref(v___x_2149_);
lean_dec(v_usingArg_2147_);
lean_dec_ref(v_simprocs_2145_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v___x_2216_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2245_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2245_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
uint8_t v___x_2221_; 
v___x_2221_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2217_);
lean_dec(v_a_2217_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2223_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2184_);
v___x_2223_ = v___x_2219_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2184_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
else
{
lean_object* v_ref_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_del_object(v___x_2219_);
v_ref_2225_ = lean_ctor_get(v___y_2161_, 5);
v___x_2226_ = l_Lean_linter_unnecessarySimpa;
v___x_2227_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
lean_inc(v_ref_2225_);
v___x_2228_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2226_, v_ref_2225_, v___x_2227_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; 
v_unused_2236_ = lean_ctor_get(v___x_2228_, 0);
lean_dec(v_unused_2236_);
v___x_2230_ = v___x_2228_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_dec(v___x_2228_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2184_);
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2184_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref_known(v___x_2184_, 2);
v_a_2237_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2228_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2228_);
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
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref_known(v___x_2184_, 2);
lean_dec(v_a_2172_);
lean_dec(v_discharge_x3f_2154_);
lean_dec(v___x_2152_);
lean_dec_ref(v___x_2149_);
lean_dec(v_usingArg_2147_);
lean_dec_ref(v_simprocs_2145_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v_a_2246_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2185_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2185_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2172_);
lean_dec(v_discharge_x3f_2154_);
lean_dec(v___x_2152_);
lean_dec_ref(v___x_2149_);
lean_dec(v_usingArg_2147_);
lean_dec_ref(v_simprocs_2145_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v_a_2254_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2173_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2173_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_discharge_x3f_2154_);
lean_dec(v___x_2152_);
lean_dec_ref(v___x_2149_);
lean_dec(v_usingArg_2147_);
lean_dec_ref(v_simprocs_2145_);
lean_dec_ref(v___x_2144_);
lean_dec(v___x_2143_);
v_a_2262_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2171_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2171_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v___x_2272_ = _args[0];
lean_object* v_tk_2273_ = _args[1];
lean_object* v___x_2274_ = _args[2];
lean_object* v___x_2275_ = _args[3];
lean_object* v___x_2276_ = _args[4];
lean_object* v_simprocs_2277_ = _args[5];
lean_object* v___x_2278_ = _args[6];
lean_object* v_usingArg_2279_ = _args[7];
lean_object* v___x_2280_ = _args[8];
lean_object* v___x_2281_ = _args[9];
lean_object* v_useReducible_2282_ = _args[10];
lean_object* v___x_2283_ = _args[11];
lean_object* v___x_2284_ = _args[12];
lean_object* v_usingTk_x3f_2285_ = _args[13];
lean_object* v_discharge_x3f_2286_ = _args[14];
lean_object* v___y_2287_ = _args[15];
lean_object* v___y_2288_ = _args[16];
lean_object* v___y_2289_ = _args[17];
lean_object* v___y_2290_ = _args[18];
lean_object* v___y_2291_ = _args[19];
lean_object* v___y_2292_ = _args[20];
lean_object* v___y_2293_ = _args[21];
lean_object* v___y_2294_ = _args[22];
lean_object* v___y_2295_ = _args[23];
_start:
{
uint8_t v___x_95539__boxed_2296_; uint8_t v___x_95540__boxed_2297_; uint8_t v_useReducible_boxed_2298_; uint8_t v___x_95542__boxed_2299_; lean_object* v_res_2300_; 
v___x_95539__boxed_2296_ = lean_unbox(v___x_2278_);
v___x_95540__boxed_2297_ = lean_unbox(v___x_2280_);
v_useReducible_boxed_2298_ = lean_unbox(v_useReducible_2282_);
v___x_95542__boxed_2299_ = lean_unbox(v___x_2283_);
v_res_2300_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2272_, v_tk_2273_, v___x_2274_, v___x_2275_, v___x_2276_, v_simprocs_2277_, v___x_95539__boxed_2296_, v_usingArg_2279_, v___x_95540__boxed_2297_, v___x_2281_, v_useReducible_boxed_2298_, v___x_95542__boxed_2299_, v___x_2284_, v_usingTk_x3f_2285_, v_discharge_x3f_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___x_2272_);
return v_res_2300_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2309_ = lean_unsigned_to_nat(38u);
v___x_2310_ = lean_unsigned_to_nat(130u);
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2313_ = l_mkPanicMessageWithDecl(v___x_2312_, v___x_2311_, v___x_2310_, v___x_2309_, v___x_2308_);
return v___x_2313_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Array_mkArray0(lean_box(0));
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2331_ = lean_unsigned_to_nat(15u);
v___x_2332_ = lean_unsigned_to_nat(131u);
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2335_ = l_mkPanicMessageWithDecl(v___x_2334_, v___x_2333_, v___x_2332_, v___x_2331_, v___x_2330_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2337_, lean_object* v___x_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v___x_2341_, uint8_t v___x_2342_, lean_object* v___x_2343_, lean_object* v___x_2344_, uint8_t v_useReducible_2345_, lean_object* v___f_2346_, lean_object* v___x_2347_, lean_object* v___x_2348_, lean_object* v___x_2349_, lean_object* v___x_2350_, lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v_usingArg_2353_, lean_object* v___x_2354_, uint8_t v___x_2355_, lean_object* v_usingTk_x3f_2356_, lean_object* v_squeeze_2357_, lean_object* v_unfold_2358_, lean_object* v_args_2359_, lean_object* v_only_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___y_2372_; lean_object* v___y_2376_; lean_object* v_stx_2377_; lean_object* v___y_2378_; lean_object* v_ref_2379_; lean_object* v___y_2380_; lean_object* v___y_2399_; lean_object* v_stx_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v_options_2425_; lean_object* v_ref_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; uint8_t v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; uint8_t v___y_2841_; lean_object* v_args_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; uint8_t v___y_2881_; lean_object* v_only_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2910_; lean_object* v___y_2911_; uint8_t v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2970_; lean_object* v___y_2971_; uint8_t v___y_2972_; lean_object* v___y_2983_; lean_object* v___y_2984_; uint8_t v___y_2985_; uint8_t v___y_2986_; lean_object* v___y_2988_; lean_object* v___y_2989_; uint8_t v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3060_; 
v_options_2425_ = lean_ctor_get(v___y_2368_, 2);
v_ref_2426_ = lean_ctor_get(v___y_2368_, 5);
v___x_2427_ = 0;
v___x_2428_ = l_Lean_SourceInfo_fromRef(v_ref_2426_, v___x_2427_);
v___x_2429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7));
lean_inc_ref(v___x_2340_);
lean_inc_ref(v___x_2339_);
lean_inc_ref(v___x_2338_);
v___x_2430_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2429_);
lean_inc(v___x_2428_);
v___x_2431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2428_);
lean_ctor_set(v___x_2431_, 1, v___x_2429_);
v___x_2432_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_2433_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_2361_) == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_3060_ = v___x_3069_;
goto v___jp_3059_;
}
else
{
lean_object* v_val_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_val_3070_ = lean_ctor_get(v___y_2361_, 0);
lean_inc(v_val_3070_);
lean_dec_ref_known(v___y_2361_, 1);
v___x_3071_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_3072_ = lean_array_push(v___x_3071_, v_val_3070_);
v___y_3060_ = v___x_3072_;
goto v___jp_3059_;
}
v___jp_2371_:
{
lean_object* v_diag_2373_; lean_object* v___x_2374_; 
v_diag_2373_ = lean_ctor_get(v___y_2372_, 1);
lean_inc_ref(v_diag_2373_);
lean_dec_ref(v___y_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_diag_2373_);
return v___x_2374_;
}
v___jp_2375_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1));
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
lean_ctor_set(v___x_2382_, 1, v_stx_2377_);
v___x_2383_ = lean_box(0);
v___x_2384_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
lean_ctor_set(v___x_2384_, 2, v___x_2383_);
lean_ctor_set(v___x_2384_, 3, v___x_2383_);
lean_ctor_set(v___x_2384_, 4, v___x_2383_);
lean_ctor_set(v___x_2384_, 5, v___x_2383_);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v_ref_2379_);
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2));
v___x_2387_ = 4;
v___x_2388_ = l_Lean_MessageData_nil;
v___x_2389_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2337_, v___x_2384_, v___x_2385_, v___x_2386_, v___x_2383_, v___x_2387_, v___x_2388_, v___y_2378_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2378_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_dec_ref_known(v___x_2389_, 1);
v___y_2372_ = v___y_2376_;
goto v___jp_2371_;
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v___y_2376_);
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
v___jp_2398_:
{
lean_object* v_ref_2403_; 
v_ref_2403_ = lean_ctor_get(v___y_2401_, 5);
lean_inc(v_ref_2403_);
v___y_2376_ = v___y_2399_;
v_stx_2377_ = v_stx_2400_;
v___y_2378_ = v___y_2401_;
v_ref_2379_ = v_ref_2403_;
v___y_2380_ = v___y_2402_;
goto v___jp_2375_;
}
v___jp_2404_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
v___x_2415_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2414_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___y_2399_ = v___y_2405_;
v_stx_2400_ = v_a_2416_;
v___y_2401_ = v___y_2412_;
v___y_2402_ = v___y_2413_;
goto v___jp_2398_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v___y_2405_);
lean_dec(v_tk_2337_);
v_a_2417_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2415_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
v___jp_2434_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = l_Array_append___redArg(v___x_2433_, v___y_2445_);
lean_dec_ref(v___y_2445_);
lean_inc_n(v___y_2440_, 2);
v___x_2447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2447_, 0, v___y_2440_);
lean_ctor_set(v___x_2447_, 1, v___x_2432_);
lean_ctor_set(v___x_2447_, 2, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_node5(v___y_2440_, v___x_2343_, v___y_2439_, v___y_2442_, v___y_2443_, v___y_2444_, v___x_2447_);
v___x_2449_ = l_Lean_Syntax_node2(v___y_2440_, v___y_2437_, v___y_2438_, v___x_2448_);
v___y_2399_ = v___y_2441_;
v_stx_2400_ = v___x_2449_;
v___y_2401_ = v___y_2436_;
v___y_2402_ = v___y_2435_;
goto v___jp_2398_;
}
v___jp_2450_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = l_Array_append___redArg(v___x_2433_, v___y_2461_);
lean_dec_ref(v___y_2461_);
lean_inc(v___y_2456_);
v___x_2463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2463_, 0, v___y_2456_);
lean_ctor_set(v___x_2463_, 1, v___x_2432_);
lean_ctor_set(v___x_2463_, 2, v___x_2462_);
if (lean_obj_tag(v___y_2459_) == 1)
{
lean_object* v_val_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec(v___x_2341_);
v_val_2464_ = lean_ctor_get(v___y_2459_, 0);
lean_inc(v_val_2464_);
lean_dec_ref_known(v___y_2459_, 1);
v___x_2465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2456_);
v___x_2466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___y_2456_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Array_mkArray2___redArg(v___x_2466_, v_val_2464_);
v___y_2435_ = v___y_2451_;
v___y_2436_ = v___y_2453_;
v___y_2437_ = v___y_2452_;
v___y_2438_ = v___y_2454_;
v___y_2439_ = v___y_2455_;
v___y_2440_ = v___y_2456_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v___y_2457_;
v___y_2443_ = v___y_2460_;
v___y_2444_ = v___x_2463_;
v___y_2445_ = v___x_2467_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2468_; 
lean_dec(v___y_2459_);
v___x_2468_ = lean_mk_empty_array_with_capacity(v___x_2341_);
lean_dec(v___x_2341_);
v___y_2435_ = v___y_2451_;
v___y_2436_ = v___y_2453_;
v___y_2437_ = v___y_2452_;
v___y_2438_ = v___y_2454_;
v___y_2439_ = v___y_2455_;
v___y_2440_ = v___y_2456_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v___y_2457_;
v___y_2443_ = v___y_2460_;
v___y_2444_ = v___x_2463_;
v___y_2445_ = v___x_2468_;
goto v___jp_2434_;
}
}
v___jp_2469_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = l_Array_append___redArg(v___x_2433_, v___y_2480_);
lean_dec_ref(v___y_2480_);
lean_inc(v___y_2475_);
v___x_2482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2482_, 0, v___y_2475_);
lean_ctor_set(v___x_2482_, 1, v___x_2432_);
lean_ctor_set(v___x_2482_, 2, v___x_2481_);
if (lean_obj_tag(v___y_2476_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_val_2483_ = lean_ctor_get(v___y_2476_, 0);
lean_inc(v_val_2483_);
lean_dec_ref_known(v___y_2476_, 1);
v___x_2484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2485_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2484_);
v___x_2486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2475_, 4);
v___x_2487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___y_2475_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = l_Array_append___redArg(v___x_2433_, v_val_2483_);
lean_dec(v_val_2483_);
v___x_2489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2489_, 0, v___y_2475_);
lean_ctor_set(v___x_2489_, 1, v___x_2432_);
lean_ctor_set(v___x_2489_, 2, v___x_2488_);
v___x_2490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___y_2475_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = l_Lean_Syntax_node3(v___y_2475_, v___x_2485_, v___x_2487_, v___x_2489_, v___x_2491_);
v___x_2493_ = l_Array_mkArray1___redArg(v___x_2492_);
v___y_2451_ = v___y_2470_;
v___y_2452_ = v___y_2472_;
v___y_2453_ = v___y_2471_;
v___y_2454_ = v___y_2473_;
v___y_2455_ = v___y_2474_;
v___y_2456_ = v___y_2475_;
v___y_2457_ = v___y_2478_;
v___y_2458_ = v___y_2477_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___x_2482_;
v___y_2461_ = v___x_2493_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2494_; 
lean_dec(v___y_2476_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2494_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2451_ = v___y_2470_;
v___y_2452_ = v___y_2472_;
v___y_2453_ = v___y_2471_;
v___y_2454_ = v___y_2473_;
v___y_2455_ = v___y_2474_;
v___y_2456_ = v___y_2475_;
v___y_2457_ = v___y_2478_;
v___y_2458_ = v___y_2477_;
v___y_2459_ = v___y_2479_;
v___y_2460_ = v___x_2482_;
v___y_2461_ = v___x_2494_;
goto v___jp_2450_;
}
}
v___jp_2495_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = l_Array_append___redArg(v___x_2433_, v___y_2506_);
lean_dec_ref(v___y_2506_);
lean_inc(v___y_2501_);
v___x_2508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2501_);
lean_ctor_set(v___x_2508_, 1, v___x_2432_);
lean_ctor_set(v___x_2508_, 2, v___x_2507_);
if (lean_obj_tag(v___y_2502_) == 1)
{
lean_object* v_val_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_val_2509_ = lean_ctor_get(v___y_2502_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v___y_2502_, 1);
v___x_2510_ = l_Lean_SourceInfo_fromRef(v_val_2509_, v___x_2342_);
lean_dec(v_val_2509_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = l_Array_mkArray1___redArg(v___x_2512_);
v___y_2470_ = v___y_2496_;
v___y_2471_ = v___y_2498_;
v___y_2472_ = v___y_2497_;
v___y_2473_ = v___y_2499_;
v___y_2474_ = v___y_2500_;
v___y_2475_ = v___y_2501_;
v___y_2476_ = v___y_2504_;
v___y_2477_ = v___y_2503_;
v___y_2478_ = v___x_2508_;
v___y_2479_ = v___y_2505_;
v___y_2480_ = v___x_2513_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2514_; 
lean_dec(v___y_2502_);
v___x_2514_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2470_ = v___y_2496_;
v___y_2471_ = v___y_2498_;
v___y_2472_ = v___y_2497_;
v___y_2473_ = v___y_2499_;
v___y_2474_ = v___y_2500_;
v___y_2475_ = v___y_2501_;
v___y_2476_ = v___y_2504_;
v___y_2477_ = v___y_2503_;
v___y_2478_ = v___x_2508_;
v___y_2479_ = v___y_2505_;
v___y_2480_ = v___x_2514_;
goto v___jp_2469_;
}
}
v___jp_2515_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2530_ = l_Array_append___redArg(v___x_2433_, v___y_2529_);
lean_dec_ref(v___y_2529_);
lean_inc_n(v___y_2517_, 3);
v___x_2531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2531_, 0, v___y_2517_);
lean_ctor_set(v___x_2531_, 1, v___x_2432_);
lean_ctor_set(v___x_2531_, 2, v___x_2530_);
v___x_2532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___y_2517_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = l_Lean_Syntax_node6(v___y_2517_, v___y_2525_, v___y_2526_, v___y_2528_, v___y_2522_, v___x_2531_, v___x_2533_, v___y_2520_);
v___x_2535_ = l_Lean_Syntax_node4(v___y_2517_, v___y_2521_, v___y_2518_, v___y_2519_, v___y_2523_, v___x_2534_);
v___y_2399_ = v___y_2527_;
v_stx_2400_ = v___x_2535_;
v___y_2401_ = v___y_2524_;
v___y_2402_ = v___y_2516_;
goto v___jp_2398_;
}
v___jp_2536_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = l_Array_append___redArg(v___x_2433_, v___y_2550_);
lean_dec_ref(v___y_2550_);
lean_inc(v___y_2538_);
v___x_2552_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2552_, 0, v___y_2538_);
lean_ctor_set(v___x_2552_, 1, v___x_2432_);
lean_ctor_set(v___x_2552_, 2, v___x_2551_);
if (lean_obj_tag(v___y_2547_) == 1)
{
lean_object* v_val_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec(v___x_2341_);
v_val_2553_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v___y_2547_, 1);
v___x_2554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2555_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2554_);
v___x_2556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2538_, 4);
v___x_2557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___y_2538_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = l_Array_append___redArg(v___x_2433_, v_val_2553_);
lean_dec(v_val_2553_);
v___x_2559_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2559_, 0, v___y_2538_);
lean_ctor_set(v___x_2559_, 1, v___x_2432_);
lean_ctor_set(v___x_2559_, 2, v___x_2558_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___y_2538_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node3(v___y_2538_, v___x_2555_, v___x_2557_, v___x_2559_, v___x_2561_);
v___x_2563_ = l_Array_mkArray1___redArg(v___x_2562_);
v___y_2516_ = v___y_2537_;
v___y_2517_ = v___y_2538_;
v___y_2518_ = v___y_2539_;
v___y_2519_ = v___y_2540_;
v___y_2520_ = v___y_2541_;
v___y_2521_ = v___y_2542_;
v___y_2522_ = v___x_2552_;
v___y_2523_ = v___y_2543_;
v___y_2524_ = v___y_2544_;
v___y_2525_ = v___y_2545_;
v___y_2526_ = v___y_2546_;
v___y_2527_ = v___y_2548_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___x_2563_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2564_; 
lean_dec(v___y_2547_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2564_ = lean_mk_empty_array_with_capacity(v___x_2341_);
lean_dec(v___x_2341_);
v___y_2516_ = v___y_2537_;
v___y_2517_ = v___y_2538_;
v___y_2518_ = v___y_2539_;
v___y_2519_ = v___y_2540_;
v___y_2520_ = v___y_2541_;
v___y_2521_ = v___y_2542_;
v___y_2522_ = v___x_2552_;
v___y_2523_ = v___y_2543_;
v___y_2524_ = v___y_2544_;
v___y_2525_ = v___y_2545_;
v___y_2526_ = v___y_2546_;
v___y_2527_ = v___y_2548_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___x_2564_;
goto v___jp_2515_;
}
}
v___jp_2565_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = l_Array_append___redArg(v___x_2433_, v___y_2579_);
lean_dec_ref(v___y_2579_);
lean_inc(v___y_2567_);
v___x_2581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2581_, 0, v___y_2567_);
lean_ctor_set(v___x_2581_, 1, v___x_2432_);
lean_ctor_set(v___x_2581_, 2, v___x_2580_);
if (lean_obj_tag(v___y_2570_) == 1)
{
lean_object* v_val_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_val_2582_ = lean_ctor_get(v___y_2570_, 0);
lean_inc(v_val_2582_);
lean_dec_ref_known(v___y_2570_, 1);
v___x_2583_ = l_Lean_SourceInfo_fromRef(v_val_2582_, v___x_2342_);
lean_dec(v_val_2582_);
v___x_2584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = l_Array_mkArray1___redArg(v___x_2585_);
v___y_2537_ = v___y_2566_;
v___y_2538_ = v___y_2567_;
v___y_2539_ = v___y_2568_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2571_;
v___y_2542_ = v___y_2572_;
v___y_2543_ = v___y_2573_;
v___y_2544_ = v___y_2574_;
v___y_2545_ = v___y_2575_;
v___y_2546_ = v___y_2576_;
v___y_2547_ = v___y_2577_;
v___y_2548_ = v___y_2578_;
v___y_2549_ = v___x_2581_;
v___y_2550_ = v___x_2586_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2587_; 
lean_dec(v___y_2570_);
v___x_2587_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2537_ = v___y_2566_;
v___y_2538_ = v___y_2567_;
v___y_2539_ = v___y_2568_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2571_;
v___y_2542_ = v___y_2572_;
v___y_2543_ = v___y_2573_;
v___y_2544_ = v___y_2574_;
v___y_2545_ = v___y_2575_;
v___y_2546_ = v___y_2576_;
v___y_2547_ = v___y_2577_;
v___y_2548_ = v___y_2578_;
v___y_2549_ = v___x_2581_;
v___y_2550_ = v___x_2587_;
goto v___jp_2536_;
}
}
v___jp_2588_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2600_ = l_Array_append___redArg(v___x_2433_, v___y_2599_);
lean_dec_ref(v___y_2599_);
lean_inc_n(v___y_2590_, 2);
v___x_2601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2601_, 0, v___y_2590_);
lean_ctor_set(v___x_2601_, 1, v___x_2432_);
lean_ctor_set(v___x_2601_, 2, v___x_2600_);
v___x_2602_ = l_Lean_Syntax_node5(v___y_2590_, v___x_2343_, v___y_2594_, v___y_2593_, v___y_2598_, v___y_2597_, v___x_2601_);
lean_inc(v___y_2592_);
v___x_2603_ = l_Lean_Syntax_node4(v___y_2590_, v___x_2344_, v___y_2596_, v___y_2592_, v___y_2592_, v___x_2602_);
v___y_2399_ = v___y_2595_;
v_stx_2400_ = v___x_2603_;
v___y_2401_ = v___y_2591_;
v___y_2402_ = v___y_2589_;
goto v___jp_2398_;
}
v___jp_2604_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = l_Array_append___redArg(v___x_2433_, v___y_2615_);
lean_dec_ref(v___y_2615_);
lean_inc(v___y_2606_);
v___x_2617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2617_, 0, v___y_2606_);
lean_ctor_set(v___x_2617_, 1, v___x_2432_);
lean_ctor_set(v___x_2617_, 2, v___x_2616_);
if (lean_obj_tag(v___y_2613_) == 1)
{
lean_object* v_val_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec(v___x_2341_);
v_val_2618_ = lean_ctor_get(v___y_2613_, 0);
lean_inc(v_val_2618_);
lean_dec_ref_known(v___y_2613_, 1);
v___x_2619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2606_);
v___x_2620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___y_2606_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = l_Array_mkArray2___redArg(v___x_2620_, v_val_2618_);
v___y_2589_ = v___y_2605_;
v___y_2590_ = v___y_2606_;
v___y_2591_ = v___y_2609_;
v___y_2592_ = v___y_2608_;
v___y_2593_ = v___y_2607_;
v___y_2594_ = v___y_2610_;
v___y_2595_ = v___y_2612_;
v___y_2596_ = v___y_2611_;
v___y_2597_ = v___x_2617_;
v___y_2598_ = v___y_2614_;
v___y_2599_ = v___x_2621_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2622_; 
lean_dec(v___y_2613_);
v___x_2622_ = lean_mk_empty_array_with_capacity(v___x_2341_);
lean_dec(v___x_2341_);
v___y_2589_ = v___y_2605_;
v___y_2590_ = v___y_2606_;
v___y_2591_ = v___y_2609_;
v___y_2592_ = v___y_2608_;
v___y_2593_ = v___y_2607_;
v___y_2594_ = v___y_2610_;
v___y_2595_ = v___y_2612_;
v___y_2596_ = v___y_2611_;
v___y_2597_ = v___x_2617_;
v___y_2598_ = v___y_2614_;
v___y_2599_ = v___x_2622_;
goto v___jp_2588_;
}
}
v___jp_2623_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = l_Array_append___redArg(v___x_2433_, v___y_2634_);
lean_dec_ref(v___y_2634_);
lean_inc(v___y_2625_);
v___x_2636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2636_, 0, v___y_2625_);
lean_ctor_set(v___x_2636_, 1, v___x_2432_);
lean_ctor_set(v___x_2636_, 2, v___x_2635_);
if (lean_obj_tag(v___y_2630_) == 1)
{
lean_object* v_val_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_val_2637_ = lean_ctor_get(v___y_2630_, 0);
lean_inc(v_val_2637_);
lean_dec_ref_known(v___y_2630_, 1);
v___x_2638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2639_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2638_);
v___x_2640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2625_, 4);
v___x_2641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___y_2625_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = l_Array_append___redArg(v___x_2433_, v_val_2637_);
lean_dec(v_val_2637_);
v___x_2643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2643_, 0, v___y_2625_);
lean_ctor_set(v___x_2643_, 1, v___x_2432_);
lean_ctor_set(v___x_2643_, 2, v___x_2642_);
v___x_2644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___y_2625_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = l_Lean_Syntax_node3(v___y_2625_, v___x_2639_, v___x_2641_, v___x_2643_, v___x_2645_);
v___x_2647_ = l_Array_mkArray1___redArg(v___x_2646_);
v___y_2605_ = v___y_2624_;
v___y_2606_ = v___y_2625_;
v___y_2607_ = v___y_2628_;
v___y_2608_ = v___y_2627_;
v___y_2609_ = v___y_2626_;
v___y_2610_ = v___y_2629_;
v___y_2611_ = v___y_2632_;
v___y_2612_ = v___y_2631_;
v___y_2613_ = v___y_2633_;
v___y_2614_ = v___x_2636_;
v___y_2615_ = v___x_2647_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2648_; 
lean_dec(v___y_2630_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2648_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2605_ = v___y_2624_;
v___y_2606_ = v___y_2625_;
v___y_2607_ = v___y_2628_;
v___y_2608_ = v___y_2627_;
v___y_2609_ = v___y_2626_;
v___y_2610_ = v___y_2629_;
v___y_2611_ = v___y_2632_;
v___y_2612_ = v___y_2631_;
v___y_2613_ = v___y_2633_;
v___y_2614_ = v___x_2636_;
v___y_2615_ = v___x_2648_;
goto v___jp_2604_;
}
}
v___jp_2649_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = l_Array_append___redArg(v___x_2433_, v___y_2660_);
lean_dec_ref(v___y_2660_);
lean_inc(v___y_2651_);
v___x_2662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2662_, 0, v___y_2651_);
lean_ctor_set(v___x_2662_, 1, v___x_2432_);
lean_ctor_set(v___x_2662_, 2, v___x_2661_);
if (lean_obj_tag(v___y_2655_) == 1)
{
lean_object* v_val_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_val_2663_ = lean_ctor_get(v___y_2655_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v___y_2655_, 1);
v___x_2664_ = l_Lean_SourceInfo_fromRef(v_val_2663_, v___x_2342_);
lean_dec(v_val_2663_);
v___x_2665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Array_mkArray1___redArg(v___x_2666_);
v___y_2624_ = v___y_2650_;
v___y_2625_ = v___y_2651_;
v___y_2626_ = v___y_2653_;
v___y_2627_ = v___y_2652_;
v___y_2628_ = v___x_2662_;
v___y_2629_ = v___y_2654_;
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2657_;
v___y_2632_ = v___y_2656_;
v___y_2633_ = v___y_2659_;
v___y_2634_ = v___x_2667_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2668_; 
lean_dec(v___y_2655_);
v___x_2668_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2624_ = v___y_2650_;
v___y_2625_ = v___y_2651_;
v___y_2626_ = v___y_2653_;
v___y_2627_ = v___y_2652_;
v___y_2628_ = v___x_2662_;
v___y_2629_ = v___y_2654_;
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2657_;
v___y_2632_ = v___y_2656_;
v___y_2633_ = v___y_2659_;
v___y_2634_ = v___x_2668_;
goto v___jp_2623_;
}
}
v___jp_2669_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2683_ = l_Array_append___redArg(v___x_2433_, v___y_2682_);
lean_dec_ref(v___y_2682_);
lean_inc_n(v___y_2672_, 3);
v___x_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2684_, 0, v___y_2672_);
lean_ctor_set(v___x_2684_, 1, v___x_2432_);
lean_ctor_set(v___x_2684_, 2, v___x_2683_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___y_2672_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_Syntax_node6(v___y_2672_, v___y_2679_, v___y_2678_, v___y_2681_, v___y_2670_, v___x_2684_, v___x_2686_, v___y_2674_);
lean_inc(v___y_2676_);
v___x_2688_ = l_Lean_Syntax_node4(v___y_2672_, v___y_2675_, v___y_2673_, v___y_2676_, v___y_2676_, v___x_2687_);
v___y_2399_ = v___y_2680_;
v_stx_2400_ = v___x_2688_;
v___y_2401_ = v___y_2677_;
v___y_2402_ = v___y_2671_;
goto v___jp_2398_;
}
v___jp_2689_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = l_Array_append___redArg(v___x_2433_, v___y_2702_);
lean_dec_ref(v___y_2702_);
lean_inc(v___y_2691_);
v___x_2704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2704_, 0, v___y_2691_);
lean_ctor_set(v___x_2704_, 1, v___x_2432_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
if (lean_obj_tag(v___y_2700_) == 1)
{
lean_object* v_val_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec(v___x_2341_);
v_val_2705_ = lean_ctor_get(v___y_2700_, 0);
lean_inc(v_val_2705_);
lean_dec_ref_known(v___y_2700_, 1);
v___x_2706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2707_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2706_);
v___x_2708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2691_, 4);
v___x_2709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___y_2691_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Array_append___redArg(v___x_2433_, v_val_2705_);
lean_dec(v_val_2705_);
v___x_2711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2711_, 0, v___y_2691_);
lean_ctor_set(v___x_2711_, 1, v___x_2432_);
lean_ctor_set(v___x_2711_, 2, v___x_2710_);
v___x_2712_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___y_2691_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_Syntax_node3(v___y_2691_, v___x_2707_, v___x_2709_, v___x_2711_, v___x_2713_);
v___x_2715_ = l_Array_mkArray1___redArg(v___x_2714_);
v___y_2670_ = v___x_2704_;
v___y_2671_ = v___y_2690_;
v___y_2672_ = v___y_2691_;
v___y_2673_ = v___y_2692_;
v___y_2674_ = v___y_2693_;
v___y_2675_ = v___y_2694_;
v___y_2676_ = v___y_2695_;
v___y_2677_ = v___y_2696_;
v___y_2678_ = v___y_2697_;
v___y_2679_ = v___y_2698_;
v___y_2680_ = v___y_2699_;
v___y_2681_ = v___y_2701_;
v___y_2682_ = v___x_2715_;
goto v___jp_2669_;
}
else
{
lean_object* v___x_2716_; 
lean_dec(v___y_2700_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2716_ = lean_mk_empty_array_with_capacity(v___x_2341_);
lean_dec(v___x_2341_);
v___y_2670_ = v___x_2704_;
v___y_2671_ = v___y_2690_;
v___y_2672_ = v___y_2691_;
v___y_2673_ = v___y_2692_;
v___y_2674_ = v___y_2693_;
v___y_2675_ = v___y_2694_;
v___y_2676_ = v___y_2695_;
v___y_2677_ = v___y_2696_;
v___y_2678_ = v___y_2697_;
v___y_2679_ = v___y_2698_;
v___y_2680_ = v___y_2699_;
v___y_2681_ = v___y_2701_;
v___y_2682_ = v___x_2716_;
goto v___jp_2669_;
}
}
v___jp_2717_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = l_Array_append___redArg(v___x_2433_, v___y_2730_);
lean_dec_ref(v___y_2730_);
lean_inc(v___y_2719_);
v___x_2732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2732_, 0, v___y_2719_);
lean_ctor_set(v___x_2732_, 1, v___x_2432_);
lean_ctor_set(v___x_2732_, 2, v___x_2731_);
if (lean_obj_tag(v___y_2722_) == 1)
{
lean_object* v_val_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_val_2733_ = lean_ctor_get(v___y_2722_, 0);
lean_inc(v_val_2733_);
lean_dec_ref_known(v___y_2722_, 1);
v___x_2734_ = l_Lean_SourceInfo_fromRef(v_val_2733_, v___x_2342_);
lean_dec(v_val_2733_);
v___x_2735_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Array_mkArray1___redArg(v___x_2736_);
v___y_2690_ = v___y_2718_;
v___y_2691_ = v___y_2719_;
v___y_2692_ = v___y_2720_;
v___y_2693_ = v___y_2721_;
v___y_2694_ = v___y_2723_;
v___y_2695_ = v___y_2724_;
v___y_2696_ = v___y_2725_;
v___y_2697_ = v___y_2726_;
v___y_2698_ = v___y_2727_;
v___y_2699_ = v___y_2728_;
v___y_2700_ = v___y_2729_;
v___y_2701_ = v___x_2732_;
v___y_2702_ = v___x_2737_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2738_; 
lean_dec(v___y_2722_);
v___x_2738_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2690_ = v___y_2718_;
v___y_2691_ = v___y_2719_;
v___y_2692_ = v___y_2720_;
v___y_2693_ = v___y_2721_;
v___y_2694_ = v___y_2723_;
v___y_2695_ = v___y_2724_;
v___y_2696_ = v___y_2725_;
v___y_2697_ = v___y_2726_;
v___y_2698_ = v___y_2727_;
v___y_2699_ = v___y_2728_;
v___y_2700_ = v___y_2729_;
v___y_2701_ = v___x_2732_;
v___y_2702_ = v___x_2738_;
goto v___jp_2689_;
}
}
v___jp_2739_:
{
if (v___y_2752_ == 0)
{
if (v_useReducible_2345_ == 0)
{
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
if (lean_obj_tag(v___y_2744_) == 0)
{
lean_dec(v___y_2754_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2743_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___y_2405_ = v___y_2751_;
v___y_2406_ = v___y_2753_;
v___y_2407_ = v___y_2742_;
v___y_2408_ = v___y_2746_;
v___y_2409_ = v___y_2741_;
v___y_2410_ = v___y_2750_;
v___y_2411_ = v___y_2745_;
v___y_2412_ = v___y_2747_;
v___y_2413_ = v___y_2740_;
goto v___jp_2404_;
}
else
{
lean_object* v_val_2755_; lean_object* v___x_2756_; 
v_val_2755_ = lean_ctor_get(v___y_2744_, 0);
lean_inc(v_val_2755_);
lean_dec_ref_known(v___y_2744_, 1);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2747_);
v___x_2756_ = lean_apply_9(v___f_2346_, v___y_2753_, v___y_2742_, v___y_2746_, v___y_2741_, v___y_2750_, v___y_2745_, v___y_2747_, v___y_2740_, lean_box(0));
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc_n(v_a_2757_, 3);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2340_, 2);
lean_inc_ref_n(v___x_2339_, 2);
lean_inc_ref_n(v___x_2338_, 2);
v___x_2759_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2760_, 0, v_a_2757_);
lean_ctor_set(v___x_2760_, 1, v___x_2347_);
v___x_2761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2761_, 0, v_a_2757_);
lean_ctor_set(v___x_2761_, 1, v___x_2432_);
lean_ctor_set(v___x_2761_, 2, v___x_2433_);
v___x_2762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2763_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2762_);
if (lean_obj_tag(v___y_2754_) == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2718_ = v___y_2740_;
v___y_2719_ = v_a_2757_;
v___y_2720_ = v___x_2760_;
v___y_2721_ = v_val_2755_;
v___y_2722_ = v___y_2743_;
v___y_2723_ = v___x_2759_;
v___y_2724_ = v___x_2761_;
v___y_2725_ = v___y_2747_;
v___y_2726_ = v___y_2748_;
v___y_2727_ = v___x_2763_;
v___y_2728_ = v___y_2751_;
v___y_2729_ = v___y_2749_;
v___y_2730_ = v___x_2764_;
goto v___jp_2717_;
}
else
{
lean_object* v_val_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_val_2765_ = lean_ctor_get(v___y_2754_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v___y_2754_, 1);
v___x_2766_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2767_ = lean_array_push(v___x_2766_, v_val_2765_);
v___y_2718_ = v___y_2740_;
v___y_2719_ = v_a_2757_;
v___y_2720_ = v___x_2760_;
v___y_2721_ = v_val_2755_;
v___y_2722_ = v___y_2743_;
v___y_2723_ = v___x_2759_;
v___y_2724_ = v___x_2761_;
v___y_2725_ = v___y_2747_;
v___y_2726_ = v___y_2748_;
v___y_2727_ = v___x_2763_;
v___y_2728_ = v___y_2751_;
v___y_2729_ = v___y_2749_;
v___y_2730_ = v___x_2767_;
goto v___jp_2717_;
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_val_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2743_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2347_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v_a_2768_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2756_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2756_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
else
{
lean_object* v___x_2776_; 
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2747_);
v___x_2776_ = lean_apply_9(v___f_2346_, v___y_2753_, v___y_2742_, v___y_2746_, v___y_2741_, v___y_2750_, v___y_2745_, v___y_2747_, v___y_2740_, lean_box(0));
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc_n(v_a_2777_, 3);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_a_2777_);
lean_ctor_set(v___x_2778_, 1, v___x_2347_);
v___x_2779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2779_, 0, v_a_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2432_);
lean_ctor_set(v___x_2779_, 2, v___x_2433_);
if (lean_obj_tag(v___y_2754_) == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2650_ = v___y_2740_;
v___y_2651_ = v_a_2777_;
v___y_2652_ = v___x_2779_;
v___y_2653_ = v___y_2747_;
v___y_2654_ = v___y_2748_;
v___y_2655_ = v___y_2743_;
v___y_2656_ = v___x_2778_;
v___y_2657_ = v___y_2751_;
v___y_2658_ = v___y_2749_;
v___y_2659_ = v___y_2744_;
v___y_2660_ = v___x_2780_;
goto v___jp_2649_;
}
else
{
lean_object* v_val_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_val_2781_ = lean_ctor_get(v___y_2754_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v___y_2754_, 1);
v___x_2782_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2783_ = lean_array_push(v___x_2782_, v_val_2781_);
v___y_2650_ = v___y_2740_;
v___y_2651_ = v_a_2777_;
v___y_2652_ = v___x_2779_;
v___y_2653_ = v___y_2747_;
v___y_2654_ = v___y_2748_;
v___y_2655_ = v___y_2743_;
v___y_2656_ = v___x_2778_;
v___y_2657_ = v___y_2751_;
v___y_2658_ = v___y_2749_;
v___y_2659_ = v___y_2744_;
v___y_2660_ = v___x_2783_;
goto v___jp_2649_;
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2347_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v_a_2784_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2776_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2776_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
else
{
lean_dec(v___x_2344_);
if (v_useReducible_2345_ == 0)
{
lean_dec(v___x_2343_);
if (lean_obj_tag(v___y_2744_) == 0)
{
lean_dec(v___y_2754_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2743_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___y_2405_ = v___y_2751_;
v___y_2406_ = v___y_2753_;
v___y_2407_ = v___y_2742_;
v___y_2408_ = v___y_2746_;
v___y_2409_ = v___y_2741_;
v___y_2410_ = v___y_2750_;
v___y_2411_ = v___y_2745_;
v___y_2412_ = v___y_2747_;
v___y_2413_ = v___y_2740_;
goto v___jp_2404_;
}
else
{
lean_object* v_val_2792_; lean_object* v___x_2793_; 
v_val_2792_ = lean_ctor_get(v___y_2744_, 0);
lean_inc(v_val_2792_);
lean_dec_ref_known(v___y_2744_, 1);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2747_);
v___x_2793_ = lean_apply_9(v___f_2346_, v___y_2753_, v___y_2742_, v___y_2746_, v___y_2741_, v___y_2750_, v___y_2745_, v___y_2747_, v___y_2740_, lean_box(0));
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc_n(v_a_2794_, 5);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2795_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2340_, 2);
lean_inc_ref_n(v___x_2339_, 2);
lean_inc_ref_n(v___x_2338_, 2);
v___x_2796_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_a_2794_);
lean_ctor_set(v___x_2797_, 1, v___x_2347_);
v___x_2798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2798_, 0, v_a_2794_);
lean_ctor_set(v___x_2798_, 1, v___x_2432_);
lean_ctor_set(v___x_2798_, 2, v___x_2433_);
v___x_2799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_2800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_a_2794_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Lean_Syntax_node1(v_a_2794_, v___x_2432_, v___x_2800_);
v___x_2802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2803_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2802_);
if (lean_obj_tag(v___y_2754_) == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2566_ = v___y_2740_;
v___y_2567_ = v_a_2794_;
v___y_2568_ = v___x_2797_;
v___y_2569_ = v___x_2798_;
v___y_2570_ = v___y_2743_;
v___y_2571_ = v_val_2792_;
v___y_2572_ = v___x_2796_;
v___y_2573_ = v___x_2801_;
v___y_2574_ = v___y_2747_;
v___y_2575_ = v___x_2803_;
v___y_2576_ = v___y_2748_;
v___y_2577_ = v___y_2749_;
v___y_2578_ = v___y_2751_;
v___y_2579_ = v___x_2804_;
goto v___jp_2565_;
}
else
{
lean_object* v_val_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_val_2805_ = lean_ctor_get(v___y_2754_, 0);
lean_inc(v_val_2805_);
lean_dec_ref_known(v___y_2754_, 1);
v___x_2806_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2807_ = lean_array_push(v___x_2806_, v_val_2805_);
v___y_2566_ = v___y_2740_;
v___y_2567_ = v_a_2794_;
v___y_2568_ = v___x_2797_;
v___y_2569_ = v___x_2798_;
v___y_2570_ = v___y_2743_;
v___y_2571_ = v_val_2792_;
v___y_2572_ = v___x_2796_;
v___y_2573_ = v___x_2801_;
v___y_2574_ = v___y_2747_;
v___y_2575_ = v___x_2803_;
v___y_2576_ = v___y_2748_;
v___y_2577_ = v___y_2749_;
v___y_2578_ = v___y_2751_;
v___y_2579_ = v___x_2807_;
goto v___jp_2565_;
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_val_2792_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2743_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2347_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v_a_2808_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2793_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2793_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
else
{
lean_object* v___x_2816_; 
lean_dec_ref(v___x_2347_);
lean_inc(v___y_2740_);
lean_inc_ref(v___y_2747_);
v___x_2816_ = lean_apply_9(v___f_2346_, v___y_2753_, v___y_2742_, v___y_2746_, v___y_2741_, v___y_2750_, v___y_2745_, v___y_2747_, v___y_2740_, lean_box(0));
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc_n(v_a_2817_, 2);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20));
lean_inc_ref(v___x_2340_);
lean_inc_ref(v___x_2339_);
lean_inc_ref(v___x_2338_);
v___x_2819_ = l_Lean_Name_mkStr4(v___x_2338_, v___x_2339_, v___x_2340_, v___x_2818_);
v___x_2820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21));
v___x_2821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2817_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
if (lean_obj_tag(v___y_2754_) == 0)
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_2496_ = v___y_2740_;
v___y_2497_ = v___x_2819_;
v___y_2498_ = v___y_2747_;
v___y_2499_ = v___x_2821_;
v___y_2500_ = v___y_2748_;
v___y_2501_ = v_a_2817_;
v___y_2502_ = v___y_2743_;
v___y_2503_ = v___y_2751_;
v___y_2504_ = v___y_2749_;
v___y_2505_ = v___y_2744_;
v___y_2506_ = v___x_2822_;
goto v___jp_2495_;
}
else
{
lean_object* v_val_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_val_2823_ = lean_ctor_get(v___y_2754_, 0);
lean_inc(v_val_2823_);
lean_dec_ref_known(v___y_2754_, 1);
v___x_2824_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2825_ = lean_array_push(v___x_2824_, v_val_2823_);
v___y_2496_ = v___y_2740_;
v___y_2497_ = v___x_2819_;
v___y_2498_ = v___y_2747_;
v___y_2499_ = v___x_2821_;
v___y_2500_ = v___y_2748_;
v___y_2501_ = v_a_2817_;
v___y_2502_ = v___y_2743_;
v___y_2503_ = v___y_2751_;
v___y_2504_ = v___y_2749_;
v___y_2505_ = v___y_2744_;
v___y_2506_ = v___x_2825_;
goto v___jp_2495_;
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2740_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v_a_2826_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2816_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2816_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
v___jp_2834_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2851_ = lean_unsigned_to_nat(5u);
v___x_2852_ = l_Lean_Syntax_getArg(v___y_2835_, v___x_2851_);
lean_dec(v___y_2835_);
v___x_2853_ = l_Lean_Syntax_matchesNull(v___x_2852_, v___x_2341_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v_args_2842_);
lean_dec(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2854_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2855_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2854_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___y_2399_ = v___y_2838_;
v_stx_2400_ = v_a_2856_;
v___y_2401_ = v___y_2849_;
v___y_2402_ = v___y_2850_;
goto v___jp_2398_;
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v___y_2838_);
lean_dec(v_tk_2337_);
v_a_2857_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2855_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2855_);
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
else
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Syntax_getOptional_x3f(v___y_2836_);
lean_dec(v___y_2836_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_box(0);
v___y_2740_ = v___y_2850_;
v___y_2741_ = v___y_2846_;
v___y_2742_ = v___y_2844_;
v___y_2743_ = v___y_2839_;
v___y_2744_ = v___y_2840_;
v___y_2745_ = v___y_2848_;
v___y_2746_ = v___y_2845_;
v___y_2747_ = v___y_2849_;
v___y_2748_ = v___y_2837_;
v___y_2749_ = v_args_2842_;
v___y_2750_ = v___y_2847_;
v___y_2751_ = v___y_2838_;
v___y_2752_ = v___y_2841_;
v___y_2753_ = v___y_2843_;
v___y_2754_ = v___x_2866_;
goto v___jp_2739_;
}
else
{
lean_object* v_val_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_val_2867_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2865_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_val_2867_);
lean_dec(v___x_2865_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_val_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
v___y_2740_ = v___y_2850_;
v___y_2741_ = v___y_2846_;
v___y_2742_ = v___y_2844_;
v___y_2743_ = v___y_2839_;
v___y_2744_ = v___y_2840_;
v___y_2745_ = v___y_2848_;
v___y_2746_ = v___y_2845_;
v___y_2747_ = v___y_2849_;
v___y_2748_ = v___y_2837_;
v___y_2749_ = v_args_2842_;
v___y_2750_ = v___y_2847_;
v___y_2751_ = v___y_2838_;
v___y_2752_ = v___y_2841_;
v___y_2753_ = v___y_2843_;
v___y_2754_ = v___x_2872_;
goto v___jp_2739_;
}
}
}
}
}
v___jp_2875_:
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = l_Lean_Syntax_getArg(v___y_2876_, v___x_2348_);
v___x_2892_ = l_Lean_Syntax_isNone(v___x_2891_);
if (v___x_2892_ == 0)
{
uint8_t v___x_2893_; 
lean_inc(v___x_2891_);
v___x_2893_ = l_Lean_Syntax_matchesNull(v___x_2891_, v___x_2349_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
lean_dec(v___x_2891_);
lean_dec(v_only_2882_);
lean_dec(v___y_2880_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2894_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2895_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2894_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v___y_2399_ = v___y_2879_;
v_stx_2400_ = v_a_2896_;
v___y_2401_ = v___y_2889_;
v___y_2402_ = v___y_2890_;
goto v___jp_2398_;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v___y_2879_);
lean_dec(v_tk_2337_);
v_a_2897_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2895_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2895_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2905_ = l_Lean_Syntax_getArg(v___x_2891_, v___x_2350_);
lean_dec(v___x_2350_);
lean_dec(v___x_2891_);
v___x_2906_ = l_Lean_Syntax_getArgs(v___x_2905_);
lean_dec(v___x_2905_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
v___y_2835_ = v___y_2876_;
v___y_2836_ = v___y_2877_;
v___y_2837_ = v___y_2878_;
v___y_2838_ = v___y_2879_;
v___y_2839_ = v_only_2882_;
v___y_2840_ = v___y_2880_;
v___y_2841_ = v___y_2881_;
v_args_2842_ = v___x_2907_;
v___y_2843_ = v___y_2883_;
v___y_2844_ = v___y_2884_;
v___y_2845_ = v___y_2885_;
v___y_2846_ = v___y_2886_;
v___y_2847_ = v___y_2887_;
v___y_2848_ = v___y_2888_;
v___y_2849_ = v___y_2889_;
v___y_2850_ = v___y_2890_;
goto v___jp_2834_;
}
}
else
{
lean_object* v___x_2908_; 
lean_dec(v___x_2891_);
lean_dec(v___x_2350_);
v___x_2908_ = lean_box(0);
v___y_2835_ = v___y_2876_;
v___y_2836_ = v___y_2877_;
v___y_2837_ = v___y_2878_;
v___y_2838_ = v___y_2879_;
v___y_2839_ = v_only_2882_;
v___y_2840_ = v___y_2880_;
v___y_2841_ = v___y_2881_;
v_args_2842_ = v___x_2908_;
v___y_2843_ = v___y_2883_;
v___y_2844_ = v___y_2884_;
v___y_2845_ = v___y_2885_;
v___y_2846_ = v___y_2886_;
v___y_2847_ = v___y_2887_;
v___y_2848_ = v___y_2888_;
v___y_2849_ = v___y_2889_;
v___y_2850_ = v___y_2890_;
goto v___jp_2834_;
}
}
v___jp_2909_:
{
lean_object* v_usedTheorems_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v_usedTheorems_2914_ = lean_ctor_get(v___y_2911_, 0);
v___x_2915_ = l_Lean_Syntax_unsetTrailing(v___y_2910_);
v___x_2916_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2915_, v_usedTheorems_2914_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; uint8_t v___x_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc_n(v_a_2917_, 2);
lean_dec_ref_known(v___x_2916_, 1);
v___x_2918_ = l_Lean_Syntax_isOfKind(v_a_2917_, v___x_2430_);
lean_dec(v___x_2430_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_inc(v_ref_2426_);
lean_dec(v_a_2917_);
lean_dec(v___y_2913_);
lean_dec(v___x_2352_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2919_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2920_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2919_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___y_2376_ = v___y_2911_;
v_stx_2377_ = v_a_2921_;
v___y_2378_ = v___y_2368_;
v_ref_2379_ = v_ref_2426_;
v___y_2380_ = v___y_2369_;
goto v___jp_2375_;
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v___y_2911_);
lean_dec(v_ref_2426_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v_tk_2337_);
v_a_2922_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2920_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2920_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = l_Lean_Syntax_getArg(v_a_2917_, v___x_2350_);
lean_inc(v___x_2930_);
v___x_2931_ = l_Lean_Syntax_isOfKind(v___x_2930_, v___x_2351_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_inc(v_ref_2426_);
lean_dec(v___x_2930_);
lean_dec(v_a_2917_);
lean_dec(v___y_2913_);
lean_dec(v___x_2352_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2932_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2933_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2932_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
v___y_2376_ = v___y_2911_;
v_stx_2377_ = v_a_2934_;
v___y_2378_ = v___y_2368_;
v_ref_2379_ = v_ref_2426_;
v___y_2380_ = v___y_2369_;
goto v___jp_2375_;
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec_ref(v___y_2911_);
lean_dec(v_ref_2426_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v_tk_2337_);
v_a_2935_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2933_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2933_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2943_ = l_Lean_Syntax_getArg(v_a_2917_, v___x_2352_);
lean_dec(v___x_2352_);
v___x_2944_ = l_Lean_Syntax_getArg(v_a_2917_, v___x_2349_);
v___x_2945_ = l_Lean_Syntax_isNone(v___x_2944_);
if (v___x_2945_ == 0)
{
uint8_t v___x_2946_; 
lean_inc(v___x_2944_);
v___x_2946_ = l_Lean_Syntax_matchesNull(v___x_2944_, v___x_2350_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_inc(v_ref_2426_);
lean_dec(v___x_2944_);
lean_dec(v___x_2943_);
lean_dec(v___x_2930_);
lean_dec(v_a_2917_);
lean_dec(v___y_2913_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
v___x_2947_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2948_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2947_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___y_2376_ = v___y_2911_;
v_stx_2377_ = v_a_2949_;
v___y_2378_ = v___y_2368_;
v_ref_2379_ = v_ref_2426_;
v___y_2380_ = v___y_2369_;
goto v___jp_2375_;
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref(v___y_2911_);
lean_dec(v_ref_2426_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v_tk_2337_);
v_a_2950_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2948_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2948_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = l_Lean_Syntax_getArg(v___x_2944_, v___x_2341_);
lean_dec(v___x_2944_);
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
v___y_2876_ = v_a_2917_;
v___y_2877_ = v___x_2943_;
v___y_2878_ = v___x_2930_;
v___y_2879_ = v___y_2911_;
v___y_2880_ = v___y_2913_;
v___y_2881_ = v___y_2912_;
v_only_2882_ = v___x_2959_;
v___y_2883_ = v___y_2362_;
v___y_2884_ = v___y_2363_;
v___y_2885_ = v___y_2364_;
v___y_2886_ = v___y_2365_;
v___y_2887_ = v___y_2366_;
v___y_2888_ = v___y_2367_;
v___y_2889_ = v___y_2368_;
v___y_2890_ = v___y_2369_;
goto v___jp_2875_;
}
}
else
{
lean_object* v___x_2960_; 
lean_dec(v___x_2944_);
v___x_2960_ = lean_box(0);
v___y_2876_ = v_a_2917_;
v___y_2877_ = v___x_2943_;
v___y_2878_ = v___x_2930_;
v___y_2879_ = v___y_2911_;
v___y_2880_ = v___y_2913_;
v___y_2881_ = v___y_2912_;
v_only_2882_ = v___x_2960_;
v___y_2883_ = v___y_2362_;
v___y_2884_ = v___y_2363_;
v___y_2885_ = v___y_2364_;
v___y_2886_ = v___y_2365_;
v___y_2887_ = v___y_2366_;
v___y_2888_ = v___y_2367_;
v___y_2889_ = v___y_2368_;
v___y_2890_ = v___y_2369_;
goto v___jp_2875_;
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2911_);
lean_dec(v___x_2430_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___x_2352_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v_a_2961_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2916_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2916_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
v___jp_2969_:
{
if (lean_obj_tag(v_usingArg_2353_) == 0)
{
v___y_2910_ = v___y_2970_;
v___y_2911_ = v___y_2971_;
v___y_2912_ = v___y_2972_;
v___y_2913_ = v_usingArg_2353_;
goto v___jp_2909_;
}
else
{
lean_object* v_val_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2981_; 
v_val_2973_ = lean_ctor_get(v_usingArg_2353_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_usingArg_2353_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2975_ = v_usingArg_2353_;
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_val_2973_);
lean_dec(v_usingArg_2353_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = l_Lean_Syntax_unsetTrailing(v_val_2973_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2977_);
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
v___y_2910_ = v___y_2970_;
v___y_2911_ = v___y_2971_;
v___y_2912_ = v___y_2972_;
v___y_2913_ = v___x_2979_;
goto v___jp_2909_;
}
}
}
}
v___jp_2982_:
{
if (v___y_2986_ == 0)
{
lean_dec(v___y_2983_);
lean_dec(v___x_2430_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_usingArg_2353_);
lean_dec(v___x_2352_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v___y_2372_ = v___y_2984_;
goto v___jp_2371_;
}
else
{
v___y_2970_ = v___y_2983_;
v___y_2971_ = v___y_2984_;
v___y_2972_ = v___y_2985_;
goto v___jp_2969_;
}
}
v___jp_2987_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___f_2998_; lean_object* v___x_2999_; 
v___x_2993_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_2992_, v___x_2427_);
v___x_2994_ = lean_box(v___x_2342_);
v___x_2995_ = lean_box(v___x_2427_);
v___x_2996_ = lean_box(v_useReducible_2345_);
v___x_2997_ = lean_box(v___x_2355_);
lean_inc(v___x_2350_);
lean_inc_ref(v___x_2347_);
lean_inc(v_usingArg_2353_);
lean_inc(v___x_2341_);
lean_inc(v_tk_2337_);
lean_inc(v___x_2352_);
v___f_2998_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 24, 14);
lean_closure_set(v___f_2998_, 0, v___x_2352_);
lean_closure_set(v___f_2998_, 1, v_tk_2337_);
lean_closure_set(v___f_2998_, 2, v___x_2432_);
lean_closure_set(v___f_2998_, 3, v___x_2341_);
lean_closure_set(v___f_2998_, 4, v___x_2993_);
lean_closure_set(v___f_2998_, 5, v___y_2988_);
lean_closure_set(v___f_2998_, 6, v___x_2994_);
lean_closure_set(v___f_2998_, 7, v_usingArg_2353_);
lean_closure_set(v___f_2998_, 8, v___x_2995_);
lean_closure_set(v___f_2998_, 9, v___x_2347_);
lean_closure_set(v___f_2998_, 10, v___x_2996_);
lean_closure_set(v___f_2998_, 11, v___x_2997_);
lean_closure_set(v___f_2998_, 12, v___x_2350_);
lean_closure_set(v___f_2998_, 13, v_usingTk_x3f_2356_);
v___x_2999_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_2991_, v___f_2998_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2991_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3002_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_2425_, v___x_3001_);
if (v___x_3002_ == 0)
{
if (lean_obj_tag(v_squeeze_2357_) == 0)
{
v___y_2983_ = v___y_2989_;
v___y_2984_ = v_a_3000_;
v___y_2985_ = v___y_2990_;
v___y_2986_ = v___x_3002_;
goto v___jp_2982_;
}
else
{
v___y_2983_ = v___y_2989_;
v___y_2984_ = v_a_3000_;
v___y_2985_ = v___y_2990_;
v___y_2986_ = v___x_2355_;
goto v___jp_2982_;
}
}
else
{
v___y_2970_ = v___y_2989_;
v___y_2971_ = v_a_3000_;
v___y_2972_ = v___y_2990_;
goto v___jp_2969_;
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v___y_2989_);
lean_dec(v___x_2430_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_usingArg_2353_);
lean_dec(v___x_2352_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v_a_3003_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2999_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2999_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
v___jp_3011_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3015_ = l_Array_append___redArg(v___x_2433_, v___y_3014_);
lean_dec_ref(v___y_3014_);
lean_inc_n(v___x_2428_, 2);
v___x_3016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3016_, 0, v___x_2428_);
lean_ctor_set(v___x_3016_, 1, v___x_2432_);
lean_ctor_set(v___x_3016_, 2, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3017_, 0, v___x_2428_);
lean_ctor_set(v___x_3017_, 1, v___x_2432_);
lean_ctor_set(v___x_3017_, 2, v___x_2433_);
lean_inc(v___x_2430_);
v___x_3018_ = l_Lean_Syntax_node6(v___x_2428_, v___x_2430_, v___x_2431_, v___x_2354_, v___y_3013_, v___y_3012_, v___x_3016_, v___x_3017_);
v___x_3019_ = 0;
v___x_3020_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23));
v___x_3021_ = lean_box(v___x_2427_);
v___x_3022_ = lean_box(v___x_3019_);
v___x_3023_ = lean_box(v___x_2427_);
lean_inc(v___x_3018_);
v___x_3024_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3024_, 0, v___x_3018_);
lean_closure_set(v___x_3024_, 1, v___x_3021_);
lean_closure_set(v___x_3024_, 2, v___x_3022_);
lean_closure_set(v___x_3024_, 3, v___x_3023_);
lean_closure_set(v___x_3024_, 4, v___x_3020_);
v___x_3025_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3024_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
if (lean_obj_tag(v_unfold_2358_) == 0)
{
lean_object* v_ctx_3027_; lean_object* v_simprocs_3028_; lean_object* v_dischargeWrapper_3029_; 
v_ctx_3027_ = lean_ctor_get(v_a_3026_, 0);
lean_inc_ref(v_ctx_3027_);
v_simprocs_3028_ = lean_ctor_get(v_a_3026_, 1);
lean_inc_ref(v_simprocs_3028_);
v_dischargeWrapper_3029_ = lean_ctor_get(v_a_3026_, 2);
lean_inc(v_dischargeWrapper_3029_);
lean_dec(v_a_3026_);
v___y_2988_ = v_simprocs_3028_;
v___y_2989_ = v___x_3018_;
v___y_2990_ = v___x_2427_;
v___y_2991_ = v_dischargeWrapper_3029_;
v___y_2992_ = v_ctx_3027_;
goto v___jp_2987_;
}
else
{
if (v___x_2355_ == 0)
{
lean_object* v_ctx_3030_; lean_object* v_simprocs_3031_; lean_object* v_dischargeWrapper_3032_; 
v_ctx_3030_ = lean_ctor_get(v_a_3026_, 0);
lean_inc_ref(v_ctx_3030_);
v_simprocs_3031_ = lean_ctor_get(v_a_3026_, 1);
lean_inc_ref(v_simprocs_3031_);
v_dischargeWrapper_3032_ = lean_ctor_get(v_a_3026_, 2);
lean_inc(v_dischargeWrapper_3032_);
lean_dec(v_a_3026_);
v___y_2988_ = v_simprocs_3031_;
v___y_2989_ = v___x_3018_;
v___y_2990_ = v___x_2355_;
v___y_2991_ = v_dischargeWrapper_3032_;
v___y_2992_ = v_ctx_3030_;
goto v___jp_2987_;
}
else
{
lean_object* v_ctx_3033_; lean_object* v_simprocs_3034_; lean_object* v_dischargeWrapper_3035_; lean_object* v___x_3036_; 
v_ctx_3033_ = lean_ctor_get(v_a_3026_, 0);
lean_inc_ref(v_ctx_3033_);
v_simprocs_3034_ = lean_ctor_get(v_a_3026_, 1);
lean_inc_ref(v_simprocs_3034_);
v_dischargeWrapper_3035_ = lean_ctor_get(v_a_3026_, 2);
lean_inc(v_dischargeWrapper_3035_);
lean_dec(v_a_3026_);
v___x_3036_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3033_);
v___y_2988_ = v_simprocs_3034_;
v___y_2989_ = v___x_3018_;
v___y_2990_ = v___x_2355_;
v___y_2991_ = v_dischargeWrapper_3035_;
v___y_2992_ = v___x_3036_;
goto v___jp_2987_;
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v___x_3018_);
lean_dec(v___x_2430_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_usingTk_x3f_2356_);
lean_dec(v_usingArg_2353_);
lean_dec(v___x_2352_);
lean_dec(v___x_2350_);
lean_dec_ref(v___x_2347_);
lean_dec_ref(v___f_2346_);
lean_dec(v___x_2344_);
lean_dec(v___x_2343_);
lean_dec(v___x_2341_);
lean_dec_ref(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec(v_tk_2337_);
v_a_3037_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3025_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3025_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
v___jp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = l_Array_append___redArg(v___x_2433_, v___y_3047_);
lean_dec_ref(v___y_3047_);
lean_inc(v___x_2428_);
v___x_3049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3049_, 0, v___x_2428_);
lean_ctor_set(v___x_3049_, 1, v___x_2432_);
lean_ctor_set(v___x_3049_, 2, v___x_3048_);
if (lean_obj_tag(v_args_2359_) == 1)
{
lean_object* v_val_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v_val_3050_ = lean_ctor_get(v_args_2359_, 0);
v___x_3051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___x_2428_, 3);
v___x_3052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_2428_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = l_Array_append___redArg(v___x_2433_, v_val_3050_);
v___x_3054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3054_, 0, v___x_2428_);
lean_ctor_set(v___x_3054_, 1, v___x_2432_);
lean_ctor_set(v___x_3054_, 2, v___x_3053_);
v___x_3055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_2428_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = l_Array_mkArray3___redArg(v___x_3052_, v___x_3054_, v___x_3056_);
v___y_3012_ = v___x_3049_;
v___y_3013_ = v___y_3046_;
v___y_3014_ = v___x_3057_;
goto v___jp_3011_;
}
else
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_3012_ = v___x_3049_;
v___y_3013_ = v___y_3046_;
v___y_3014_ = v___x_3058_;
goto v___jp_3011_;
}
}
v___jp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = l_Array_append___redArg(v___x_2433_, v___y_3060_);
lean_dec_ref(v___y_3060_);
lean_inc(v___x_2428_);
v___x_3062_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3062_, 0, v___x_2428_);
lean_ctor_set(v___x_3062_, 1, v___x_2432_);
lean_ctor_set(v___x_3062_, 2, v___x_3061_);
if (lean_obj_tag(v_only_2360_) == 1)
{
lean_object* v_val_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_val_3063_ = lean_ctor_get(v_only_2360_, 0);
v___x_3064_ = l_Lean_SourceInfo_fromRef(v_val_3063_, v___x_2342_);
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Array_mkArray1___redArg(v___x_3066_);
v___y_3046_ = v___x_3062_;
v___y_3047_ = v___x_3067_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___y_3046_ = v___x_3062_;
v___y_3047_ = v___x_3068_;
goto v___jp_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v_tk_3073_ = _args[0];
lean_object* v___x_3074_ = _args[1];
lean_object* v___x_3075_ = _args[2];
lean_object* v___x_3076_ = _args[3];
lean_object* v___x_3077_ = _args[4];
lean_object* v___x_3078_ = _args[5];
lean_object* v___x_3079_ = _args[6];
lean_object* v___x_3080_ = _args[7];
lean_object* v_useReducible_3081_ = _args[8];
lean_object* v___f_3082_ = _args[9];
lean_object* v___x_3083_ = _args[10];
lean_object* v___x_3084_ = _args[11];
lean_object* v___x_3085_ = _args[12];
lean_object* v___x_3086_ = _args[13];
lean_object* v___x_3087_ = _args[14];
lean_object* v___x_3088_ = _args[15];
lean_object* v_usingArg_3089_ = _args[16];
lean_object* v___x_3090_ = _args[17];
lean_object* v___x_3091_ = _args[18];
lean_object* v_usingTk_x3f_3092_ = _args[19];
lean_object* v_squeeze_3093_ = _args[20];
lean_object* v_unfold_3094_ = _args[21];
lean_object* v_args_3095_ = _args[22];
lean_object* v_only_3096_ = _args[23];
lean_object* v___y_3097_ = _args[24];
lean_object* v___y_3098_ = _args[25];
lean_object* v___y_3099_ = _args[26];
lean_object* v___y_3100_ = _args[27];
lean_object* v___y_3101_ = _args[28];
lean_object* v___y_3102_ = _args[29];
lean_object* v___y_3103_ = _args[30];
lean_object* v___y_3104_ = _args[31];
lean_object* v___y_3105_ = _args[32];
lean_object* v___y_3106_ = _args[33];
_start:
{
uint8_t v___x_95955__boxed_3107_; uint8_t v_useReducible_boxed_3108_; uint8_t v___x_95966__boxed_3109_; lean_object* v_res_3110_; 
v___x_95955__boxed_3107_ = lean_unbox(v___x_3078_);
v_useReducible_boxed_3108_ = lean_unbox(v_useReducible_3081_);
v___x_95966__boxed_3109_ = lean_unbox(v___x_3091_);
v_res_3110_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3073_, v___x_3074_, v___x_3075_, v___x_3076_, v___x_3077_, v___x_95955__boxed_3107_, v___x_3079_, v___x_3080_, v_useReducible_boxed_3108_, v___f_3082_, v___x_3083_, v___x_3084_, v___x_3085_, v___x_3086_, v___x_3087_, v___x_3088_, v_usingArg_3089_, v___x_3090_, v___x_95966__boxed_3109_, v_usingTk_x3f_3092_, v_squeeze_3093_, v_unfold_3094_, v_args_3095_, v_only_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v_only_3096_);
lean_dec(v_args_3095_);
lean_dec(v_unfold_3094_);
lean_dec(v_squeeze_3093_);
lean_dec(v___x_3087_);
lean_dec(v___x_3085_);
lean_dec(v___x_3084_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3136_, lean_object* v_stx_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_3148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3149_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_3150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3137_);
v___x_3152_ = l_Lean_Syntax_isOfKind(v_stx_3137_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_dec(v_stx_3137_);
v___x_3153_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3153_;
}
else
{
lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v_tk_3156_; lean_object* v___x_3157_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; uint8_t v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; uint8_t v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v_usingTk_x3f_3208_; lean_object* v_usingArg_3209_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_args_3241_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v_only_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v_unfold_3297_; lean_object* v_squeeze_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___f_3154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3155_ = lean_unsigned_to_nat(0u);
v_tk_3156_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3155_);
v___x_3157_ = lean_unsigned_to_nat(1u);
v___x_3333_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3157_);
v___x_3334_ = l_Lean_Syntax_isNone(v___x_3333_);
if (v___x_3334_ == 0)
{
uint8_t v___x_3335_; 
lean_inc(v___x_3333_);
v___x_3335_ = l_Lean_Syntax_matchesNull(v___x_3333_, v___x_3157_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec(v___x_3333_);
lean_dec(v_tk_3156_);
lean_dec(v_stx_3137_);
v___x_3336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3336_;
}
else
{
lean_object* v_squeeze_3337_; lean_object* v___x_3338_; 
v_squeeze_3337_ = l_Lean_Syntax_getArg(v___x_3333_, v___x_3155_);
lean_dec(v___x_3333_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_squeeze_3337_);
v_squeeze_3316_ = v___x_3338_;
v___y_3317_ = v_a_3138_;
v___y_3318_ = v_a_3139_;
v___y_3319_ = v_a_3140_;
v___y_3320_ = v_a_3141_;
v___y_3321_ = v_a_3142_;
v___y_3322_ = v_a_3143_;
v___y_3323_ = v_a_3144_;
v___y_3324_ = v_a_3145_;
goto v___jp_3315_;
}
}
else
{
lean_object* v___x_3339_; 
lean_dec(v___x_3333_);
v___x_3339_ = lean_box(0);
v_squeeze_3316_ = v___x_3339_;
v___y_3317_ = v_a_3138_;
v___y_3318_ = v_a_3139_;
v___y_3319_ = v_a_3140_;
v___y_3320_ = v_a_3141_;
v___y_3321_ = v_a_3142_;
v___y_3322_ = v_a_3143_;
v___y_3323_ = v_a_3144_;
v___y_3324_ = v_a_3145_;
goto v___jp_3315_;
}
v___jp_3158_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3181_ = lean_box(v___x_3152_);
v___x_3182_ = lean_box(v_useReducible_3136_);
v___x_3183_ = lean_box(v___y_3164_);
lean_inc(v___y_3166_);
lean_inc(v___y_3161_);
v___f_3184_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3184_, 0, v_tk_3156_);
lean_closure_set(v___f_3184_, 1, v___x_3147_);
lean_closure_set(v___f_3184_, 2, v___x_3148_);
lean_closure_set(v___f_3184_, 3, v___x_3149_);
lean_closure_set(v___f_3184_, 4, v___x_3155_);
lean_closure_set(v___f_3184_, 5, v___x_3181_);
lean_closure_set(v___f_3184_, 6, v___y_3161_);
lean_closure_set(v___f_3184_, 7, v___x_3151_);
lean_closure_set(v___f_3184_, 8, v___x_3182_);
lean_closure_set(v___f_3184_, 9, v___f_3154_);
lean_closure_set(v___f_3184_, 10, v___x_3150_);
lean_closure_set(v___f_3184_, 11, v___y_3169_);
lean_closure_set(v___f_3184_, 12, v___y_3167_);
lean_closure_set(v___f_3184_, 13, v___x_3157_);
lean_closure_set(v___f_3184_, 14, v___y_3166_);
lean_closure_set(v___f_3184_, 15, v___y_3178_);
lean_closure_set(v___f_3184_, 16, v___y_3179_);
lean_closure_set(v___f_3184_, 17, v___y_3162_);
lean_closure_set(v___f_3184_, 18, v___x_3183_);
lean_closure_set(v___f_3184_, 19, v___y_3177_);
lean_closure_set(v___f_3184_, 20, v___y_3168_);
lean_closure_set(v___f_3184_, 21, v___y_3173_);
lean_closure_set(v___f_3184_, 22, v___y_3163_);
lean_closure_set(v___f_3184_, 23, v___y_3159_);
lean_closure_set(v___f_3184_, 24, v___y_3180_);
v___x_3185_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3185_, 0, v___f_3184_);
v___x_3186_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3185_, v___y_3174_, v___y_3160_, v___y_3176_, v___y_3175_, v___y_3172_, v___y_3165_, v___y_3170_, v___y_3171_);
return v___x_3186_;
}
v___jp_3187_:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Syntax_getOptional_x3f(v___y_3207_);
lean_dec(v___y_3207_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_box(0);
v___y_3159_ = v___y_3188_;
v___y_3160_ = v___y_3189_;
v___y_3161_ = v___y_3190_;
v___y_3162_ = v___y_3191_;
v___y_3163_ = v___y_3192_;
v___y_3164_ = v___y_3193_;
v___y_3165_ = v___y_3194_;
v___y_3166_ = v___y_3195_;
v___y_3167_ = v___y_3196_;
v___y_3168_ = v___y_3197_;
v___y_3169_ = v___y_3198_;
v___y_3170_ = v___y_3199_;
v___y_3171_ = v___y_3200_;
v___y_3172_ = v___y_3201_;
v___y_3173_ = v___y_3202_;
v___y_3174_ = v___y_3203_;
v___y_3175_ = v___y_3205_;
v___y_3176_ = v___y_3204_;
v___y_3177_ = v_usingTk_x3f_3208_;
v___y_3178_ = v___y_3206_;
v___y_3179_ = v_usingArg_3209_;
v___y_3180_ = v___x_3211_;
goto v___jp_3158_;
}
else
{
lean_object* v_val_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
v_val_3212_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3210_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_val_3212_);
lean_dec(v___x_3210_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_val_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
v___y_3159_ = v___y_3188_;
v___y_3160_ = v___y_3189_;
v___y_3161_ = v___y_3190_;
v___y_3162_ = v___y_3191_;
v___y_3163_ = v___y_3192_;
v___y_3164_ = v___y_3193_;
v___y_3165_ = v___y_3194_;
v___y_3166_ = v___y_3195_;
v___y_3167_ = v___y_3196_;
v___y_3168_ = v___y_3197_;
v___y_3169_ = v___y_3198_;
v___y_3170_ = v___y_3199_;
v___y_3171_ = v___y_3200_;
v___y_3172_ = v___y_3201_;
v___y_3173_ = v___y_3202_;
v___y_3174_ = v___y_3203_;
v___y_3175_ = v___y_3205_;
v___y_3176_ = v___y_3204_;
v___y_3177_ = v_usingTk_x3f_3208_;
v___y_3178_ = v___y_3206_;
v___y_3179_ = v_usingArg_3209_;
v___y_3180_ = v___x_3217_;
goto v___jp_3158_;
}
}
}
}
v___jp_3220_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3242_ = lean_unsigned_to_nat(4u);
v___x_3243_ = l_Lean_Syntax_getArg(v___y_3233_, v___x_3242_);
lean_dec(v___y_3233_);
v___x_3244_ = l_Lean_Syntax_isNone(v___x_3243_);
if (v___x_3244_ == 0)
{
uint8_t v___x_3245_; 
lean_inc(v___x_3243_);
v___x_3245_ = l_Lean_Syntax_matchesNull(v___x_3243_, v___y_3235_);
lean_dec(v___y_3235_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_dec(v___x_3243_);
lean_dec(v_args_3241_);
lean_dec(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec(v___y_3234_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3224_);
lean_dec(v___y_3221_);
lean_dec(v_tk_3156_);
v___x_3246_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3246_;
}
else
{
lean_object* v_usingTk_x3f_3247_; lean_object* v_usingArg_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_usingTk_x3f_3247_ = l_Lean_Syntax_getArg(v___x_3243_, v___x_3155_);
v_usingArg_3248_ = l_Lean_Syntax_getArg(v___x_3243_, v___x_3157_);
lean_dec(v___x_3243_);
v___x_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3249_, 0, v_usingTk_x3f_3247_);
v___x_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_usingArg_3248_);
v___y_3188_ = v___y_3221_;
v___y_3189_ = v___y_3222_;
v___y_3190_ = v___y_3223_;
v___y_3191_ = v___y_3224_;
v___y_3192_ = v_args_3241_;
v___y_3193_ = v___y_3225_;
v___y_3194_ = v___y_3226_;
v___y_3195_ = v___y_3227_;
v___y_3196_ = v___y_3228_;
v___y_3197_ = v___y_3229_;
v___y_3198_ = v___x_3242_;
v___y_3199_ = v___y_3230_;
v___y_3200_ = v___y_3231_;
v___y_3201_ = v___y_3232_;
v___y_3202_ = v___y_3234_;
v___y_3203_ = v___y_3236_;
v___y_3204_ = v___y_3238_;
v___y_3205_ = v___y_3237_;
v___y_3206_ = v___y_3239_;
v___y_3207_ = v___y_3240_;
v_usingTk_x3f_3208_ = v___x_3249_;
v_usingArg_3209_ = v___x_3250_;
goto v___jp_3187_;
}
}
else
{
lean_object* v___x_3251_; 
lean_dec(v___x_3243_);
lean_dec(v___y_3235_);
v___x_3251_ = lean_box(0);
v___y_3188_ = v___y_3221_;
v___y_3189_ = v___y_3222_;
v___y_3190_ = v___y_3223_;
v___y_3191_ = v___y_3224_;
v___y_3192_ = v_args_3241_;
v___y_3193_ = v___y_3225_;
v___y_3194_ = v___y_3226_;
v___y_3195_ = v___y_3227_;
v___y_3196_ = v___y_3228_;
v___y_3197_ = v___y_3229_;
v___y_3198_ = v___x_3242_;
v___y_3199_ = v___y_3230_;
v___y_3200_ = v___y_3231_;
v___y_3201_ = v___y_3232_;
v___y_3202_ = v___y_3234_;
v___y_3203_ = v___y_3236_;
v___y_3204_ = v___y_3238_;
v___y_3205_ = v___y_3237_;
v___y_3206_ = v___y_3239_;
v___y_3207_ = v___y_3240_;
v_usingTk_x3f_3208_ = v___x_3251_;
v_usingArg_3209_ = v___x_3251_;
goto v___jp_3187_;
}
}
v___jp_3252_:
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = l_Lean_Syntax_getArg(v___y_3264_, v___y_3261_);
lean_dec(v___y_3261_);
v___x_3275_ = l_Lean_Syntax_isNone(v___x_3274_);
if (v___x_3275_ == 0)
{
uint8_t v___x_3276_; 
lean_inc(v___x_3274_);
v___x_3276_ = l_Lean_Syntax_matchesNull(v___x_3274_, v___x_3157_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; 
lean_dec(v___x_3274_);
lean_dec(v_only_3265_);
lean_dec(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec(v_tk_3156_);
v___x_3277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
v___x_3278_ = l_Lean_Syntax_getArg(v___x_3274_, v___x_3155_);
lean_dec(v___x_3274_);
v___x_3279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3278_);
v___x_3280_ = l_Lean_Syntax_isOfKind(v___x_3278_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_dec(v___x_3278_);
lean_dec(v_only_3265_);
lean_dec(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec(v_tk_3156_);
v___x_3281_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3281_;
}
else
{
lean_object* v___x_3282_; lean_object* v_args_3283_; lean_object* v___x_3284_; 
v___x_3282_ = l_Lean_Syntax_getArg(v___x_3278_, v___x_3157_);
lean_dec(v___x_3278_);
v_args_3283_ = l_Lean_Syntax_getArgs(v___x_3282_);
lean_dec(v___x_3282_);
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v_args_3283_);
v___y_3221_ = v_only_3265_;
v___y_3222_ = v___y_3267_;
v___y_3223_ = v___y_3253_;
v___y_3224_ = v___y_3254_;
v___y_3225_ = v___y_3256_;
v___y_3226_ = v___y_3271_;
v___y_3227_ = v___y_3257_;
v___y_3228_ = v___y_3259_;
v___y_3229_ = v___y_3258_;
v___y_3230_ = v___y_3272_;
v___y_3231_ = v___y_3273_;
v___y_3232_ = v___y_3270_;
v___y_3233_ = v___y_3264_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___y_3262_;
v___y_3236_ = v___y_3266_;
v___y_3237_ = v___y_3269_;
v___y_3238_ = v___y_3268_;
v___y_3239_ = v___y_3260_;
v___y_3240_ = v___y_3263_;
v_args_3241_ = v___x_3284_;
goto v___jp_3220_;
}
}
}
else
{
lean_object* v___x_3285_; 
lean_dec(v___x_3274_);
v___x_3285_ = lean_box(0);
v___y_3221_ = v_only_3265_;
v___y_3222_ = v___y_3267_;
v___y_3223_ = v___y_3253_;
v___y_3224_ = v___y_3254_;
v___y_3225_ = v___y_3256_;
v___y_3226_ = v___y_3271_;
v___y_3227_ = v___y_3257_;
v___y_3228_ = v___y_3259_;
v___y_3229_ = v___y_3258_;
v___y_3230_ = v___y_3272_;
v___y_3231_ = v___y_3273_;
v___y_3232_ = v___y_3270_;
v___y_3233_ = v___y_3264_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___y_3262_;
v___y_3236_ = v___y_3266_;
v___y_3237_ = v___y_3269_;
v___y_3238_ = v___y_3268_;
v___y_3239_ = v___y_3260_;
v___y_3240_ = v___y_3263_;
v_args_3241_ = v___x_3285_;
goto v___jp_3220_;
}
}
v___jp_3286_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3298_ = lean_unsigned_to_nat(3u);
v___x_3299_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3298_);
lean_dec(v_stx_3137_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3299_);
v___x_3301_ = l_Lean_Syntax_isOfKind(v___x_3299_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; 
lean_dec(v___x_3299_);
lean_dec(v_unfold_3297_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v_tk_3156_);
v___x_3302_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3302_;
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3303_ = l_Lean_Syntax_getArg(v___x_3299_, v___x_3155_);
v___x_3304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3303_);
v___x_3305_ = l_Lean_Syntax_isOfKind(v___x_3303_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
lean_dec(v___x_3303_);
lean_dec(v___x_3299_);
lean_dec(v_unfold_3297_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v_tk_3156_);
v___x_3306_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3307_ = l_Lean_Syntax_getArg(v___x_3299_, v___x_3157_);
v___x_3308_ = l_Lean_Syntax_getArg(v___x_3299_, v___y_3294_);
v___x_3309_ = l_Lean_Syntax_isNone(v___x_3308_);
if (v___x_3309_ == 0)
{
uint8_t v___x_3310_; 
lean_inc(v___x_3308_);
v___x_3310_ = l_Lean_Syntax_matchesNull(v___x_3308_, v___x_3157_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; 
lean_dec(v___x_3308_);
lean_dec(v___x_3307_);
lean_dec(v___x_3303_);
lean_dec(v___x_3299_);
lean_dec(v_unfold_3297_);
lean_dec(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v_tk_3156_);
v___x_3311_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3311_;
}
else
{
lean_object* v_only_3312_; lean_object* v___x_3313_; 
v_only_3312_ = l_Lean_Syntax_getArg(v___x_3308_, v___x_3155_);
lean_dec(v___x_3308_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_only_3312_);
lean_inc(v___y_3294_);
v___y_3253_ = v___x_3300_;
v___y_3254_ = v___x_3303_;
v___y_3255_ = v_unfold_3297_;
v___y_3256_ = v___x_3305_;
v___y_3257_ = v___x_3304_;
v___y_3258_ = v___y_3293_;
v___y_3259_ = v___x_3298_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___x_3298_;
v___y_3262_ = v___y_3294_;
v___y_3263_ = v___x_3307_;
v___y_3264_ = v___x_3299_;
v_only_3265_ = v___x_3313_;
v___y_3266_ = v___y_3296_;
v___y_3267_ = v___y_3290_;
v___y_3268_ = v___y_3288_;
v___y_3269_ = v___y_3292_;
v___y_3270_ = v___y_3287_;
v___y_3271_ = v___y_3289_;
v___y_3272_ = v___y_3295_;
v___y_3273_ = v___y_3291_;
goto v___jp_3252_;
}
}
else
{
lean_object* v___x_3314_; 
lean_dec(v___x_3308_);
v___x_3314_ = lean_box(0);
lean_inc(v___y_3294_);
v___y_3253_ = v___x_3300_;
v___y_3254_ = v___x_3303_;
v___y_3255_ = v_unfold_3297_;
v___y_3256_ = v___x_3305_;
v___y_3257_ = v___x_3304_;
v___y_3258_ = v___y_3293_;
v___y_3259_ = v___x_3298_;
v___y_3260_ = v___y_3294_;
v___y_3261_ = v___x_3298_;
v___y_3262_ = v___y_3294_;
v___y_3263_ = v___x_3307_;
v___y_3264_ = v___x_3299_;
v_only_3265_ = v___x_3314_;
v___y_3266_ = v___y_3296_;
v___y_3267_ = v___y_3290_;
v___y_3268_ = v___y_3288_;
v___y_3269_ = v___y_3292_;
v___y_3270_ = v___y_3287_;
v___y_3271_ = v___y_3289_;
v___y_3272_ = v___y_3295_;
v___y_3273_ = v___y_3291_;
goto v___jp_3252_;
}
}
}
}
v___jp_3315_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3325_ = lean_unsigned_to_nat(2u);
v___x_3326_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3325_);
v___x_3327_ = l_Lean_Syntax_isNone(v___x_3326_);
if (v___x_3327_ == 0)
{
uint8_t v___x_3328_; 
lean_inc(v___x_3326_);
v___x_3328_ = l_Lean_Syntax_matchesNull(v___x_3326_, v___x_3157_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; 
lean_dec(v___x_3326_);
lean_dec(v_squeeze_3316_);
lean_dec(v_tk_3156_);
lean_dec(v_stx_3137_);
v___x_3329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3329_;
}
else
{
lean_object* v_unfold_3330_; lean_object* v___x_3331_; 
v_unfold_3330_ = l_Lean_Syntax_getArg(v___x_3326_, v___x_3155_);
lean_dec(v___x_3326_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_unfold_3330_);
v___y_3287_ = v___y_3321_;
v___y_3288_ = v___y_3319_;
v___y_3289_ = v___y_3322_;
v___y_3290_ = v___y_3318_;
v___y_3291_ = v___y_3324_;
v___y_3292_ = v___y_3320_;
v___y_3293_ = v_squeeze_3316_;
v___y_3294_ = v___x_3325_;
v___y_3295_ = v___y_3323_;
v___y_3296_ = v___y_3317_;
v_unfold_3297_ = v___x_3331_;
goto v___jp_3286_;
}
}
else
{
lean_object* v___x_3332_; 
lean_dec(v___x_3326_);
v___x_3332_ = lean_box(0);
v___y_3287_ = v___y_3321_;
v___y_3288_ = v___y_3319_;
v___y_3289_ = v___y_3322_;
v___y_3290_ = v___y_3318_;
v___y_3291_ = v___y_3324_;
v___y_3292_ = v___y_3320_;
v___y_3293_ = v_squeeze_3316_;
v___y_3294_ = v___x_3325_;
v___y_3295_ = v___y_3323_;
v___y_3296_ = v___y_3317_;
v_unfold_3297_ = v___x_3332_;
goto v___jp_3286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3340_, lean_object* v_stx_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
uint8_t v_useReducible_boxed_3351_; lean_object* v_res_3352_; 
v_useReducible_boxed_3351_ = lean_unbox(v_useReducible_3340_);
v_res_3352_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3351_, v_stx_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3353_, lean_object* v_val_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3353_, v_val_3354_, v___y_3360_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3365_, lean_object* v_val_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3365_, v_val_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3377_, v___y_3385_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v_00_u03b1_3399_, lean_object* v_msg_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_3400_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v_00_u03b1_3411_, lean_object* v_msg_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_3411_, v_msg_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_00_u03b1_3423_, lean_object* v_x_3424_, lean_object* v_mkInfoTree_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_3424_, v_mkInfoTree_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_00_u03b1_3436_, lean_object* v_x_3437_, lean_object* v_mkInfoTree_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_3436_, v_x_3437_, v_mkInfoTree_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3449_, lean_object* v_x_3450_, lean_object* v_x_3451_, lean_object* v_x_3452_){
_start:
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3450_, v_x_3451_, v_x_3452_);
return v___x_3453_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3454_, lean_object* v_m_3455_, lean_object* v_a_3456_){
_start:
{
uint8_t v___x_3457_; 
v___x_3457_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3455_, v_a_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3458_, lean_object* v_m_3459_, lean_object* v_a_3460_){
_start:
{
uint8_t v_res_3461_; lean_object* v_r_3462_; 
v_res_3461_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_3458_, v_m_3459_, v_a_3460_);
lean_dec_ref(v_a_3460_);
lean_dec_ref(v_m_3459_);
v_r_3462_ = lean_box(v_res_3461_);
return v_r_3462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3463_, lean_object* v_m_3464_, lean_object* v_a_3465_, lean_object* v_b_3466_){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_m_3464_, v_a_3465_, v_b_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3468_, v___y_3469_, v___y_3475_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(v_mvarId_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v_mvarId_3480_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3492_, v___y_3493_, v___y_3499_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_mvarId_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v_mvarId_3504_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3516_, lean_object* v_x_3517_, size_t v_x_3518_, size_t v_x_3519_, lean_object* v_x_3520_, lean_object* v_x_3521_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_3517_, v_x_3518_, v_x_3519_, v_x_3520_, v_x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3523_, lean_object* v_x_3524_, lean_object* v_x_3525_, lean_object* v_x_3526_, lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
size_t v_x_98168__boxed_3529_; size_t v_x_98169__boxed_3530_; lean_object* v_res_3531_; 
v_x_98168__boxed_3529_ = lean_unbox_usize(v_x_3525_);
lean_dec(v_x_3525_);
v_x_98169__boxed_3530_ = lean_unbox_usize(v_x_3526_);
lean_dec(v_x_3526_);
v_res_3531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_3523_, v_x_3524_, v_x_98168__boxed_3529_, v_x_98169__boxed_3530_, v_x_3527_, v_x_3528_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(lean_object* v_ref_3532_, lean_object* v_msgData_3533_, uint8_t v_severity_3534_, uint8_t v_isSilent_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_3532_, v_msgData_3533_, v_severity_3534_, v_isSilent_3535_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3546_, lean_object* v_msgData_3547_, lean_object* v_severity_3548_, lean_object* v_isSilent_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
uint8_t v_severity_boxed_3559_; uint8_t v_isSilent_boxed_3560_; lean_object* v_res_3561_; 
v_severity_boxed_3559_ = lean_unbox(v_severity_3548_);
v_isSilent_boxed_3560_ = lean_unbox(v_isSilent_3549_);
v_res_3561_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(v_ref_3546_, v_msgData_3547_, v_severity_boxed_3559_, v_isSilent_boxed_3560_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v_ref_3546_);
return v_res_3561_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3562_, lean_object* v_a_3563_, lean_object* v_x_3564_){
_start:
{
uint8_t v___x_3565_; 
v___x_3565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3563_, v_x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3566_, lean_object* v_a_3567_, lean_object* v_x_3568_){
_start:
{
uint8_t v_res_3569_; lean_object* v_r_3570_; 
v_res_3569_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3566_, v_a_3567_, v_x_3568_);
lean_dec(v_x_3568_);
lean_dec_ref(v_a_3567_);
v_r_3570_ = lean_box(v_res_3569_);
return v_r_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3571_, lean_object* v_data_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3574_, lean_object* v_n_3575_, lean_object* v_k_3576_, lean_object* v_v_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3575_, v_k_3576_, v_v_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3579_, size_t v_depth_3580_, lean_object* v_keys_3581_, lean_object* v_vals_3582_, lean_object* v_heq_3583_, lean_object* v_i_3584_, lean_object* v_entries_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3580_, v_keys_3581_, v_vals_3582_, v_i_3584_, v_entries_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3587_, lean_object* v_depth_3588_, lean_object* v_keys_3589_, lean_object* v_vals_3590_, lean_object* v_heq_3591_, lean_object* v_i_3592_, lean_object* v_entries_3593_){
_start:
{
size_t v_depth_boxed_3594_; lean_object* v_res_3595_; 
v_depth_boxed_3594_ = lean_unbox_usize(v_depth_3588_);
lean_dec(v_depth_3588_);
v_res_3595_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3587_, v_depth_boxed_3594_, v_keys_3589_, v_vals_3590_, v_heq_3591_, v_i_3592_, v_entries_3593_);
lean_dec_ref(v_vals_3590_);
lean_dec_ref(v_keys_3589_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3596_, lean_object* v_i_3597_, lean_object* v_source_3598_, lean_object* v_target_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3597_, v_source_3598_, v_target_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3601_, lean_object* v_x_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3602_, v_x_3603_, v_x_3604_, v_x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3607_, lean_object* v_x_3608_, lean_object* v_x_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3608_, v_x_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
uint8_t v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = 1;
v___x_3622_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_3621_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
lean_dec(v_a_3627_);
lean_dec_ref(v_a_3626_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3643_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3646_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3647_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3643_, v___x_3644_, v___x_3645_, v___x_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3678_ = l_Lean_addBuiltinDeclarationRanges(v___x_3676_, v___x_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_3685_);
lean_dec(v_x_3685_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; uint8_t v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_3698_);
v___x_3740_ = l_Lean_Syntax_isOfKind(v_stx_3698_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec(v_stx_3698_);
v___x_3741_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; uint8_t v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; uint8_t v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; uint8_t v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v_tk_3869_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v_args_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___x_3929_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v_only_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v_unfold_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v_squeeze_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v___x_3742_ = lean_unsigned_to_nat(0u);
v_tk_3869_ = l_Lean_Syntax_getArg(v_stx_3698_, v___x_3742_);
v___x_3929_ = lean_unsigned_to_nat(1u);
v___x_4005_ = l_Lean_Syntax_getArg(v_stx_3698_, v___x_3929_);
v___x_4006_ = l_Lean_Syntax_isNone(v___x_4005_);
if (v___x_4006_ == 0)
{
uint8_t v___x_4007_; 
lean_inc(v___x_4005_);
v___x_4007_ = l_Lean_Syntax_matchesNull(v___x_4005_, v___x_3929_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; 
lean_dec(v___x_4005_);
lean_dec(v_tk_3869_);
lean_dec(v_stx_3698_);
v___x_4008_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4008_;
}
else
{
lean_object* v_squeeze_4009_; lean_object* v___x_4010_; 
v_squeeze_4009_ = l_Lean_Syntax_getArg(v___x_4005_, v___x_3742_);
lean_dec(v___x_4005_);
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v_squeeze_4009_);
v_squeeze_3988_ = v___x_4010_;
v___y_3989_ = v_a_3699_;
v___y_3990_ = v_a_3700_;
v___y_3991_ = v_a_3701_;
v___y_3992_ = v_a_3702_;
v___y_3993_ = v_a_3703_;
v___y_3994_ = v_a_3704_;
v___y_3995_ = v_a_3705_;
v___y_3996_ = v_a_3706_;
goto v___jp_3987_;
}
}
else
{
lean_object* v___x_4011_; 
lean_dec(v___x_4005_);
v___x_4011_ = lean_box(0);
v_squeeze_3988_ = v___x_4011_;
v___y_3989_ = v_a_3699_;
v___y_3990_ = v_a_3700_;
v___y_3991_ = v_a_3701_;
v___y_3992_ = v_a_3702_;
v___y_3993_ = v_a_3703_;
v___y_3994_ = v_a_3704_;
v___y_3995_ = v_a_3705_;
v___y_3996_ = v_a_3706_;
goto v___jp_3987_;
}
v___jp_3743_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_inc_ref(v___y_3756_);
v___x_3766_ = l_Array_append___redArg(v___y_3756_, v___y_3765_);
lean_dec_ref(v___y_3765_);
lean_inc(v___y_3750_);
lean_inc(v___y_3764_);
v___x_3767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3767_, 0, v___y_3764_);
lean_ctor_set(v___x_3767_, 1, v___y_3750_);
lean_ctor_set(v___x_3767_, 2, v___x_3766_);
if (lean_obj_tag(v___y_3752_) == 1)
{
lean_object* v_val_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_val_3768_ = lean_ctor_get(v___y_3752_, 0);
lean_inc(v_val_3768_);
lean_dec_ref_known(v___y_3752_, 1);
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3764_, 4);
v___x_3771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___y_3764_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
lean_inc_ref(v___y_3756_);
v___x_3772_ = l_Array_append___redArg(v___y_3756_, v_val_3768_);
lean_dec(v_val_3768_);
lean_inc(v___y_3750_);
v___x_3773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3773_, 0, v___y_3764_);
lean_ctor_set(v___x_3773_, 1, v___y_3750_);
lean_ctor_set(v___x_3773_, 2, v___x_3772_);
v___x_3774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___y_3764_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = l_Lean_Syntax_node3(v___y_3764_, v___x_3769_, v___x_3771_, v___x_3773_, v___x_3775_);
v___x_3777_ = l_Array_mkArray1___redArg(v___x_3776_);
v___y_3709_ = v___y_3744_;
v___y_3710_ = v___y_3745_;
v___y_3711_ = v___y_3746_;
v___y_3712_ = v___y_3747_;
v___y_3713_ = v___y_3748_;
v___y_3714_ = v___y_3749_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v___y_3751_;
v___y_3717_ = v___x_3767_;
v___y_3718_ = v___y_3753_;
v___y_3719_ = v___y_3754_;
v___y_3720_ = v___y_3755_;
v___y_3721_ = v___y_3756_;
v___y_3722_ = v___y_3759_;
v___y_3723_ = v___y_3758_;
v___y_3724_ = v___y_3757_;
v___y_3725_ = v___y_3760_;
v___y_3726_ = v___y_3761_;
v___y_3727_ = v___y_3762_;
v___y_3728_ = v___y_3763_;
v___y_3729_ = v___y_3764_;
v___y_3730_ = v___x_3777_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3778_; 
lean_dec(v___y_3752_);
v___x_3778_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3709_ = v___y_3744_;
v___y_3710_ = v___y_3745_;
v___y_3711_ = v___y_3746_;
v___y_3712_ = v___y_3747_;
v___y_3713_ = v___y_3748_;
v___y_3714_ = v___y_3749_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v___y_3751_;
v___y_3717_ = v___x_3767_;
v___y_3718_ = v___y_3753_;
v___y_3719_ = v___y_3754_;
v___y_3720_ = v___y_3755_;
v___y_3721_ = v___y_3756_;
v___y_3722_ = v___y_3759_;
v___y_3723_ = v___y_3758_;
v___y_3724_ = v___y_3757_;
v___y_3725_ = v___y_3760_;
v___y_3726_ = v___y_3761_;
v___y_3727_ = v___y_3762_;
v___y_3728_ = v___y_3763_;
v___y_3729_ = v___y_3764_;
v___y_3730_ = v___x_3778_;
goto v___jp_3708_;
}
}
v___jp_3779_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_inc_ref(v___y_3793_);
v___x_3802_ = l_Array_append___redArg(v___y_3793_, v___y_3801_);
lean_dec_ref(v___y_3801_);
lean_inc(v___y_3786_);
lean_inc(v___y_3800_);
v___x_3803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3803_, 0, v___y_3800_);
lean_ctor_set(v___x_3803_, 1, v___y_3786_);
lean_ctor_set(v___x_3803_, 2, v___x_3802_);
if (lean_obj_tag(v___y_3791_) == 1)
{
lean_object* v_val_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v_val_3804_ = lean_ctor_get(v___y_3791_, 0);
lean_inc(v_val_3804_);
lean_dec_ref_known(v___y_3791_, 1);
v___x_3805_ = l_Lean_SourceInfo_fromRef(v_val_3804_, v___x_3740_);
lean_dec(v_val_3804_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = l_Array_mkArray1___redArg(v___x_3807_);
v___y_3744_ = v___y_3780_;
v___y_3745_ = v___y_3781_;
v___y_3746_ = v___y_3782_;
v___y_3747_ = v___y_3783_;
v___y_3748_ = v___y_3784_;
v___y_3749_ = v___y_3785_;
v___y_3750_ = v___y_3786_;
v___y_3751_ = v___y_3787_;
v___y_3752_ = v___y_3788_;
v___y_3753_ = v___y_3789_;
v___y_3754_ = v___y_3790_;
v___y_3755_ = v___y_3792_;
v___y_3756_ = v___y_3793_;
v___y_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
v___y_3759_ = v___y_3794_;
v___y_3760_ = v___y_3797_;
v___y_3761_ = v___y_3798_;
v___y_3762_ = v___x_3803_;
v___y_3763_ = v___y_3799_;
v___y_3764_ = v___y_3800_;
v___y_3765_ = v___x_3808_;
goto v___jp_3743_;
}
else
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3791_);
lean_dec(v___y_3791_);
v___y_3744_ = v___y_3780_;
v___y_3745_ = v___y_3781_;
v___y_3746_ = v___y_3782_;
v___y_3747_ = v___y_3783_;
v___y_3748_ = v___y_3784_;
v___y_3749_ = v___y_3785_;
v___y_3750_ = v___y_3786_;
v___y_3751_ = v___y_3787_;
v___y_3752_ = v___y_3788_;
v___y_3753_ = v___y_3789_;
v___y_3754_ = v___y_3790_;
v___y_3755_ = v___y_3792_;
v___y_3756_ = v___y_3793_;
v___y_3757_ = v___y_3796_;
v___y_3758_ = v___y_3795_;
v___y_3759_ = v___y_3794_;
v___y_3760_ = v___y_3797_;
v___y_3761_ = v___y_3798_;
v___y_3762_ = v___x_3803_;
v___y_3763_ = v___y_3799_;
v___y_3764_ = v___y_3800_;
v___y_3765_ = v___x_3809_;
goto v___jp_3743_;
}
}
v___jp_3810_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_inc_ref(v___y_3822_);
v___x_3832_ = l_Array_append___redArg(v___y_3822_, v___y_3831_);
lean_dec_ref(v___y_3831_);
lean_inc(v___y_3816_);
lean_inc(v___y_3830_);
v___x_3833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3833_, 0, v___y_3830_);
lean_ctor_set(v___x_3833_, 1, v___y_3816_);
lean_ctor_set(v___x_3833_, 2, v___x_3832_);
v___x_3834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_3823_) == 0)
{
lean_object* v___x_3835_; 
v___x_3835_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3780_ = v___y_3811_;
v___y_3781_ = v___y_3812_;
v___y_3782_ = v___y_3813_;
v___y_3783_ = v___x_3833_;
v___y_3784_ = v___y_3814_;
v___y_3785_ = v___y_3815_;
v___y_3786_ = v___y_3816_;
v___y_3787_ = v___x_3834_;
v___y_3788_ = v___y_3817_;
v___y_3789_ = v___y_3818_;
v___y_3790_ = v___y_3819_;
v___y_3791_ = v___y_3820_;
v___y_3792_ = v___y_3821_;
v___y_3793_ = v___y_3822_;
v___y_3794_ = v___y_3826_;
v___y_3795_ = v___y_3825_;
v___y_3796_ = v___y_3824_;
v___y_3797_ = v___y_3827_;
v___y_3798_ = v___y_3828_;
v___y_3799_ = v___y_3829_;
v___y_3800_ = v___y_3830_;
v___y_3801_ = v___x_3835_;
goto v___jp_3779_;
}
else
{
lean_object* v_val_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v_val_3836_ = lean_ctor_get(v___y_3823_, 0);
lean_inc(v_val_3836_);
lean_dec_ref_known(v___y_3823_, 1);
v___x_3837_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3838_ = lean_array_push(v___x_3837_, v_val_3836_);
v___y_3780_ = v___y_3811_;
v___y_3781_ = v___y_3812_;
v___y_3782_ = v___y_3813_;
v___y_3783_ = v___x_3833_;
v___y_3784_ = v___y_3814_;
v___y_3785_ = v___y_3815_;
v___y_3786_ = v___y_3816_;
v___y_3787_ = v___x_3834_;
v___y_3788_ = v___y_3817_;
v___y_3789_ = v___y_3818_;
v___y_3790_ = v___y_3819_;
v___y_3791_ = v___y_3820_;
v___y_3792_ = v___y_3821_;
v___y_3793_ = v___y_3822_;
v___y_3794_ = v___y_3826_;
v___y_3795_ = v___y_3825_;
v___y_3796_ = v___y_3824_;
v___y_3797_ = v___y_3827_;
v___y_3798_ = v___y_3828_;
v___y_3799_ = v___y_3829_;
v___y_3800_ = v___y_3830_;
v___y_3801_ = v___x_3838_;
goto v___jp_3779_;
}
}
v___jp_3839_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_inc_ref(v___y_3850_);
v___x_3861_ = l_Array_append___redArg(v___y_3850_, v___y_3860_);
lean_dec_ref(v___y_3860_);
lean_inc(v___y_3846_);
lean_inc(v___y_3859_);
v___x_3862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3862_, 0, v___y_3859_);
lean_ctor_set(v___x_3862_, 1, v___y_3846_);
lean_ctor_set(v___x_3862_, 2, v___x_3861_);
if (lean_obj_tag(v___y_3845_) == 1)
{
lean_object* v_val_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v_val_3863_ = lean_ctor_get(v___y_3845_, 0);
lean_inc(v_val_3863_);
lean_dec_ref_known(v___y_3845_, 1);
v___x_3864_ = l_Lean_SourceInfo_fromRef(v_val_3863_, v___x_3740_);
lean_dec(v_val_3863_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_3866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3864_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v___x_3867_ = l_Array_mkArray1___redArg(v___x_3866_);
v___y_3811_ = v___y_3840_;
v___y_3812_ = v___y_3841_;
v___y_3813_ = v___y_3842_;
v___y_3814_ = v___y_3843_;
v___y_3815_ = v___y_3844_;
v___y_3816_ = v___y_3846_;
v___y_3817_ = v___y_3847_;
v___y_3818_ = v___y_3848_;
v___y_3819_ = v___x_3862_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3851_;
v___y_3822_ = v___y_3850_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3855_;
v___y_3825_ = v___y_3854_;
v___y_3826_ = v___y_3853_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3857_;
v___y_3829_ = v___y_3858_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___x_3867_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3845_);
lean_dec(v___y_3845_);
v___y_3811_ = v___y_3840_;
v___y_3812_ = v___y_3841_;
v___y_3813_ = v___y_3842_;
v___y_3814_ = v___y_3843_;
v___y_3815_ = v___y_3844_;
v___y_3816_ = v___y_3846_;
v___y_3817_ = v___y_3847_;
v___y_3818_ = v___y_3848_;
v___y_3819_ = v___x_3862_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3851_;
v___y_3822_ = v___y_3850_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3855_;
v___y_3825_ = v___y_3854_;
v___y_3826_ = v___y_3853_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3857_;
v___y_3829_ = v___y_3858_;
v___y_3830_ = v___y_3859_;
v___y_3831_ = v___x_3868_;
goto v___jp_3810_;
}
}
v___jp_3870_:
{
lean_object* v_ref_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_ref_3886_ = lean_ctor_get(v___y_3879_, 5);
v___x_3887_ = 0;
v___x_3888_ = l_Lean_SourceInfo_fromRef(v_ref_3886_, v___x_3887_);
v___x_3889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3891_ = l_Lean_SourceInfo_fromRef(v_tk_3869_, v___x_3740_);
lean_dec(v_tk_3869_);
v___x_3892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v___x_3889_);
v___x_3893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_3894_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_3883_) == 1)
{
lean_object* v_val_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_val_3895_ = lean_ctor_get(v___y_3883_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___y_3883_, 1);
v___x_3896_ = l_Lean_SourceInfo_fromRef(v_val_3895_, v___x_3740_);
lean_dec(v_val_3895_);
v___x_3897_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_3898_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = l_Array_mkArray1___redArg(v___x_3898_);
v___y_3840_ = v___y_3871_;
v___y_3841_ = v___x_3892_;
v___y_3842_ = v___y_3872_;
v___y_3843_ = v___y_3873_;
v___y_3844_ = v___y_3874_;
v___y_3845_ = v___y_3875_;
v___y_3846_ = v___x_3893_;
v___y_3847_ = v___y_3876_;
v___y_3848_ = v___x_3890_;
v___y_3849_ = v___y_3877_;
v___y_3850_ = v___x_3894_;
v___y_3851_ = v___y_3878_;
v___y_3852_ = v___y_3885_;
v___y_3853_ = v___y_3879_;
v___y_3854_ = v___y_3880_;
v___y_3855_ = v___x_3887_;
v___y_3856_ = v___y_3881_;
v___y_3857_ = v___y_3882_;
v___y_3858_ = v___y_3884_;
v___y_3859_ = v___x_3888_;
v___y_3860_ = v___x_3899_;
goto v___jp_3839_;
}
else
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3883_);
lean_dec(v___y_3883_);
v___y_3840_ = v___y_3871_;
v___y_3841_ = v___x_3892_;
v___y_3842_ = v___y_3872_;
v___y_3843_ = v___y_3873_;
v___y_3844_ = v___y_3874_;
v___y_3845_ = v___y_3875_;
v___y_3846_ = v___x_3893_;
v___y_3847_ = v___y_3876_;
v___y_3848_ = v___x_3890_;
v___y_3849_ = v___y_3877_;
v___y_3850_ = v___x_3894_;
v___y_3851_ = v___y_3878_;
v___y_3852_ = v___y_3885_;
v___y_3853_ = v___y_3879_;
v___y_3854_ = v___y_3880_;
v___y_3855_ = v___x_3887_;
v___y_3856_ = v___y_3881_;
v___y_3857_ = v___y_3882_;
v___y_3858_ = v___y_3884_;
v___y_3859_ = v___x_3888_;
v___y_3860_ = v___x_3900_;
goto v___jp_3839_;
}
}
v___jp_3901_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_unsigned_to_nat(5u);
v___x_3918_ = l_Lean_Syntax_getArg(v___y_3904_, v___x_3917_);
lean_dec(v___y_3904_);
v___x_3919_ = l_Lean_Syntax_getOptional_x3f(v___y_3902_);
lean_dec(v___y_3902_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_box(0);
v___y_3871_ = v___y_3916_;
v___y_3872_ = v___y_3914_;
v___y_3873_ = v___x_3918_;
v___y_3874_ = v___y_3910_;
v___y_3875_ = v___y_3905_;
v___y_3876_ = v_args_3908_;
v___y_3877_ = v___y_3907_;
v___y_3878_ = v___y_3913_;
v___y_3879_ = v___y_3915_;
v___y_3880_ = v___y_3911_;
v___y_3881_ = v___y_3903_;
v___y_3882_ = v___y_3912_;
v___y_3883_ = v___y_3906_;
v___y_3884_ = v___y_3909_;
v___y_3885_ = v___x_3920_;
goto v___jp_3870_;
}
else
{
lean_object* v_val_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
v_val_3921_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3919_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_val_3921_);
lean_dec(v___x_3919_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_val_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
v___y_3871_ = v___y_3916_;
v___y_3872_ = v___y_3914_;
v___y_3873_ = v___x_3918_;
v___y_3874_ = v___y_3910_;
v___y_3875_ = v___y_3905_;
v___y_3876_ = v_args_3908_;
v___y_3877_ = v___y_3907_;
v___y_3878_ = v___y_3913_;
v___y_3879_ = v___y_3915_;
v___y_3880_ = v___y_3911_;
v___y_3881_ = v___y_3903_;
v___y_3882_ = v___y_3912_;
v___y_3883_ = v___y_3906_;
v___y_3884_ = v___y_3909_;
v___y_3885_ = v___x_3926_;
goto v___jp_3870_;
}
}
}
}
v___jp_3930_:
{
lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = l_Lean_Syntax_getArg(v___y_3933_, v___y_3931_);
v___x_3947_ = l_Lean_Syntax_isNone(v___x_3946_);
if (v___x_3947_ == 0)
{
uint8_t v___x_3948_; 
lean_inc(v___x_3946_);
v___x_3948_ = l_Lean_Syntax_matchesNull(v___x_3946_, v___x_3929_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec(v___x_3946_);
lean_dec(v_only_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec(v_tk_3869_);
v___x_3949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3950_ = l_Lean_Syntax_getArg(v___x_3946_, v___x_3742_);
lean_dec(v___x_3946_);
v___x_3951_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3950_);
v___x_3952_ = l_Lean_Syntax_isOfKind(v___x_3950_, v___x_3951_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; 
lean_dec(v___x_3950_);
lean_dec(v_only_3937_);
lean_dec(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec(v_tk_3869_);
v___x_3953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3953_;
}
else
{
lean_object* v___x_3954_; lean_object* v_args_3955_; lean_object* v___x_3956_; 
v___x_3954_ = l_Lean_Syntax_getArg(v___x_3950_, v___x_3929_);
lean_dec(v___x_3950_);
v_args_3955_ = l_Lean_Syntax_getArgs(v___x_3954_);
lean_dec(v___x_3954_);
v___x_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_args_3955_);
v___y_3902_ = v___y_3932_;
v___y_3903_ = v___y_3934_;
v___y_3904_ = v___y_3933_;
v___y_3905_ = v___y_3935_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v_only_3937_;
v_args_3908_ = v___x_3956_;
v___y_3909_ = v___y_3938_;
v___y_3910_ = v___y_3939_;
v___y_3911_ = v___y_3940_;
v___y_3912_ = v___y_3941_;
v___y_3913_ = v___y_3942_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v___y_3945_;
goto v___jp_3901_;
}
}
}
else
{
lean_object* v___x_3957_; 
lean_dec(v___x_3946_);
v___x_3957_ = lean_box(0);
v___y_3902_ = v___y_3932_;
v___y_3903_ = v___y_3934_;
v___y_3904_ = v___y_3933_;
v___y_3905_ = v___y_3935_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v_only_3937_;
v_args_3908_ = v___x_3957_;
v___y_3909_ = v___y_3938_;
v___y_3910_ = v___y_3939_;
v___y_3911_ = v___y_3940_;
v___y_3912_ = v___y_3941_;
v___y_3913_ = v___y_3942_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3944_;
v___y_3916_ = v___y_3945_;
goto v___jp_3901_;
}
}
v___jp_3958_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3970_ = lean_unsigned_to_nat(3u);
v___x_3971_ = l_Lean_Syntax_getArg(v_stx_3698_, v___x_3970_);
lean_dec(v_stx_3698_);
v___x_3972_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_3971_);
v___x_3973_ = l_Lean_Syntax_isOfKind(v___x_3971_, v___x_3972_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
lean_dec(v___x_3971_);
lean_dec(v_unfold_3961_);
lean_dec(v___y_3960_);
lean_dec(v_tk_3869_);
v___x_3974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3974_;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3975_ = l_Lean_Syntax_getArg(v___x_3971_, v___x_3742_);
v___x_3976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3975_);
v___x_3977_ = l_Lean_Syntax_isOfKind(v___x_3975_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; 
lean_dec(v___x_3975_);
lean_dec(v___x_3971_);
lean_dec(v_unfold_3961_);
lean_dec(v___y_3960_);
lean_dec(v_tk_3869_);
v___x_3978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3978_;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; uint8_t v___x_3981_; 
v___x_3979_ = l_Lean_Syntax_getArg(v___x_3971_, v___x_3929_);
v___x_3980_ = l_Lean_Syntax_getArg(v___x_3971_, v___y_3959_);
v___x_3981_ = l_Lean_Syntax_isNone(v___x_3980_);
if (v___x_3981_ == 0)
{
uint8_t v___x_3982_; 
lean_inc(v___x_3980_);
v___x_3982_ = l_Lean_Syntax_matchesNull(v___x_3980_, v___x_3929_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
lean_dec(v___x_3980_);
lean_dec(v___x_3979_);
lean_dec(v___x_3975_);
lean_dec(v___x_3971_);
lean_dec(v_unfold_3961_);
lean_dec(v___y_3960_);
lean_dec(v_tk_3869_);
v___x_3983_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3983_;
}
else
{
lean_object* v_only_3984_; lean_object* v___x_3985_; 
v_only_3984_ = l_Lean_Syntax_getArg(v___x_3980_, v___x_3742_);
lean_dec(v___x_3980_);
v___x_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3985_, 0, v_only_3984_);
v___y_3931_ = v___x_3970_;
v___y_3932_ = v___x_3979_;
v___y_3933_ = v___x_3971_;
v___y_3934_ = v___x_3975_;
v___y_3935_ = v_unfold_3961_;
v___y_3936_ = v___y_3960_;
v_only_3937_ = v___x_3985_;
v___y_3938_ = v___y_3962_;
v___y_3939_ = v___y_3963_;
v___y_3940_ = v___y_3964_;
v___y_3941_ = v___y_3965_;
v___y_3942_ = v___y_3966_;
v___y_3943_ = v___y_3967_;
v___y_3944_ = v___y_3968_;
v___y_3945_ = v___y_3969_;
goto v___jp_3930_;
}
}
else
{
lean_object* v___x_3986_; 
lean_dec(v___x_3980_);
v___x_3986_ = lean_box(0);
v___y_3931_ = v___x_3970_;
v___y_3932_ = v___x_3979_;
v___y_3933_ = v___x_3971_;
v___y_3934_ = v___x_3975_;
v___y_3935_ = v_unfold_3961_;
v___y_3936_ = v___y_3960_;
v_only_3937_ = v___x_3986_;
v___y_3938_ = v___y_3962_;
v___y_3939_ = v___y_3963_;
v___y_3940_ = v___y_3964_;
v___y_3941_ = v___y_3965_;
v___y_3942_ = v___y_3966_;
v___y_3943_ = v___y_3967_;
v___y_3944_ = v___y_3968_;
v___y_3945_ = v___y_3969_;
goto v___jp_3930_;
}
}
}
}
v___jp_3987_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v___x_3997_ = lean_unsigned_to_nat(2u);
v___x_3998_ = l_Lean_Syntax_getArg(v_stx_3698_, v___x_3997_);
v___x_3999_ = l_Lean_Syntax_isNone(v___x_3998_);
if (v___x_3999_ == 0)
{
uint8_t v___x_4000_; 
lean_inc(v___x_3998_);
v___x_4000_ = l_Lean_Syntax_matchesNull(v___x_3998_, v___x_3929_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
lean_dec(v___x_3998_);
lean_dec(v_squeeze_3988_);
lean_dec(v_tk_3869_);
lean_dec(v_stx_3698_);
v___x_4001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4001_;
}
else
{
lean_object* v_unfold_4002_; lean_object* v___x_4003_; 
v_unfold_4002_ = l_Lean_Syntax_getArg(v___x_3998_, v___x_3742_);
lean_dec(v___x_3998_);
v___x_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4003_, 0, v_unfold_4002_);
v___y_3959_ = v___x_3997_;
v___y_3960_ = v_squeeze_3988_;
v_unfold_3961_ = v___x_4003_;
v___y_3962_ = v___y_3989_;
v___y_3963_ = v___y_3990_;
v___y_3964_ = v___y_3991_;
v___y_3965_ = v___y_3992_;
v___y_3966_ = v___y_3993_;
v___y_3967_ = v___y_3994_;
v___y_3968_ = v___y_3995_;
v___y_3969_ = v___y_3996_;
goto v___jp_3958_;
}
}
else
{
lean_object* v___x_4004_; 
lean_dec(v___x_3998_);
v___x_4004_ = lean_box(0);
v___y_3959_ = v___x_3997_;
v___y_3960_ = v_squeeze_3988_;
v_unfold_3961_ = v___x_4004_;
v___y_3962_ = v___y_3989_;
v___y_3963_ = v___y_3990_;
v___y_3964_ = v___y_3991_;
v___y_3965_ = v___y_3992_;
v___y_3966_ = v___y_3993_;
v___y_3967_ = v___y_3994_;
v___y_3968_ = v___y_3995_;
v___y_3969_ = v___y_3996_;
goto v___jp_3958_;
}
}
}
v___jp_3708_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_inc_ref(v___y_3721_);
v___x_3731_ = l_Array_append___redArg(v___y_3721_, v___y_3730_);
lean_dec_ref(v___y_3730_);
lean_inc_n(v___y_3715_, 2);
lean_inc_n(v___y_3729_, 4);
v___x_3732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3732_, 0, v___y_3729_);
lean_ctor_set(v___x_3732_, 1, v___y_3715_);
lean_ctor_set(v___x_3732_, 2, v___x_3731_);
v___x_3733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___y_3729_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = l_Lean_Syntax_node2(v___y_3729_, v___y_3715_, v___x_3734_, v___y_3713_);
lean_inc(v___y_3716_);
v___x_3736_ = l_Lean_Syntax_node5(v___y_3729_, v___y_3716_, v___y_3725_, v___y_3727_, v___y_3717_, v___x_3732_, v___x_3735_);
lean_inc(v___y_3718_);
v___x_3737_ = l_Lean_Syntax_node4(v___y_3729_, v___y_3718_, v___y_3710_, v___y_3719_, v___y_3712_, v___x_3736_);
v___x_3738_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3724_, v___x_3737_, v___y_3728_, v___y_3714_, v___y_3723_, v___y_3726_, v___y_3720_, v___y_3711_, v___y_3722_, v___y_3709_);
return v___x_3738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4031_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4032_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4034_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4035_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4031_, v___x_4032_, v___x_4033_, v___x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4037_;
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
