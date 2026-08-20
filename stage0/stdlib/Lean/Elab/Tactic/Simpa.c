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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* v___f_253_; lean_object* v___x_62074__overap_254_; lean_object* v___x_255_; 
v___f_253_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0));
v___x_62074__overap_254_ = lean_panic_fn_borrowed(v___f_253_, v_msg_243_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
v___x_255_ = lean_apply_9(v___x_62074__overap_254_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, lean_box(0));
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
uint8_t v___x_75018__boxed_587_; uint8_t v___x_75019__boxed_588_; uint8_t v_useReducible_boxed_589_; uint8_t v___x_75023__boxed_590_; lean_object* v_res_591_; 
v___x_75018__boxed_587_ = lean_unbox(v___x_570_);
v___x_75019__boxed_588_ = lean_unbox(v___x_571_);
v_useReducible_boxed_589_ = lean_unbox(v_useReducible_576_);
v___x_75023__boxed_590_ = lean_unbox(v___x_577_);
v_res_591_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_568_, v_a_569_, v___x_75018__boxed_587_, v___x_75019__boxed_588_, v_a_572_, v_mvarCounter_573_, v___x_574_, v___x_575_, v_useReducible_boxed_589_, v___x_75023__boxed_590_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
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
lean_object* v_ks_1191_; lean_object* v_vs_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1210_; 
v_ks_1191_ = lean_ctor_get(v_x_1140_, 0);
v_vs_1192_ = lean_ctor_get(v_x_1140_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1194_ = v_x_1140_;
v_isShared_1195_ = v_isSharedCheck_1210_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_vs_1192_);
lean_inc(v_ks_1191_);
lean_dec(v_x_1140_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1210_;
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
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_ks_1191_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_vs_1192_);
v___x_1197_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v_newNode_1198_; size_t v___x_1199_; uint8_t v___x_1200_; 
v_newNode_1198_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v___x_1197_, v_x_1143_, v_x_1144_);
v___x_1199_ = ((size_t)7ULL);
v___x_1200_ = lean_usize_dec_le(v___x_1199_, v_x_1142_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1198_);
v___x_1202_ = lean_unsigned_to_nat(4u);
v___x_1203_ = lean_nat_dec_lt(v___x_1201_, v___x_1202_);
lean_dec(v___x_1201_);
if (v___x_1203_ == 0)
{
lean_object* v_ks_1204_; lean_object* v_vs_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_ks_1204_ = lean_ctor_get(v_newNode_1198_, 0);
lean_inc_ref(v_ks_1204_);
v_vs_1205_ = lean_ctor_get(v_newNode_1198_, 1);
lean_inc_ref(v_vs_1205_);
lean_dec_ref(v_newNode_1198_);
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0);
v___x_1208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_x_1142_, v_ks_1204_, v_vs_1205_, v___x_1206_, v___x_1207_);
lean_dec_ref(v_vs_1205_);
lean_dec_ref(v_ks_1204_);
return v___x_1208_;
}
else
{
return v_newNode_1198_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(size_t v_depth_1211_, lean_object* v_keys_1212_, lean_object* v_vals_1213_, lean_object* v_i_1214_, lean_object* v_entries_1215_){
_start:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_array_get_size(v_keys_1212_);
v___x_1217_ = lean_nat_dec_lt(v_i_1214_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec(v_i_1214_);
return v_entries_1215_;
}
else
{
lean_object* v_k_1218_; lean_object* v_v_1219_; uint64_t v___x_1220_; size_t v_h_1221_; size_t v___x_1222_; lean_object* v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; size_t v_h_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_k_1218_ = lean_array_fget_borrowed(v_keys_1212_, v_i_1214_);
v_v_1219_ = lean_array_fget_borrowed(v_vals_1213_, v_i_1214_);
v___x_1220_ = l_Lean_instHashableMVarId_hash(v_k_1218_);
v_h_1221_ = lean_uint64_to_usize(v___x_1220_);
v___x_1222_ = ((size_t)5ULL);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_sub(v_depth_1211_, v___x_1224_);
v___x_1226_ = lean_usize_mul(v___x_1222_, v___x_1225_);
v_h_1227_ = lean_usize_shift_right(v_h_1221_, v___x_1226_);
v___x_1228_ = lean_nat_add(v_i_1214_, v___x_1223_);
lean_dec(v_i_1214_);
lean_inc(v_v_1219_);
lean_inc(v_k_1218_);
v___x_1229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_entries_1215_, v_h_1227_, v_depth_1211_, v_k_1218_, v_v_1219_);
v_i_1214_ = v___x_1228_;
v_entries_1215_ = v___x_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg___boxed(lean_object* v_depth_1231_, lean_object* v_keys_1232_, lean_object* v_vals_1233_, lean_object* v_i_1234_, lean_object* v_entries_1235_){
_start:
{
size_t v_depth_boxed_1236_; lean_object* v_res_1237_; 
v_depth_boxed_1236_ = lean_unbox_usize(v_depth_1231_);
lean_dec(v_depth_1231_);
v_res_1237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_1236_, v_keys_1232_, v_vals_1233_, v_i_1234_, v_entries_1235_);
lean_dec_ref(v_vals_1233_);
lean_dec_ref(v_keys_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
size_t v_x_76294__boxed_1243_; size_t v_x_76295__boxed_1244_; lean_object* v_res_1245_; 
v_x_76294__boxed_1243_ = lean_unbox_usize(v_x_1239_);
lean_dec(v_x_1239_);
v_x_76295__boxed_1244_ = lean_unbox_usize(v_x_1240_);
lean_dec(v_x_1240_);
v_res_1245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1238_, v_x_76294__boxed_1243_, v_x_76295__boxed_1244_, v_x_1241_, v_x_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint64_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = l_Lean_instHashableMVarId_hash(v_x_1247_);
v___x_1250_ = lean_uint64_to_usize(v___x_1249_);
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_1246_, v___x_1250_, v___x_1251_, v_x_1247_, v_x_1248_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_1253_, lean_object* v_val_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_mctx_1258_; lean_object* v_cache_1259_; lean_object* v_zetaDeltaFVarIds_1260_; lean_object* v_postponed_1261_; lean_object* v_diag_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1291_; 
v___x_1257_ = lean_st_ref_take(v___y_1255_);
v_mctx_1258_ = lean_ctor_get(v___x_1257_, 0);
v_cache_1259_ = lean_ctor_get(v___x_1257_, 1);
v_zetaDeltaFVarIds_1260_ = lean_ctor_get(v___x_1257_, 2);
v_postponed_1261_ = lean_ctor_get(v___x_1257_, 3);
v_diag_1262_ = lean_ctor_get(v___x_1257_, 4);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1264_ = v___x_1257_;
v_isShared_1265_ = v_isSharedCheck_1291_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_diag_1262_);
lean_inc(v_postponed_1261_);
lean_inc(v_zetaDeltaFVarIds_1260_);
lean_inc(v_cache_1259_);
lean_inc(v_mctx_1258_);
lean_dec(v___x_1257_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1291_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_depth_1266_; lean_object* v_levelAssignDepth_1267_; lean_object* v_lmvarCounter_1268_; lean_object* v_mvarCounter_1269_; lean_object* v_lDecls_1270_; lean_object* v_decls_1271_; lean_object* v_userNames_1272_; lean_object* v_lAssignment_1273_; lean_object* v_eAssignment_1274_; lean_object* v_dAssignment_1275_; lean_object* v_instanceTypedMVars_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1290_; 
v_depth_1266_ = lean_ctor_get(v_mctx_1258_, 0);
v_levelAssignDepth_1267_ = lean_ctor_get(v_mctx_1258_, 1);
v_lmvarCounter_1268_ = lean_ctor_get(v_mctx_1258_, 2);
v_mvarCounter_1269_ = lean_ctor_get(v_mctx_1258_, 3);
v_lDecls_1270_ = lean_ctor_get(v_mctx_1258_, 4);
v_decls_1271_ = lean_ctor_get(v_mctx_1258_, 5);
v_userNames_1272_ = lean_ctor_get(v_mctx_1258_, 6);
v_lAssignment_1273_ = lean_ctor_get(v_mctx_1258_, 7);
v_eAssignment_1274_ = lean_ctor_get(v_mctx_1258_, 8);
v_dAssignment_1275_ = lean_ctor_get(v_mctx_1258_, 9);
v_instanceTypedMVars_1276_ = lean_ctor_get(v_mctx_1258_, 10);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_mctx_1258_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1278_ = v_mctx_1258_;
v_isShared_1279_ = v_isSharedCheck_1290_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_instanceTypedMVars_1276_);
lean_inc(v_dAssignment_1275_);
lean_inc(v_eAssignment_1274_);
lean_inc(v_lAssignment_1273_);
lean_inc(v_userNames_1272_);
lean_inc(v_decls_1271_);
lean_inc(v_lDecls_1270_);
lean_inc(v_mvarCounter_1269_);
lean_inc(v_lmvarCounter_1268_);
lean_inc(v_levelAssignDepth_1267_);
lean_inc(v_depth_1266_);
lean_dec(v_mctx_1258_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1290_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_1274_, v_mvarId_1253_, v_val_1254_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 8, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_depth_1266_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_levelAssignDepth_1267_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_lmvarCounter_1268_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_mvarCounter_1269_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_lDecls_1270_);
lean_ctor_set(v_reuseFailAlloc_1289_, 5, v_decls_1271_);
lean_ctor_set(v_reuseFailAlloc_1289_, 6, v_userNames_1272_);
lean_ctor_set(v_reuseFailAlloc_1289_, 7, v_lAssignment_1273_);
lean_ctor_set(v_reuseFailAlloc_1289_, 8, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1289_, 9, v_dAssignment_1275_);
lean_ctor_set(v_reuseFailAlloc_1289_, 10, v_instanceTypedMVars_1276_);
v___x_1282_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1284_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1282_);
v___x_1284_ = v___x_1264_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_cache_1259_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_zetaDeltaFVarIds_1260_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_postponed_1261_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v_diag_1262_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_st_ref_put(v___y_1255_, v___x_1284_);
v___x_1286_ = lean_box(0);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_1292_, lean_object* v_val_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_1292_, v_val_1293_, v___y_1294_);
lean_dec(v___y_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(uint8_t v_suppressElabErrors_1305_, uint8_t v___y_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 1)
{
lean_object* v_pre_1308_; 
v_pre_1308_ = lean_ctor_get(v_x_1307_, 0);
switch(lean_obj_tag(v_pre_1308_))
{
case 1:
{
lean_object* v_pre_1309_; 
v_pre_1309_ = lean_ctor_get(v_pre_1308_, 0);
switch(lean_obj_tag(v_pre_1309_))
{
case 0:
{
lean_object* v_str_1310_; lean_object* v_str_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_str_1310_ = lean_ctor_get(v_x_1307_, 1);
v_str_1311_ = lean_ctor_get(v_pre_1308_, 1);
v___x_1312_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0));
v___x_1313_ = lean_string_dec_eq(v_str_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_1315_ = lean_string_dec_eq(v_str_1311_, v___x_1314_);
if (v___x_1315_ == 0)
{
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2));
v___x_1317_ = lean_string_dec_eq(v_str_1310_, v___x_1316_);
if (v___x_1317_ == 0)
{
return v___x_1317_;
}
else
{
return v_suppressElabErrors_1305_;
}
}
}
else
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3));
v___x_1319_ = lean_string_dec_eq(v_str_1310_, v___x_1318_);
if (v___x_1319_ == 0)
{
return v___x_1319_;
}
else
{
return v_suppressElabErrors_1305_;
}
}
}
case 1:
{
lean_object* v_pre_1320_; 
v_pre_1320_ = lean_ctor_get(v_pre_1309_, 0);
if (lean_obj_tag(v_pre_1320_) == 0)
{
lean_object* v_str_1321_; lean_object* v_str_1322_; lean_object* v_str_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_str_1321_ = lean_ctor_get(v_x_1307_, 1);
v_str_1322_ = lean_ctor_get(v_pre_1308_, 1);
v_str_1323_ = lean_ctor_get(v_pre_1309_, 1);
v___x_1324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4));
v___x_1325_ = lean_string_dec_eq(v_str_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5));
v___x_1327_ = lean_string_dec_eq(v_str_1322_, v___x_1326_);
if (v___x_1327_ == 0)
{
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6));
v___x_1329_ = lean_string_dec_eq(v_str_1321_, v___x_1328_);
if (v___x_1329_ == 0)
{
return v___x_1329_;
}
else
{
return v_suppressElabErrors_1305_;
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
lean_object* v_str_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_str_1330_ = lean_ctor_get(v_x_1307_, 1);
v___x_1331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7));
v___x_1332_ = lean_string_dec_eq(v_str_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
return v___x_1332_;
}
else
{
return v_suppressElabErrors_1305_;
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1333_, lean_object* v___y_1334_, lean_object* v_x_1335_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1336_; uint8_t v___y_76519__boxed_1337_; uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_suppressElabErrors_boxed_1336_ = lean_unbox(v_suppressElabErrors_1333_);
v___y_76519__boxed_1337_ = lean_unbox(v___y_1334_);
v_res_1338_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v_suppressElabErrors_boxed_1336_, v___y_76519__boxed_1337_, v_x_1335_);
lean_dec(v_x_1335_);
v_r_1339_ = lean_box(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(lean_object* v_ref_1341_, lean_object* v_msgData_1342_, uint8_t v_severity_1343_, uint8_t v_isSilent_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; uint8_t v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1412_; uint8_t v___y_1413_; lean_object* v___y_1414_; uint8_t v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1423_; uint8_t v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; uint8_t v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; uint8_t v___x_1434_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; uint8_t v___y_1441_; uint8_t v___y_1442_; uint8_t v___y_1444_; uint8_t v___x_1459_; 
v___x_1434_ = 2;
v___x_1459_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1343_, v___x_1434_);
if (v___x_1459_ == 0)
{
v___y_1444_ = v___x_1459_;
goto v___jp_1443_;
}
else
{
uint8_t v___x_1460_; 
lean_inc_ref(v_msgData_1342_);
v___x_1460_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1342_);
v___y_1444_ = v___x_1460_;
goto v___jp_1443_;
}
v___jp_1350_:
{
lean_object* v___x_1360_; lean_object* v_currNamespace_1361_; lean_object* v_openDecls_1362_; lean_object* v_env_1363_; lean_object* v_nextMacroScope_1364_; lean_object* v_ngen_1365_; lean_object* v_auxDeclNGen_1366_; lean_object* v_traceState_1367_; lean_object* v_cache_1368_; lean_object* v_messages_1369_; lean_object* v_infoState_1370_; lean_object* v_snapshotTasks_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1385_; 
v___x_1360_ = lean_st_ref_take(v___y_1359_);
v_currNamespace_1361_ = lean_ctor_get(v___y_1358_, 6);
v_openDecls_1362_ = lean_ctor_get(v___y_1358_, 7);
v_env_1363_ = lean_ctor_get(v___x_1360_, 0);
v_nextMacroScope_1364_ = lean_ctor_get(v___x_1360_, 1);
v_ngen_1365_ = lean_ctor_get(v___x_1360_, 2);
v_auxDeclNGen_1366_ = lean_ctor_get(v___x_1360_, 3);
v_traceState_1367_ = lean_ctor_get(v___x_1360_, 4);
v_cache_1368_ = lean_ctor_get(v___x_1360_, 5);
v_messages_1369_ = lean_ctor_get(v___x_1360_, 6);
v_infoState_1370_ = lean_ctor_get(v___x_1360_, 7);
v_snapshotTasks_1371_ = lean_ctor_get(v___x_1360_, 8);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1373_ = v___x_1360_;
v_isShared_1374_ = v_isSharedCheck_1385_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snapshotTasks_1371_);
lean_inc(v_infoState_1370_);
lean_inc(v_messages_1369_);
lean_inc(v_cache_1368_);
lean_inc(v_traceState_1367_);
lean_inc(v_auxDeclNGen_1366_);
lean_inc(v_ngen_1365_);
lean_inc(v_nextMacroScope_1364_);
lean_inc(v_env_1363_);
lean_dec(v___x_1360_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1385_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_inc(v_openDecls_1362_);
lean_inc(v_currNamespace_1361_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_currNamespace_1361_);
lean_ctor_set(v___x_1375_, 1, v_openDecls_1362_);
v___x_1376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___y_1354_);
lean_inc_ref(v___y_1355_);
lean_inc_ref(v___y_1352_);
v___x_1377_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1377_, 0, v___y_1352_);
lean_ctor_set(v___x_1377_, 1, v___y_1357_);
lean_ctor_set(v___x_1377_, 2, v___y_1353_);
lean_ctor_set(v___x_1377_, 3, v___y_1355_);
lean_ctor_set(v___x_1377_, 4, v___x_1376_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*5, v___y_1351_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*5 + 1, v___y_1356_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*5 + 2, v_isSilent_1344_);
v___x_1378_ = l_Lean_MessageLog_add(v___x_1377_, v_messages_1369_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 6, v___x_1378_);
v___x_1380_ = v___x_1373_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_env_1363_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_nextMacroScope_1364_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_ngen_1365_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_auxDeclNGen_1366_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_traceState_1367_);
lean_ctor_set(v_reuseFailAlloc_1384_, 5, v_cache_1368_);
lean_ctor_set(v_reuseFailAlloc_1384_, 6, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1384_, 7, v_infoState_1370_);
lean_ctor_set(v_reuseFailAlloc_1384_, 8, v_snapshotTasks_1371_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = lean_st_ref_put(v___y_1359_, v___x_1380_);
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
}
v___jp_1386_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1410_; 
v___x_1395_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1342_);
v___x_1396_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v___x_1395_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_inc_ref_n(v___y_1391_, 2);
v___x_1401_ = l_Lean_FileMap_toPosition(v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
v___x_1402_ = l_Lean_FileMap_toPosition(v___y_1391_, v___y_1394_);
lean_dec(v___y_1394_);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
v___x_1404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0));
if (v___y_1388_ == 0)
{
lean_del_object(v___x_1399_);
lean_dec_ref(v___y_1387_);
v___y_1351_ = v___y_1390_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___x_1403_;
v___y_1354_ = v_a_1397_;
v___y_1355_ = v___x_1404_;
v___y_1356_ = v___y_1393_;
v___y_1357_ = v___x_1401_;
v___y_1358_ = v___y_1347_;
v___y_1359_ = v___y_1348_;
goto v___jp_1350_;
}
else
{
uint8_t v___x_1405_; 
lean_inc(v_a_1397_);
v___x_1405_ = l_Lean_MessageData_hasTag(v___y_1387_, v_a_1397_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_dec_ref_known(v___x_1403_, 1);
lean_dec_ref(v___x_1401_);
lean_dec(v_a_1397_);
v___x_1406_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1406_);
v___x_1408_ = v___x_1399_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
lean_del_object(v___x_1399_);
v___y_1351_ = v___y_1390_;
v___y_1352_ = v___y_1389_;
v___y_1353_ = v___x_1403_;
v___y_1354_ = v_a_1397_;
v___y_1355_ = v___x_1404_;
v___y_1356_ = v___y_1393_;
v___y_1357_ = v___x_1401_;
v___y_1358_ = v___y_1347_;
v___y_1359_ = v___y_1348_;
goto v___jp_1350_;
}
}
}
}
v___jp_1411_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Syntax_getTailPos_x3f(v___y_1417_, v___y_1415_);
lean_dec(v___y_1417_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_inc(v___y_1419_);
v___y_1387_ = v___y_1412_;
v___y_1388_ = v___y_1413_;
v___y_1389_ = v___y_1416_;
v___y_1390_ = v___y_1415_;
v___y_1391_ = v___y_1414_;
v___y_1392_ = v___y_1419_;
v___y_1393_ = v___y_1418_;
v___y_1394_ = v___y_1419_;
goto v___jp_1386_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___y_1387_ = v___y_1412_;
v___y_1388_ = v___y_1413_;
v___y_1389_ = v___y_1416_;
v___y_1390_ = v___y_1415_;
v___y_1391_ = v___y_1414_;
v___y_1392_ = v___y_1419_;
v___y_1393_ = v___y_1418_;
v___y_1394_ = v_val_1421_;
goto v___jp_1386_;
}
}
v___jp_1422_:
{
lean_object* v_ref_1430_; lean_object* v___x_1431_; 
v_ref_1430_ = l_Lean_replaceRef(v_ref_1341_, v___y_1425_);
v___x_1431_ = l_Lean_Syntax_getPos_x3f(v_ref_1430_, v___y_1427_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_unsigned_to_nat(0u);
v___y_1412_ = v___y_1423_;
v___y_1413_ = v___y_1424_;
v___y_1414_ = v___y_1428_;
v___y_1415_ = v___y_1427_;
v___y_1416_ = v___y_1426_;
v___y_1417_ = v_ref_1430_;
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___x_1432_;
goto v___jp_1411_;
}
else
{
lean_object* v_val_1433_; 
v_val_1433_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v___x_1431_, 1);
v___y_1412_ = v___y_1423_;
v___y_1413_ = v___y_1424_;
v___y_1414_ = v___y_1428_;
v___y_1415_ = v___y_1427_;
v___y_1416_ = v___y_1426_;
v___y_1417_ = v_ref_1430_;
v___y_1418_ = v___y_1429_;
v___y_1419_ = v_val_1433_;
goto v___jp_1411_;
}
}
v___jp_1435_:
{
if (v___y_1442_ == 0)
{
v___y_1423_ = v___y_1436_;
v___y_1424_ = v___y_1438_;
v___y_1425_ = v___y_1437_;
v___y_1426_ = v___y_1440_;
v___y_1427_ = v___y_1441_;
v___y_1428_ = v___y_1439_;
v___y_1429_ = v_severity_1343_;
goto v___jp_1422_;
}
else
{
v___y_1423_ = v___y_1436_;
v___y_1424_ = v___y_1438_;
v___y_1425_ = v___y_1437_;
v___y_1426_ = v___y_1440_;
v___y_1427_ = v___y_1441_;
v___y_1428_ = v___y_1439_;
v___y_1429_ = v___x_1434_;
goto v___jp_1422_;
}
}
v___jp_1443_:
{
if (v___y_1444_ == 0)
{
lean_object* v_fileName_1445_; lean_object* v_fileMap_1446_; lean_object* v_options_1447_; lean_object* v_ref_1448_; uint8_t v_suppressElabErrors_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___f_1452_; uint8_t v___x_1453_; uint8_t v___x_1454_; 
v_fileName_1445_ = lean_ctor_get(v___y_1347_, 0);
v_fileMap_1446_ = lean_ctor_get(v___y_1347_, 1);
v_options_1447_ = lean_ctor_get(v___y_1347_, 2);
v_ref_1448_ = lean_ctor_get(v___y_1347_, 5);
v_suppressElabErrors_1449_ = lean_ctor_get_uint8(v___y_1347_, sizeof(void*)*14 + 1);
v___x_1450_ = lean_box(v_suppressElabErrors_1449_);
v___x_1451_ = lean_box(v___y_1444_);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1452_, 0, v___x_1450_);
lean_closure_set(v___f_1452_, 1, v___x_1451_);
v___x_1453_ = 1;
v___x_1454_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1343_, v___x_1453_);
if (v___x_1454_ == 0)
{
v___y_1436_ = v___f_1452_;
v___y_1437_ = v_ref_1448_;
v___y_1438_ = v_suppressElabErrors_1449_;
v___y_1439_ = v_fileMap_1446_;
v___y_1440_ = v_fileName_1445_;
v___y_1441_ = v___y_1444_;
v___y_1442_ = v___x_1454_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = l_Lean_warningAsError;
v___x_1456_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_1447_, v___x_1455_);
v___y_1436_ = v___f_1452_;
v___y_1437_ = v_ref_1448_;
v___y_1438_ = v_suppressElabErrors_1449_;
v___y_1439_ = v_fileMap_1446_;
v___y_1440_ = v_fileName_1445_;
v___y_1441_ = v___y_1444_;
v___y_1442_ = v___x_1456_;
goto v___jp_1435_;
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v_msgData_1342_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___boxed(lean_object* v_ref_1461_, lean_object* v_msgData_1462_, lean_object* v_severity_1463_, lean_object* v_isSilent_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v_severity_boxed_1470_; uint8_t v_isSilent_boxed_1471_; lean_object* v_res_1472_; 
v_severity_boxed_1470_ = lean_unbox(v_severity_1463_);
v_isSilent_boxed_1471_ = lean_unbox(v_isSilent_1464_);
v_res_1472_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1461_, v_msgData_1462_, v_severity_boxed_1470_, v_isSilent_boxed_1471_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v_ref_1461_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(lean_object* v_ref_1473_, lean_object* v_msgData_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = 1;
v___x_1485_ = 0;
v___x_1486_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_1473_, v_msgData_1474_, v___x_1484_, v___x_1485_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(lean_object* v_ref_1487_, lean_object* v_msgData_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_ref_1487_, v_msgData_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v_ref_1487_);
return v_res_1498_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_linterOption_1505_, lean_object* v_stx_1506_, lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_name_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1535_; 
v_name_1517_ = lean_ctor_get(v_linterOption_1505_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_linterOption_1505_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v_linterOption_1505_, 1);
lean_dec(v_unused_1536_);
v___x_1519_ = v_linterOption_1505_;
v_isShared_1520_ = v_isSharedCheck_1535_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_name_1517_);
lean_dec(v_linterOption_1505_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1535_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1521_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
lean_inc(v_name_1517_);
v___x_1522_ = l_Lean_MessageData_ofName(v_name_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 7);
lean_ctor_set(v___x_1519_, 1, v___x_1522_);
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1524_ = v___x_1519_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_disable_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1525_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v_disable_1527_ = l_Lean_MessageData_note(v___x_1526_);
v___x_1528_ = l_Lean_Linter_linterMessageTag;
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_msg_1507_);
lean_ctor_set(v___x_1529_, 1, v_disable_1527_);
v___x_1530_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_name_1517_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
lean_inc(v_stx_1506_);
v___x_1532_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_stx_1506_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_stx_1506_, v___x_1532_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v_stx_1506_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_linterOption_1537_, lean_object* v_stx_1538_, lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_linterOption_1537_, v_stx_1538_, v_msg_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(lean_object* v___y_1550_, lean_object* v_mkInfoTree_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v_a_1559_, lean_object* v_a_x3f_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v_infoState_1563_; lean_object* v_trees_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_st_ref_get(v___y_1550_);
v_infoState_1563_ = lean_ctor_get(v___x_1562_, 7);
lean_inc_ref(v_infoState_1563_);
lean_dec(v___x_1562_);
v_trees_1564_ = lean_ctor_get(v_infoState_1563_, 2);
lean_inc_ref(v_trees_1564_);
lean_dec_ref(v_infoState_1563_);
lean_inc(v___y_1550_);
lean_inc_ref(v___y_1558_);
lean_inc(v___y_1557_);
lean_inc_ref(v___y_1556_);
lean_inc(v___y_1555_);
lean_inc_ref(v___y_1554_);
lean_inc(v___y_1553_);
lean_inc_ref(v___y_1552_);
v___x_1565_ = lean_apply_10(v_mkInfoTree_1551_, v_trees_1564_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1550_, lean_box(0));
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1604_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1604_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1604_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v_infoState_1571_; lean_object* v_env_1572_; lean_object* v_nextMacroScope_1573_; lean_object* v_ngen_1574_; lean_object* v_auxDeclNGen_1575_; lean_object* v_traceState_1576_; lean_object* v_cache_1577_; lean_object* v_messages_1578_; lean_object* v_snapshotTasks_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1603_; 
v___x_1570_ = lean_st_ref_take(v___y_1550_);
v_infoState_1571_ = lean_ctor_get(v___x_1570_, 7);
v_env_1572_ = lean_ctor_get(v___x_1570_, 0);
v_nextMacroScope_1573_ = lean_ctor_get(v___x_1570_, 1);
v_ngen_1574_ = lean_ctor_get(v___x_1570_, 2);
v_auxDeclNGen_1575_ = lean_ctor_get(v___x_1570_, 3);
v_traceState_1576_ = lean_ctor_get(v___x_1570_, 4);
v_cache_1577_ = lean_ctor_get(v___x_1570_, 5);
v_messages_1578_ = lean_ctor_get(v___x_1570_, 6);
v_snapshotTasks_1579_ = lean_ctor_get(v___x_1570_, 8);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1581_ = v___x_1570_;
v_isShared_1582_ = v_isSharedCheck_1603_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_snapshotTasks_1579_);
lean_inc(v_infoState_1571_);
lean_inc(v_messages_1578_);
lean_inc(v_cache_1577_);
lean_inc(v_traceState_1576_);
lean_inc(v_auxDeclNGen_1575_);
lean_inc(v_ngen_1574_);
lean_inc(v_nextMacroScope_1573_);
lean_inc(v_env_1572_);
lean_dec(v___x_1570_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1603_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
uint8_t v_enabled_1583_; lean_object* v_assignment_1584_; lean_object* v_lazyAssignment_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1601_; 
v_enabled_1583_ = lean_ctor_get_uint8(v_infoState_1571_, sizeof(void*)*3);
v_assignment_1584_ = lean_ctor_get(v_infoState_1571_, 0);
v_lazyAssignment_1585_ = lean_ctor_get(v_infoState_1571_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_infoState_1571_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v_infoState_1571_, 2);
lean_dec(v_unused_1602_);
v___x_1587_ = v_infoState_1571_;
v_isShared_1588_ = v_isSharedCheck_1601_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_lazyAssignment_1585_);
lean_inc(v_assignment_1584_);
lean_dec(v_infoState_1571_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1601_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = l_Lean_PersistentArray_push___redArg(v_a_1559_, v_a_1566_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 2, v___x_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_assignment_1584_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_lazyAssignment_1585_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v___x_1589_);
lean_ctor_set_uint8(v_reuseFailAlloc_1600_, sizeof(void*)*3, v_enabled_1583_);
v___x_1591_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 7, v___x_1591_);
v___x_1593_ = v___x_1581_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_env_1572_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_nextMacroScope_1573_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_ngen_1574_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_auxDeclNGen_1575_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_traceState_1576_);
lean_ctor_set(v_reuseFailAlloc_1599_, 5, v_cache_1577_);
lean_ctor_set(v_reuseFailAlloc_1599_, 6, v_messages_1578_);
lean_ctor_set(v_reuseFailAlloc_1599_, 7, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1599_, 8, v_snapshotTasks_1579_);
v___x_1593_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = lean_st_ref_put(v___y_1550_, v___x_1593_);
v___x_1595_ = lean_box(0);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1595_);
v___x_1597_ = v___x_1568_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref(v_a_1559_);
v_a_1605_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1565_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1565_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(lean_object* v___y_1613_, lean_object* v_mkInfoTree_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v_a_1622_, lean_object* v_a_x3f_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1613_, v_mkInfoTree_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v_a_1622_, v_a_x3f_1623_);
lean_dec(v_a_x3f_1623_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1613_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(lean_object* v_x_1626_, lean_object* v_mkInfoTree_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; lean_object* v_infoState_1638_; uint8_t v_enabled_1639_; 
v___x_1637_ = lean_st_ref_get(v___y_1635_);
v_infoState_1638_ = lean_ctor_get(v___x_1637_, 7);
lean_inc_ref(v_infoState_1638_);
lean_dec(v___x_1637_);
v_enabled_1639_ = lean_ctor_get_uint8(v_infoState_1638_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1638_);
if (v_enabled_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_dec_ref(v_mkInfoTree_1627_);
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
v___x_1640_ = lean_apply_9(v_x_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, lean_box(0));
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v_a_1642_; lean_object* v_r_1643_; 
v___x_1641_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1635_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
v_r_1643_ = lean_apply_9(v_x_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, lean_box(0));
if (lean_obj_tag(v_r_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1668_; 
v_a_1644_ = lean_ctor_get(v_r_1643_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_r_1643_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1646_ = v_r_1643_;
v_isShared_1647_ = v_isSharedCheck_1668_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v_r_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1668_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
lean_inc(v_a_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 1);
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1635_, v_mkInfoTree_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v_a_1642_, v___x_1649_);
lean_dec_ref(v___x_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v___x_1650_, 0);
lean_dec(v_unused_1658_);
v___x_1652_ = v___x_1650_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v___x_1650_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v_a_1644_);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1644_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_a_1644_);
v_a_1659_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1650_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1650_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_a_1669_ = lean_ctor_get(v_r_1643_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v_r_1643_, 1);
v___x_1670_ = lean_box(0);
v___x_1671_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_1635_, v_mkInfoTree_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v_a_1642_, v___x_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v___x_1671_, 0);
lean_dec(v_unused_1679_);
v___x_1673_ = v___x_1671_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_dec(v___x_1671_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 1);
lean_ctor_set(v___x_1673_, 0, v_a_1669_);
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1669_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_a_1669_);
v_a_1680_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1671_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1671_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(lean_object* v_x_1688_, lean_object* v_mkInfoTree_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_1688_, v_mkInfoTree_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; lean_object* v_env_1704_; lean_object* v___x_1705_; lean_object* v_toEnvExtension_1706_; lean_object* v_asyncMode_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_merged_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v___x_1703_ = lean_st_ref_get(v___y_1701_);
v_env_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc_ref(v_env_1704_);
lean_dec(v___x_1703_);
v___x_1705_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1706_ = lean_ctor_get(v___x_1705_, 0);
v_asyncMode_1707_ = lean_ctor_get(v_toEnvExtension_1706_, 2);
v___x_1708_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1709_ = lean_box(0);
v___x_1710_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1708_, v___x_1705_, v_env_1704_, v_asyncMode_1707_, v___x_1709_);
v_merged_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v___x_1710_, 1);
lean_dec(v_unused_1720_);
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_merged_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v_merged_1711_);
lean_ctor_set(v___x_1713_, 0, v_o_1700_);
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_o_1700_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_merged_1711_);
v___x_1716_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_1721_, v___y_1722_);
lean_dec(v___y_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_options_1734_; lean_object* v___x_1735_; 
v_options_1734_ = lean_ctor_get(v___y_1731_, 2);
lean_inc_ref(v_options_1734_);
v___x_1735_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_1734_, v___y_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1745_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2));
v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
return v___x_1751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4));
v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6));
v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
return v___x_1757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8));
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10));
v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_usingArg_1767_, lean_object* v_snd_1768_, uint8_t v___x_1769_, uint8_t v___x_1770_, lean_object* v___x_1771_, uint8_t v_useReducible_1772_, uint8_t v___x_1773_, lean_object* v___x_1774_, lean_object* v___x_1775_, lean_object* v_simprocs_1776_, lean_object* v_discharge_x3f_1777_, lean_object* v_snd_1778_, lean_object* v___x_1779_, lean_object* v___f_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; 
if (lean_obj_tag(v_usingArg_1767_) == 1)
{
lean_object* v_val_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___x_2023_; lean_object* v_infoState_2024_; uint8_t v_enabled_2025_; 
v_val_1971_ = lean_ctor_get(v_usingArg_1767_, 0);
lean_inc(v_val_1971_);
lean_dec_ref_known(v_usingArg_1767_, 1);
v___x_2023_ = lean_st_ref_get(v___y_1788_);
v_infoState_2024_ = lean_ctor_get(v___x_2023_, 7);
lean_inc_ref(v_infoState_2024_);
lean_dec(v___x_2023_);
v_enabled_2025_ = lean_ctor_get_uint8(v_infoState_2024_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2024_);
if (v_enabled_2025_ == 0)
{
lean_dec_ref(v___f_1780_);
v___y_1973_ = v___y_1781_;
v___y_1974_ = v___y_1782_;
v___y_1975_ = v___y_1783_;
v___y_1976_ = v___y_1784_;
v___y_1977_ = v___y_1785_;
v___y_1978_ = v___y_1786_;
v___y_1979_ = v___y_1787_;
v___y_1980_ = v___y_1788_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_2026_; lean_object* v_a_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; 
v___x_2026_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_1788_);
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v___f_2028_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 10, 1);
lean_closure_set(v___f_2028_, 0, v_a_2027_);
v___x_2029_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_2028_, v___f_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref_known(v___x_2029_, 1);
v___y_1973_ = v___y_1781_;
v___y_1974_ = v___y_1782_;
v___y_1975_ = v___y_1783_;
v___y_1976_ = v___y_1784_;
v___y_1977_ = v___y_1785_;
v___y_1978_ = v___y_1786_;
v___y_1979_ = v___y_1787_;
v___y_1980_ = v___y_1788_;
goto v___jp_1972_;
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_val_1971_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
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
}
v___jp_1972_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_st_ref_get(v___y_1978_);
v___x_1982_ = lean_box(0);
v___x_1983_ = l_Lean_Elab_Tactic_elabTerm(v_val_1971_, v___x_1982_, v___x_1769_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1985_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc_n(v_a_1984_, 2);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_1768_, v_a_1984_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_mctx_1986_; lean_object* v_a_1987_; uint8_t v___x_1988_; 
v_mctx_1986_ = lean_ctor_get(v___x_1981_, 0);
lean_inc_ref(v_mctx_1986_);
lean_dec(v___x_1981_);
v_a_1987_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1988_ = lean_unbox(v_a_1987_);
lean_dec(v_a_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v_mctx_1986_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
v___x_1989_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
v___x_1990_ = l_Lean_indentExpr(v_a_1984_);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_Expr_mvar___override(v_snd_1768_);
v___x_1995_ = l_Lean_MessageData_ofExpr(v___x_1994_);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1993_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_1996_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
else
{
lean_object* v_mvarCounter_2006_; 
v_mvarCounter_2006_ = lean_ctor_get(v_mctx_1986_, 3);
lean_inc(v_mvarCounter_2006_);
lean_dec_ref(v_mctx_1986_);
lean_inc(v_a_1984_);
v___y_1855_ = v_mvarCounter_2006_;
v___y_1856_ = v___x_1982_;
v___y_1857_ = v_a_1984_;
v___y_1858_ = v___x_1982_;
v___y_1859_ = v_a_1984_;
v___y_1860_ = v___y_1973_;
v___y_1861_ = v___y_1974_;
v___y_1862_ = v___y_1975_;
v___y_1863_ = v___y_1976_;
v___y_1864_ = v___y_1977_;
v___y_1865_ = v___y_1978_;
v___y_1866_ = v___y_1979_;
v___y_1867_ = v___y_1980_;
goto v___jp_1854_;
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_a_1984_);
lean_dec(v___x_1981_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_2007_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1985_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1985_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v___x_1981_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_2015_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1983_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1983_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
else
{
lean_object* v_lctx_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v___f_1780_);
lean_dec_ref(v___x_1771_);
lean_dec(v_usingArg_1767_);
v_lctx_2038_ = lean_ctor_get(v___y_1785_, 2);
v___x_2039_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13));
v___x_2040_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2038_, v___x_2039_);
if (lean_obj_tag(v___x_2040_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_val_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_val_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = l_Lean_LocalDecl_fvarId(v_val_2041_);
lean_dec(v_val_2041_);
v___x_2043_ = lean_mk_empty_array_with_capacity(v___x_1774_);
v___x_2044_ = lean_array_push(v___x_2043_, v___x_2042_);
lean_inc_ref(v_snd_1778_);
v___x_2045_ = l_Lean_Meta_simpGoal(v_snd_1768_, v___x_1775_, v_simprocs_1776_, v_discharge_x3f_1777_, v___x_1770_, v___x_2044_, v_snd_1778_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2074_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2074_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2074_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_fst_2050_; 
v_fst_2050_ = lean_ctor_get(v_a_2046_, 0);
if (lean_obj_tag(v_fst_2050_) == 1)
{
lean_object* v_val_2051_; lean_object* v_snd_2052_; lean_object* v_snd_2053_; lean_object* v___x_2054_; 
lean_del_object(v___x_2048_);
lean_dec_ref(v_snd_1778_);
v_val_2051_ = lean_ctor_get(v_fst_2050_, 0);
lean_inc(v_val_2051_);
v_snd_2052_ = lean_ctor_get(v_a_2046_, 1);
lean_inc(v_snd_2052_);
lean_dec(v_a_2046_);
v_snd_2053_ = lean_ctor_get(v_val_2051_, 1);
lean_inc(v_snd_2053_);
lean_dec(v_val_2051_);
v___x_2054_ = l_Lean_MVarId_assumption(v_snd_2053_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2062_);
v___x_2056_ = v___x_2054_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v___x_2054_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v_snd_2052_);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_snd_2052_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_snd_2052_);
v_a_2063_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2054_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2054_);
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
else
{
lean_object* v___x_2072_; 
lean_dec(v_a_2046_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v_snd_1778_);
v___x_2072_ = v___x_2048_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_snd_1778_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec_ref(v_snd_1778_);
v_a_2075_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2045_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2045_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v___x_2083_; 
lean_dec(v___x_2040_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
v___x_2083_ = l_Lean_MVarId_assumption(v_snd_1768_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; 
v_unused_2091_ = lean_ctor_get(v___x_2083_, 0);
lean_dec(v_unused_2091_);
v___x_2085_ = v___x_2083_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_dec(v___x_2083_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_snd_1778_);
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_snd_1778_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_snd_1778_);
v_a_2092_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2083_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2083_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
v___jp_1790_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v___x_1794_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_1768_, v___y_1792_, v___y_1793_);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v___x_1794_, 0);
lean_dec(v_unused_1802_);
v___x_1796_ = v___x_1794_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_dec(v___x_1794_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___y_1791_);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___y_1791_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
v___jp_1803_:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Core_mkFreshUserName(v___y_1811_, v___y_1815_, v___y_1807_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc_n(v_a_1821_, 2);
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = l_Lean_MVarId_rename(v___y_1817_, v___y_1819_, v_a_1821_, v___y_1816_, v___y_1809_, v___y_1815_, v___y_1807_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc_n(v_a_1823_, 2);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = lean_box(v___x_1769_);
v___x_1825_ = lean_box(v___x_1770_);
v___x_1826_ = lean_box(v_useReducible_1772_);
v___x_1827_ = lean_box(v___x_1773_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 19, 10);
lean_closure_set(v___f_1828_, 0, v_a_1823_);
lean_closure_set(v___f_1828_, 1, v_a_1821_);
lean_closure_set(v___f_1828_, 2, v___x_1824_);
lean_closure_set(v___f_1828_, 3, v___x_1825_);
lean_closure_set(v___f_1828_, 4, v___y_1806_);
lean_closure_set(v___f_1828_, 5, v___y_1804_);
lean_closure_set(v___f_1828_, 6, v___x_1771_);
lean_closure_set(v___f_1828_, 7, v___y_1805_);
lean_closure_set(v___f_1828_, 8, v___x_1826_);
lean_closure_set(v___f_1828_, 9, v___x_1827_);
v___x_1829_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_1823_, v___f_1828_, v___y_1818_, v___y_1813_, v___y_1810_, v___y_1812_, v___y_1816_, v___y_1809_, v___y_1815_, v___y_1807_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_dec_ref_known(v___x_1829_, 1);
v___y_1791_ = v___y_1808_;
v___y_1792_ = v___y_1814_;
v___y_1793_ = v___y_1809_;
goto v___jp_1790_;
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v___y_1814_);
lean_dec_ref(v___y_1808_);
lean_dec(v_snd_1768_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1821_);
lean_dec_ref(v___y_1814_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_1838_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1822_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1822_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v___y_1819_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1814_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_1846_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1820_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1820_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
v___jp_1854_:
{
lean_object* v___x_1868_; 
lean_inc(v_snd_1768_);
v___x_1868_ = l_Lean_MVarId_getType(v_snd_1768_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
lean_inc(v_snd_1768_);
v___x_1870_ = l_Lean_MVarId_getTag(v_snd_1768_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1869_, v_a_1871_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = l_Lean_Expr_mvarId_x21(v_a_1873_);
v___x_1875_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1));
lean_inc_ref(v___y_1859_);
v___x_1876_ = l_Lean_MVarId_note(v___x_1874_, v___x_1875_, v___y_1859_, v___y_1858_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1938_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v_fst_1878_ = lean_ctor_get(v_a_1877_, 0);
v_snd_1879_ = lean_ctor_get(v_a_1877_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_a_1877_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1881_ = v_a_1877_;
v_isShared_1882_ = v_isSharedCheck_1938_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_snd_1879_);
lean_inc(v_fst_1878_);
lean_dec(v_a_1877_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1938_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_mk_empty_array_with_capacity(v___x_1774_);
lean_inc(v_fst_1878_);
v___x_1884_ = lean_array_push(v___x_1883_, v_fst_1878_);
v___x_1885_ = l_Lean_Meta_simpGoal(v_snd_1879_, v___x_1775_, v_simprocs_1776_, v_discharge_x3f_1777_, v___x_1770_, v___x_1884_, v_snd_1778_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v_fst_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v_fst_1887_ = lean_ctor_get(v_a_1886_, 0);
if (lean_obj_tag(v_fst_1887_) == 0)
{
lean_object* v_snd_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_fst_1878_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___x_1771_);
v_snd_1888_ = lean_ctor_get(v_a_1886_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v_a_1886_, 0);
lean_dec(v_unused_1922_);
v___x_1890_ = v_a_1886_;
v_isShared_1891_ = v_isSharedCheck_1921_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_snd_1888_);
lean_dec(v_a_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1921_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v_a_1893_; uint8_t v___x_1894_; 
v___x_1892_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_1893_);
lean_dec(v_a_1893_);
if (v___x_1894_ == 0)
{
lean_del_object(v___x_1890_);
lean_del_object(v___x_1881_);
lean_dec_ref(v___y_1859_);
v___y_1791_ = v_snd_1888_;
v___y_1792_ = v_a_1873_;
v___y_1793_ = v___y_1865_;
goto v___jp_1790_;
}
else
{
if (lean_obj_tag(v___y_1859_) == 1)
{
lean_object* v_fvarId_1895_; lean_object* v_lctx_1896_; lean_object* v___x_1897_; 
v_fvarId_1895_ = lean_ctor_get(v___y_1859_, 0);
v_lctx_1896_ = lean_ctor_get(v___y_1864_, 2);
lean_inc(v_fvarId_1895_);
lean_inc_ref(v_lctx_1896_);
v___x_1897_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_1896_, v_fvarId_1895_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_dec_ref_known(v___y_1859_, 1);
lean_del_object(v___x_1890_);
lean_del_object(v___x_1881_);
v___y_1791_ = v_snd_1888_;
v___y_1792_ = v_a_1873_;
v___y_1793_ = v___y_1865_;
goto v___jp_1790_;
}
else
{
lean_dec_ref_known(v___x_1897_, 1);
if (v___x_1894_ == 0)
{
lean_dec_ref_known(v___y_1859_, 1);
lean_del_object(v___x_1890_);
lean_del_object(v___x_1881_);
v___y_1791_ = v_snd_1888_;
v___y_1792_ = v_a_1873_;
v___y_1793_ = v___y_1865_;
goto v___jp_1790_;
}
else
{
lean_object* v_ref_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v_ref_1898_ = lean_ctor_get(v___y_1866_, 5);
v___x_1899_ = l_Lean_linter_unnecessarySimpa;
v___x_1900_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
v___x_1901_ = l_Lean_MessageData_ofExpr(v___y_1859_);
lean_inc_ref(v___x_1901_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 7);
lean_ctor_set(v___x_1890_, 1, v___x_1901_);
lean_ctor_set(v___x_1890_, 0, v___x_1900_);
v___x_1903_ = v___x_1890_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 7);
lean_ctor_set(v___x_1881_, 1, v___x_1904_);
lean_ctor_set(v___x_1881_, 0, v___x_1903_);
v___x_1906_ = v___x_1881_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1901_);
v___x_1908_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
lean_inc(v_ref_1898_);
v___x_1910_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_1899_, v_ref_1898_, v___x_1909_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_dec_ref_known(v___x_1910_, 1);
v___y_1791_ = v_snd_1888_;
v___y_1792_ = v_a_1873_;
v___y_1793_ = v___y_1865_;
goto v___jp_1790_;
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_snd_1888_);
lean_dec(v_a_1873_);
lean_dec(v_snd_1768_);
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
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
lean_del_object(v___x_1890_);
lean_del_object(v___x_1881_);
lean_dec_ref(v___y_1859_);
v___y_1791_ = v_snd_1888_;
v___y_1792_ = v_a_1873_;
v___y_1793_ = v___y_1865_;
goto v___jp_1790_;
}
}
}
}
else
{
lean_object* v_val_1923_; lean_object* v_snd_1924_; lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
lean_del_object(v___x_1881_);
lean_dec_ref(v___y_1859_);
v_val_1923_ = lean_ctor_get(v_fst_1887_, 0);
lean_inc(v_val_1923_);
v_snd_1924_ = lean_ctor_get(v_a_1886_, 1);
lean_inc(v_snd_1924_);
lean_dec(v_a_1886_);
v_fst_1925_ = lean_ctor_get(v_val_1923_, 0);
lean_inc(v_fst_1925_);
v_snd_1926_ = lean_ctor_get(v_val_1923_, 1);
lean_inc(v_snd_1926_);
lean_dec(v_val_1923_);
v___x_1927_ = lean_array_get_size(v_fst_1925_);
v___x_1928_ = lean_nat_dec_lt(v___x_1779_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_dec(v_fst_1925_);
v___y_1804_ = v___y_1855_;
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___y_1857_;
v___y_1807_ = v___y_1867_;
v___y_1808_ = v_snd_1924_;
v___y_1809_ = v___y_1865_;
v___y_1810_ = v___y_1862_;
v___y_1811_ = v___x_1875_;
v___y_1812_ = v___y_1863_;
v___y_1813_ = v___y_1861_;
v___y_1814_ = v_a_1873_;
v___y_1815_ = v___y_1866_;
v___y_1816_ = v___y_1864_;
v___y_1817_ = v_snd_1926_;
v___y_1818_ = v___y_1860_;
v___y_1819_ = v_fst_1878_;
goto v___jp_1803_;
}
else
{
lean_object* v___x_1929_; 
lean_dec(v_fst_1878_);
v___x_1929_ = lean_array_fget(v_fst_1925_, v___x_1779_);
lean_dec(v_fst_1925_);
v___y_1804_ = v___y_1855_;
v___y_1805_ = v___y_1856_;
v___y_1806_ = v___y_1857_;
v___y_1807_ = v___y_1867_;
v___y_1808_ = v_snd_1924_;
v___y_1809_ = v___y_1865_;
v___y_1810_ = v___y_1862_;
v___y_1811_ = v___x_1875_;
v___y_1812_ = v___y_1863_;
v___y_1813_ = v___y_1861_;
v___y_1814_ = v_a_1873_;
v___y_1815_ = v___y_1866_;
v___y_1816_ = v___y_1864_;
v___y_1817_ = v_snd_1926_;
v___y_1818_ = v___y_1860_;
v___y_1819_ = v___x_1929_;
goto v___jp_1803_;
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_del_object(v___x_1881_);
lean_dec(v_fst_1878_);
lean_dec(v_a_1873_);
lean_dec_ref(v___y_1859_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_1930_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1885_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1885_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_a_1873_);
lean_dec_ref(v___y_1859_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_1939_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1876_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1876_);
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
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_1947_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1872_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1872_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_a_1869_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_1955_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1870_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1870_);
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
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v_snd_1778_);
lean_dec(v_discharge_x3f_1777_);
lean_dec_ref(v_simprocs_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1768_);
v_a_1963_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1868_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1868_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object** _args){
lean_object* v_usingArg_2100_ = _args[0];
lean_object* v_snd_2101_ = _args[1];
lean_object* v___x_2102_ = _args[2];
lean_object* v___x_2103_ = _args[3];
lean_object* v___x_2104_ = _args[4];
lean_object* v_useReducible_2105_ = _args[5];
lean_object* v___x_2106_ = _args[6];
lean_object* v___x_2107_ = _args[7];
lean_object* v___x_2108_ = _args[8];
lean_object* v_simprocs_2109_ = _args[9];
lean_object* v_discharge_x3f_2110_ = _args[10];
lean_object* v_snd_2111_ = _args[11];
lean_object* v___x_2112_ = _args[12];
lean_object* v___f_2113_ = _args[13];
lean_object* v___y_2114_ = _args[14];
lean_object* v___y_2115_ = _args[15];
lean_object* v___y_2116_ = _args[16];
lean_object* v___y_2117_ = _args[17];
lean_object* v___y_2118_ = _args[18];
lean_object* v___y_2119_ = _args[19];
lean_object* v___y_2120_ = _args[20];
lean_object* v___y_2121_ = _args[21];
lean_object* v___y_2122_ = _args[22];
_start:
{
uint8_t v___x_77254__boxed_2123_; uint8_t v___x_77255__boxed_2124_; uint8_t v_useReducible_boxed_2125_; uint8_t v___x_77257__boxed_2126_; lean_object* v_res_2127_; 
v___x_77254__boxed_2123_ = lean_unbox(v___x_2102_);
v___x_77255__boxed_2124_ = lean_unbox(v___x_2103_);
v_useReducible_boxed_2125_ = lean_unbox(v_useReducible_2105_);
v___x_77257__boxed_2126_ = lean_unbox(v___x_2106_);
v_res_2127_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_usingArg_2100_, v_snd_2101_, v___x_77254__boxed_2123_, v___x_77255__boxed_2124_, v___x_2104_, v_useReducible_boxed_2125_, v___x_77257__boxed_2126_, v___x_2107_, v___x_2108_, v_simprocs_2109_, v_discharge_x3f_2110_, v_snd_2111_, v___x_2112_, v___f_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___x_2112_);
lean_dec(v___x_2107_);
return v_res_2127_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0(void){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2128_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = lean_unsigned_to_nat(32u);
v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2138_ = l_Lean_MessageData_ofFormat(v___x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v___x_2139_, lean_object* v_tk_2140_, lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v_simprocs_2144_, uint8_t v___x_2145_, lean_object* v_usingArg_2146_, uint8_t v___x_2147_, lean_object* v___x_2148_, uint8_t v_useReducible_2149_, uint8_t v___x_2150_, lean_object* v___x_2151_, lean_object* v_usingTk_x3f_2152_, lean_object* v_discharge_x3f_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v___y_2164_; 
if (lean_obj_tag(v_usingTk_x3f_2152_) == 0)
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_box(0);
v___y_2164_ = v___x_2269_;
goto v___jp_2163_;
}
else
{
lean_object* v_val_2270_; 
v_val_2270_ = lean_ctor_get(v_usingTk_x3f_2152_, 0);
lean_inc(v_val_2270_);
lean_dec_ref_known(v_usingTk_x3f_2152_, 1);
v___y_2164_ = v_val_2270_;
goto v___jp_2163_;
}
v___jp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2165_ = lean_mk_empty_array_with_capacity(v___x_2139_);
v___x_2166_ = lean_array_push(v___x_2165_, v_tk_2140_);
v___x_2167_ = lean_array_push(v___x_2166_, v___y_2164_);
v___x_2168_ = lean_box(2);
v___x_2169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2141_);
lean_ctor_set(v___x_2169_, 2, v___x_2167_);
v___x_2170_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2169_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2155_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; size_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2142_);
v___x_2175_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
lean_inc_n(v___x_2142_, 3);
v___x_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2142_);
v___x_2177_ = lean_unsigned_to_nat(32u);
v___x_2178_ = lean_mk_empty_array_with_capacity(v___x_2177_);
v___x_2179_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
v___x_2180_ = ((size_t)5ULL);
v___x_2181_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2178_);
lean_ctor_set(v___x_2181_, 2, v___x_2142_);
lean_ctor_set(v___x_2181_, 3, v___x_2142_);
lean_ctor_set_usize(v___x_2181_, 4, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2175_);
lean_ctor_set(v___x_2182_, 1, v___x_2175_);
lean_ctor_set(v___x_2182_, 2, v___x_2175_);
lean_ctor_set(v___x_2182_, 3, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2176_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
lean_inc_ref(v___x_2183_);
lean_inc(v_discharge_x3f_2153_);
lean_inc_ref(v_simprocs_2144_);
lean_inc_ref(v___x_2143_);
v___x_2184_ = l_Lean_Meta_simpGoal(v_a_2173_, v___x_2143_, v_simprocs_2144_, v_discharge_x3f_2153_, v___x_2145_, v___x_2174_, v___x_2183_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v_fst_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v_fst_2186_ = lean_ctor_get(v_a_2185_, 0);
if (lean_obj_tag(v_fst_2186_) == 1)
{
lean_object* v_val_2187_; lean_object* v_snd_2188_; lean_object* v_snd_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref_known(v___x_2183_, 2);
v_val_2187_ = lean_ctor_get(v_fst_2186_, 0);
lean_inc(v_val_2187_);
v_snd_2188_ = lean_ctor_get(v_a_2185_, 1);
lean_inc(v_snd_2188_);
lean_dec(v_a_2185_);
v_snd_2189_ = lean_ctor_get(v_val_2187_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_val_2187_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v_val_2187_, 0);
lean_dec(v_unused_2214_);
v___x_2191_ = v_val_2187_;
v_isShared_2192_ = v_isSharedCheck_2213_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_snd_2189_);
lean_dec(v_val_2187_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2213_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = lean_box(0);
lean_inc(v_snd_2189_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set_tag(v___x_2191_, 1);
lean_ctor_set(v___x_2191_, 1, v___x_2193_);
lean_ctor_set(v___x_2191_, 0, v_snd_2189_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_snd_2189_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2195_, v___y_2155_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___f_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___y_2202_; lean_object* v___x_2203_; 
lean_dec_ref_known(v___x_2196_, 1);
v___f_2197_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 11, 1);
lean_closure_set(v___f_2197_, 0, v_a_2171_);
v___x_2198_ = lean_box(v___x_2145_);
v___x_2199_ = lean_box(v___x_2147_);
v___x_2200_ = lean_box(v_useReducible_2149_);
v___x_2201_ = lean_box(v___x_2150_);
lean_inc(v_snd_2189_);
v___y_2202_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 23, 14);
lean_closure_set(v___y_2202_, 0, v_usingArg_2146_);
lean_closure_set(v___y_2202_, 1, v_snd_2189_);
lean_closure_set(v___y_2202_, 2, v___x_2198_);
lean_closure_set(v___y_2202_, 3, v___x_2199_);
lean_closure_set(v___y_2202_, 4, v___x_2148_);
lean_closure_set(v___y_2202_, 5, v___x_2200_);
lean_closure_set(v___y_2202_, 6, v___x_2201_);
lean_closure_set(v___y_2202_, 7, v___x_2151_);
lean_closure_set(v___y_2202_, 8, v___x_2143_);
lean_closure_set(v___y_2202_, 9, v_simprocs_2144_);
lean_closure_set(v___y_2202_, 10, v_discharge_x3f_2153_);
lean_closure_set(v___y_2202_, 11, v_snd_2188_);
lean_closure_set(v___y_2202_, 12, v___x_2142_);
lean_closure_set(v___y_2202_, 13, v___f_2197_);
v___x_2203_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_2189_, v___y_2202_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
return v___x_2203_;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_snd_2189_);
lean_dec(v_snd_2188_);
lean_dec(v_a_2171_);
lean_dec(v_discharge_x3f_2153_);
lean_dec(v___x_2151_);
lean_dec_ref(v___x_2148_);
lean_dec(v_usingArg_2146_);
lean_dec_ref(v_simprocs_2144_);
lean_dec_ref(v___x_2143_);
lean_dec(v___x_2142_);
v_a_2204_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2196_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2196_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2185_);
lean_dec(v_a_2171_);
lean_dec(v_discharge_x3f_2153_);
lean_dec(v___x_2151_);
lean_dec_ref(v___x_2148_);
lean_dec(v_usingArg_2146_);
lean_dec_ref(v_simprocs_2144_);
lean_dec_ref(v___x_2143_);
lean_dec(v___x_2142_);
v___x_2215_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2244_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2244_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2216_);
lean_dec(v_a_2216_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2222_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2183_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2183_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
lean_object* v_ref_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_del_object(v___x_2218_);
v_ref_2224_ = lean_ctor_get(v___y_2160_, 5);
v___x_2225_ = l_Lean_linter_unnecessarySimpa;
v___x_2226_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
lean_inc(v_ref_2224_);
v___x_2227_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_2225_, v_ref_2224_, v___x_2226_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v___x_2227_, 0);
lean_dec(v_unused_2235_);
v___x_2229_ = v___x_2227_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v___x_2227_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2183_);
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2183_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref_known(v___x_2183_, 2);
v_a_2236_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2227_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2227_);
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
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref_known(v___x_2183_, 2);
lean_dec(v_a_2171_);
lean_dec(v_discharge_x3f_2153_);
lean_dec(v___x_2151_);
lean_dec_ref(v___x_2148_);
lean_dec(v_usingArg_2146_);
lean_dec_ref(v_simprocs_2144_);
lean_dec_ref(v___x_2143_);
lean_dec(v___x_2142_);
v_a_2245_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2184_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2184_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_a_2171_);
lean_dec(v_discharge_x3f_2153_);
lean_dec(v___x_2151_);
lean_dec_ref(v___x_2148_);
lean_dec(v_usingArg_2146_);
lean_dec_ref(v_simprocs_2144_);
lean_dec_ref(v___x_2143_);
lean_dec(v___x_2142_);
v_a_2253_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2172_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2172_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v_discharge_x3f_2153_);
lean_dec(v___x_2151_);
lean_dec_ref(v___x_2148_);
lean_dec(v_usingArg_2146_);
lean_dec_ref(v_simprocs_2144_);
lean_dec_ref(v___x_2143_);
lean_dec(v___x_2142_);
v_a_2261_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2170_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2170_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v___x_2271_ = _args[0];
lean_object* v_tk_2272_ = _args[1];
lean_object* v___x_2273_ = _args[2];
lean_object* v___x_2274_ = _args[3];
lean_object* v___x_2275_ = _args[4];
lean_object* v_simprocs_2276_ = _args[5];
lean_object* v___x_2277_ = _args[6];
lean_object* v_usingArg_2278_ = _args[7];
lean_object* v___x_2279_ = _args[8];
lean_object* v___x_2280_ = _args[9];
lean_object* v_useReducible_2281_ = _args[10];
lean_object* v___x_2282_ = _args[11];
lean_object* v___x_2283_ = _args[12];
lean_object* v_usingTk_x3f_2284_ = _args[13];
lean_object* v_discharge_x3f_2285_ = _args[14];
lean_object* v___y_2286_ = _args[15];
lean_object* v___y_2287_ = _args[16];
lean_object* v___y_2288_ = _args[17];
lean_object* v___y_2289_ = _args[18];
lean_object* v___y_2290_ = _args[19];
lean_object* v___y_2291_ = _args[20];
lean_object* v___y_2292_ = _args[21];
lean_object* v___y_2293_ = _args[22];
lean_object* v___y_2294_ = _args[23];
_start:
{
uint8_t v___x_77978__boxed_2295_; uint8_t v___x_77979__boxed_2296_; uint8_t v_useReducible_boxed_2297_; uint8_t v___x_77981__boxed_2298_; lean_object* v_res_2299_; 
v___x_77978__boxed_2295_ = lean_unbox(v___x_2277_);
v___x_77979__boxed_2296_ = lean_unbox(v___x_2279_);
v_useReducible_boxed_2297_ = lean_unbox(v_useReducible_2281_);
v___x_77981__boxed_2298_ = lean_unbox(v___x_2282_);
v_res_2299_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v___x_2271_, v_tk_2272_, v___x_2273_, v___x_2274_, v___x_2275_, v_simprocs_2276_, v___x_77978__boxed_2295_, v_usingArg_2278_, v___x_77979__boxed_2296_, v___x_2280_, v_useReducible_boxed_2297_, v___x_77981__boxed_2298_, v___x_2283_, v_usingTk_x3f_2284_, v_discharge_x3f_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___x_2271_);
return v_res_2299_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2308_ = lean_unsigned_to_nat(38u);
v___x_2309_ = lean_unsigned_to_nat(130u);
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2312_ = l_mkPanicMessageWithDecl(v___x_2311_, v___x_2310_, v___x_2309_, v___x_2308_, v___x_2307_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Array_mkArray0(lean_box(0));
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5));
v___x_2330_ = lean_unsigned_to_nat(15u);
v___x_2331_ = lean_unsigned_to_nat(131u);
v___x_2332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4));
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3));
v___x_2334_ = l_mkPanicMessageWithDecl(v___x_2333_, v___x_2332_, v___x_2331_, v___x_2330_, v___x_2329_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v_tk_2336_, lean_object* v___x_2337_, lean_object* v___x_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, uint8_t v___x_2341_, lean_object* v___x_2342_, lean_object* v___x_2343_, uint8_t v_useReducible_2344_, lean_object* v___f_2345_, lean_object* v___x_2346_, lean_object* v___x_2347_, lean_object* v___x_2348_, lean_object* v___x_2349_, lean_object* v___x_2350_, lean_object* v___x_2351_, lean_object* v_usingArg_2352_, lean_object* v___x_2353_, uint8_t v___x_2354_, lean_object* v_usingTk_x3f_2355_, lean_object* v_squeeze_2356_, lean_object* v_unfold_2357_, lean_object* v_args_2358_, lean_object* v_only_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v___y_2371_; lean_object* v___y_2375_; lean_object* v_stx_2376_; lean_object* v___y_2377_; lean_object* v_ref_2378_; lean_object* v___y_2379_; lean_object* v___y_2398_; lean_object* v_stx_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v_options_2424_; lean_object* v_ref_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; uint8_t v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; uint8_t v___y_2840_; lean_object* v_args_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; uint8_t v___y_2880_; lean_object* v_only_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2909_; lean_object* v___y_2910_; uint8_t v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2969_; lean_object* v___y_2970_; uint8_t v___y_2971_; lean_object* v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2984_; uint8_t v___y_2985_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; uint8_t v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3059_; 
v_options_2424_ = lean_ctor_get(v___y_2367_, 2);
v_ref_2425_ = lean_ctor_get(v___y_2367_, 5);
v___x_2426_ = 0;
v___x_2427_ = l_Lean_SourceInfo_fromRef(v_ref_2425_, v___x_2426_);
v___x_2428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7));
lean_inc_ref(v___x_2339_);
lean_inc_ref(v___x_2338_);
lean_inc_ref(v___x_2337_);
v___x_2429_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2428_);
lean_inc(v___x_2427_);
v___x_2430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2427_);
lean_ctor_set(v___x_2430_, 1, v___x_2428_);
v___x_2431_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_2432_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_2360_) == 0)
{
lean_object* v___x_3068_; 
v___x_3068_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_3059_ = v___x_3068_;
goto v___jp_3058_;
}
else
{
lean_object* v_val_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_val_3069_ = lean_ctor_get(v___y_2360_, 0);
lean_inc(v_val_3069_);
lean_dec_ref_known(v___y_2360_, 1);
v___x_3070_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___x_3071_ = lean_array_push(v___x_3070_, v_val_3069_);
v___y_3059_ = v___x_3071_;
goto v___jp_3058_;
}
v___jp_2370_:
{
lean_object* v_diag_2372_; lean_object* v___x_2373_; 
v_diag_2372_ = lean_ctor_get(v___y_2371_, 1);
lean_inc_ref(v_diag_2372_);
lean_dec_ref(v___y_2371_);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v_diag_2372_);
return v___x_2373_;
}
v___jp_2374_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1));
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v_stx_2376_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
lean_ctor_set(v___x_2383_, 2, v___x_2382_);
lean_ctor_set(v___x_2383_, 3, v___x_2382_);
lean_ctor_set(v___x_2383_, 4, v___x_2382_);
lean_ctor_set(v___x_2383_, 5, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v_ref_2378_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2));
v___x_2386_ = 4;
v___x_2387_ = l_Lean_MessageData_nil;
v___x_2388_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2336_, v___x_2383_, v___x_2384_, v___x_2385_, v___x_2382_, v___x_2386_, v___x_2387_, v___y_2377_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2377_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_dec_ref_known(v___x_2388_, 1);
v___y_2371_ = v___y_2375_;
goto v___jp_2370_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___y_2375_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
v___jp_2397_:
{
lean_object* v_ref_2402_; 
v_ref_2402_ = lean_ctor_get(v___y_2400_, 5);
lean_inc(v_ref_2402_);
v___y_2375_ = v___y_2398_;
v_stx_2376_ = v_stx_2399_;
v___y_2377_ = v___y_2400_;
v_ref_2378_ = v_ref_2402_;
v___y_2379_ = v___y_2401_;
goto v___jp_2374_;
}
v___jp_2403_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
v___x_2414_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2413_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___y_2398_ = v___y_2404_;
v_stx_2399_ = v_a_2415_;
v___y_2400_ = v___y_2411_;
v___y_2401_ = v___y_2412_;
goto v___jp_2397_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec_ref(v___y_2404_);
lean_dec(v_tk_2336_);
v_a_2416_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2414_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2414_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
v___jp_2433_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2445_ = l_Array_append___redArg(v___x_2432_, v___y_2444_);
lean_dec_ref(v___y_2444_);
lean_inc_n(v___y_2435_, 2);
v___x_2446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2446_, 0, v___y_2435_);
lean_ctor_set(v___x_2446_, 1, v___x_2431_);
lean_ctor_set(v___x_2446_, 2, v___x_2445_);
v___x_2447_ = l_Lean_Syntax_node5(v___y_2435_, v___x_2342_, v___y_2439_, v___y_2436_, v___y_2437_, v___y_2443_, v___x_2446_);
v___x_2448_ = l_Lean_Syntax_node2(v___y_2435_, v___y_2442_, v___y_2438_, v___x_2447_);
v___y_2398_ = v___y_2434_;
v_stx_2399_ = v___x_2448_;
v___y_2400_ = v___y_2440_;
v___y_2401_ = v___y_2441_;
goto v___jp_2397_;
}
v___jp_2449_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = l_Array_append___redArg(v___x_2432_, v___y_2460_);
lean_dec_ref(v___y_2460_);
lean_inc(v___y_2451_);
v___x_2462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2462_, 0, v___y_2451_);
lean_ctor_set(v___x_2462_, 1, v___x_2431_);
lean_ctor_set(v___x_2462_, 2, v___x_2461_);
if (lean_obj_tag(v___y_2456_) == 1)
{
lean_object* v_val_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec(v___x_2340_);
v_val_2463_ = lean_ctor_get(v___y_2456_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v___y_2456_, 1);
v___x_2464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2451_);
v___x_2465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___y_2451_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = l_Array_mkArray2___redArg(v___x_2465_, v_val_2463_);
v___y_2434_ = v___y_2450_;
v___y_2435_ = v___y_2451_;
v___y_2436_ = v___y_2452_;
v___y_2437_ = v___y_2453_;
v___y_2438_ = v___y_2455_;
v___y_2439_ = v___y_2454_;
v___y_2440_ = v___y_2457_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v___y_2459_;
v___y_2443_ = v___x_2462_;
v___y_2444_ = v___x_2466_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2467_; 
lean_dec(v___y_2456_);
v___x_2467_ = lean_mk_empty_array_with_capacity(v___x_2340_);
lean_dec(v___x_2340_);
v___y_2434_ = v___y_2450_;
v___y_2435_ = v___y_2451_;
v___y_2436_ = v___y_2452_;
v___y_2437_ = v___y_2453_;
v___y_2438_ = v___y_2455_;
v___y_2439_ = v___y_2454_;
v___y_2440_ = v___y_2457_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v___y_2459_;
v___y_2443_ = v___x_2462_;
v___y_2444_ = v___x_2467_;
goto v___jp_2433_;
}
}
v___jp_2468_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = l_Array_append___redArg(v___x_2432_, v___y_2479_);
lean_dec_ref(v___y_2479_);
lean_inc(v___y_2470_);
v___x_2481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2481_, 0, v___y_2470_);
lean_ctor_set(v___x_2481_, 1, v___x_2431_);
lean_ctor_set(v___x_2481_, 2, v___x_2480_);
if (lean_obj_tag(v___y_2474_) == 1)
{
lean_object* v_val_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_val_2482_ = lean_ctor_get(v___y_2474_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v___y_2474_, 1);
v___x_2483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2484_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2483_);
v___x_2485_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2470_, 4);
v___x_2486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___y_2470_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l_Array_append___redArg(v___x_2432_, v_val_2482_);
lean_dec(v_val_2482_);
v___x_2488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2488_, 0, v___y_2470_);
lean_ctor_set(v___x_2488_, 1, v___x_2431_);
lean_ctor_set(v___x_2488_, 2, v___x_2487_);
v___x_2489_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___y_2470_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l_Lean_Syntax_node3(v___y_2470_, v___x_2484_, v___x_2486_, v___x_2488_, v___x_2490_);
v___x_2492_ = l_Array_mkArray1___redArg(v___x_2491_);
v___y_2450_ = v___y_2469_;
v___y_2451_ = v___y_2470_;
v___y_2452_ = v___y_2471_;
v___y_2453_ = v___x_2481_;
v___y_2454_ = v___y_2473_;
v___y_2455_ = v___y_2472_;
v___y_2456_ = v___y_2476_;
v___y_2457_ = v___y_2475_;
v___y_2458_ = v___y_2477_;
v___y_2459_ = v___y_2478_;
v___y_2460_ = v___x_2492_;
goto v___jp_2449_;
}
else
{
lean_object* v___x_2493_; 
lean_dec(v___y_2474_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2493_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2450_ = v___y_2469_;
v___y_2451_ = v___y_2470_;
v___y_2452_ = v___y_2471_;
v___y_2453_ = v___x_2481_;
v___y_2454_ = v___y_2473_;
v___y_2455_ = v___y_2472_;
v___y_2456_ = v___y_2476_;
v___y_2457_ = v___y_2475_;
v___y_2458_ = v___y_2477_;
v___y_2459_ = v___y_2478_;
v___y_2460_ = v___x_2493_;
goto v___jp_2449_;
}
}
v___jp_2494_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = l_Array_append___redArg(v___x_2432_, v___y_2505_);
lean_dec_ref(v___y_2505_);
lean_inc(v___y_2496_);
v___x_2507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2507_, 0, v___y_2496_);
lean_ctor_set(v___x_2507_, 1, v___x_2431_);
lean_ctor_set(v___x_2507_, 2, v___x_2506_);
if (lean_obj_tag(v___y_2499_) == 1)
{
lean_object* v_val_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_val_2508_ = lean_ctor_get(v___y_2499_, 0);
lean_inc(v_val_2508_);
lean_dec_ref_known(v___y_2499_, 1);
v___x_2509_ = l_Lean_SourceInfo_fromRef(v_val_2508_, v___x_2341_);
lean_dec(v_val_2508_);
v___x_2510_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = l_Array_mkArray1___redArg(v___x_2511_);
v___y_2469_ = v___y_2495_;
v___y_2470_ = v___y_2496_;
v___y_2471_ = v___x_2507_;
v___y_2472_ = v___y_2498_;
v___y_2473_ = v___y_2497_;
v___y_2474_ = v___y_2502_;
v___y_2475_ = v___y_2501_;
v___y_2476_ = v___y_2500_;
v___y_2477_ = v___y_2503_;
v___y_2478_ = v___y_2504_;
v___y_2479_ = v___x_2512_;
goto v___jp_2468_;
}
else
{
lean_object* v___x_2513_; 
lean_dec(v___y_2499_);
v___x_2513_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2469_ = v___y_2495_;
v___y_2470_ = v___y_2496_;
v___y_2471_ = v___x_2507_;
v___y_2472_ = v___y_2498_;
v___y_2473_ = v___y_2497_;
v___y_2474_ = v___y_2502_;
v___y_2475_ = v___y_2501_;
v___y_2476_ = v___y_2500_;
v___y_2477_ = v___y_2503_;
v___y_2478_ = v___y_2504_;
v___y_2479_ = v___x_2513_;
goto v___jp_2468_;
}
}
v___jp_2514_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2529_ = l_Array_append___redArg(v___x_2432_, v___y_2528_);
lean_dec_ref(v___y_2528_);
lean_inc_n(v___y_2515_, 3);
v___x_2530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2530_, 0, v___y_2515_);
lean_ctor_set(v___x_2530_, 1, v___x_2431_);
lean_ctor_set(v___x_2530_, 2, v___x_2529_);
v___x_2531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___y_2515_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = l_Lean_Syntax_node6(v___y_2515_, v___y_2524_, v___y_2523_, v___y_2516_, v___y_2527_, v___x_2530_, v___x_2532_, v___y_2525_);
v___x_2534_ = l_Lean_Syntax_node4(v___y_2515_, v___y_2520_, v___y_2518_, v___y_2521_, v___y_2522_, v___x_2533_);
v___y_2398_ = v___y_2519_;
v_stx_2399_ = v___x_2534_;
v___y_2400_ = v___y_2517_;
v___y_2401_ = v___y_2526_;
goto v___jp_2397_;
}
v___jp_2535_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = l_Array_append___redArg(v___x_2432_, v___y_2549_);
lean_dec_ref(v___y_2549_);
lean_inc(v___y_2536_);
v___x_2551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2551_, 0, v___y_2536_);
lean_ctor_set(v___x_2551_, 1, v___x_2431_);
lean_ctor_set(v___x_2551_, 2, v___x_2550_);
if (lean_obj_tag(v___y_2537_) == 1)
{
lean_object* v_val_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v___x_2340_);
v_val_2552_ = lean_ctor_get(v___y_2537_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v___y_2537_, 1);
v___x_2553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2554_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2553_);
v___x_2555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2536_, 4);
v___x_2556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___y_2536_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = l_Array_append___redArg(v___x_2432_, v_val_2552_);
lean_dec(v_val_2552_);
v___x_2558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2558_, 0, v___y_2536_);
lean_ctor_set(v___x_2558_, 1, v___x_2431_);
lean_ctor_set(v___x_2558_, 2, v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___y_2536_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = l_Lean_Syntax_node3(v___y_2536_, v___x_2554_, v___x_2556_, v___x_2558_, v___x_2560_);
v___x_2562_ = l_Array_mkArray1___redArg(v___x_2561_);
v___y_2515_ = v___y_2536_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2539_;
v___y_2518_ = v___y_2540_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2542_;
v___y_2521_ = v___y_2543_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___x_2551_;
v___y_2528_ = v___x_2562_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2563_; 
lean_dec(v___y_2537_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2563_ = lean_mk_empty_array_with_capacity(v___x_2340_);
lean_dec(v___x_2340_);
v___y_2515_ = v___y_2536_;
v___y_2516_ = v___y_2538_;
v___y_2517_ = v___y_2539_;
v___y_2518_ = v___y_2540_;
v___y_2519_ = v___y_2541_;
v___y_2520_ = v___y_2542_;
v___y_2521_ = v___y_2543_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___x_2551_;
v___y_2528_ = v___x_2563_;
goto v___jp_2514_;
}
}
v___jp_2564_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = l_Array_append___redArg(v___x_2432_, v___y_2578_);
lean_dec_ref(v___y_2578_);
lean_inc(v___y_2565_);
v___x_2580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2580_, 0, v___y_2565_);
lean_ctor_set(v___x_2580_, 1, v___x_2431_);
lean_ctor_set(v___x_2580_, 2, v___x_2579_);
if (lean_obj_tag(v___y_2566_) == 1)
{
lean_object* v_val_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_val_2581_ = lean_ctor_get(v___y_2566_, 0);
lean_inc(v_val_2581_);
lean_dec_ref_known(v___y_2566_, 1);
v___x_2582_ = l_Lean_SourceInfo_fromRef(v_val_2581_, v___x_2341_);
lean_dec(v_val_2581_);
v___x_2583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = l_Array_mkArray1___redArg(v___x_2584_);
v___y_2536_ = v___y_2565_;
v___y_2537_ = v___y_2567_;
v___y_2538_ = v___x_2580_;
v___y_2539_ = v___y_2568_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___y_2571_;
v___y_2543_ = v___y_2572_;
v___y_2544_ = v___y_2573_;
v___y_2545_ = v___y_2574_;
v___y_2546_ = v___y_2575_;
v___y_2547_ = v___y_2576_;
v___y_2548_ = v___y_2577_;
v___y_2549_ = v___x_2585_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2586_; 
lean_dec(v___y_2566_);
v___x_2586_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2536_ = v___y_2565_;
v___y_2537_ = v___y_2567_;
v___y_2538_ = v___x_2580_;
v___y_2539_ = v___y_2568_;
v___y_2540_ = v___y_2569_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___y_2571_;
v___y_2543_ = v___y_2572_;
v___y_2544_ = v___y_2573_;
v___y_2545_ = v___y_2574_;
v___y_2546_ = v___y_2575_;
v___y_2547_ = v___y_2576_;
v___y_2548_ = v___y_2577_;
v___y_2549_ = v___x_2586_;
goto v___jp_2535_;
}
}
v___jp_2587_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = l_Array_append___redArg(v___x_2432_, v___y_2598_);
lean_dec_ref(v___y_2598_);
lean_inc_n(v___y_2589_, 2);
v___x_2600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2600_, 0, v___y_2589_);
lean_ctor_set(v___x_2600_, 1, v___x_2431_);
lean_ctor_set(v___x_2600_, 2, v___x_2599_);
v___x_2601_ = l_Lean_Syntax_node5(v___y_2589_, v___x_2342_, v___y_2591_, v___y_2590_, v___y_2596_, v___y_2597_, v___x_2600_);
lean_inc(v___y_2594_);
v___x_2602_ = l_Lean_Syntax_node4(v___y_2589_, v___x_2343_, v___y_2595_, v___y_2594_, v___y_2594_, v___x_2601_);
v___y_2398_ = v___y_2588_;
v_stx_2399_ = v___x_2602_;
v___y_2400_ = v___y_2592_;
v___y_2401_ = v___y_2593_;
goto v___jp_2397_;
}
v___jp_2603_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = l_Array_append___redArg(v___x_2432_, v___y_2614_);
lean_dec_ref(v___y_2614_);
lean_inc(v___y_2605_);
v___x_2616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___y_2605_);
lean_ctor_set(v___x_2616_, 1, v___x_2431_);
lean_ctor_set(v___x_2616_, 2, v___x_2615_);
if (lean_obj_tag(v___y_2608_) == 1)
{
lean_object* v_val_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_dec(v___x_2340_);
v_val_2617_ = lean_ctor_get(v___y_2608_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v___y_2608_, 1);
v___x_2618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
lean_inc(v___y_2605_);
v___x_2619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___y_2605_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Array_mkArray2___redArg(v___x_2619_, v_val_2617_);
v___y_2588_ = v___y_2604_;
v___y_2589_ = v___y_2605_;
v___y_2590_ = v___y_2607_;
v___y_2591_ = v___y_2606_;
v___y_2592_ = v___y_2609_;
v___y_2593_ = v___y_2612_;
v___y_2594_ = v___y_2611_;
v___y_2595_ = v___y_2610_;
v___y_2596_ = v___y_2613_;
v___y_2597_ = v___x_2616_;
v___y_2598_ = v___x_2620_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2621_; 
lean_dec(v___y_2608_);
v___x_2621_ = lean_mk_empty_array_with_capacity(v___x_2340_);
lean_dec(v___x_2340_);
v___y_2588_ = v___y_2604_;
v___y_2589_ = v___y_2605_;
v___y_2590_ = v___y_2607_;
v___y_2591_ = v___y_2606_;
v___y_2592_ = v___y_2609_;
v___y_2593_ = v___y_2612_;
v___y_2594_ = v___y_2611_;
v___y_2595_ = v___y_2610_;
v___y_2596_ = v___y_2613_;
v___y_2597_ = v___x_2616_;
v___y_2598_ = v___x_2621_;
goto v___jp_2587_;
}
}
v___jp_2622_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = l_Array_append___redArg(v___x_2432_, v___y_2633_);
lean_dec_ref(v___y_2633_);
lean_inc(v___y_2624_);
v___x_2635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2635_, 0, v___y_2624_);
lean_ctor_set(v___x_2635_, 1, v___x_2431_);
lean_ctor_set(v___x_2635_, 2, v___x_2634_);
if (lean_obj_tag(v___y_2627_) == 1)
{
lean_object* v_val_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v_val_2636_ = lean_ctor_get(v___y_2627_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v___y_2627_, 1);
v___x_2637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2638_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2637_);
v___x_2639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2624_, 4);
v___x_2640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___y_2624_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = l_Array_append___redArg(v___x_2432_, v_val_2636_);
lean_dec(v_val_2636_);
v___x_2642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2642_, 0, v___y_2624_);
lean_ctor_set(v___x_2642_, 1, v___x_2431_);
lean_ctor_set(v___x_2642_, 2, v___x_2641_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___y_2624_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_Lean_Syntax_node3(v___y_2624_, v___x_2638_, v___x_2640_, v___x_2642_, v___x_2644_);
v___x_2646_ = l_Array_mkArray1___redArg(v___x_2645_);
v___y_2604_ = v___y_2623_;
v___y_2605_ = v___y_2624_;
v___y_2606_ = v___y_2626_;
v___y_2607_ = v___y_2625_;
v___y_2608_ = v___y_2629_;
v___y_2609_ = v___y_2628_;
v___y_2610_ = v___y_2632_;
v___y_2611_ = v___y_2631_;
v___y_2612_ = v___y_2630_;
v___y_2613_ = v___x_2635_;
v___y_2614_ = v___x_2646_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2647_; 
lean_dec(v___y_2627_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2647_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2604_ = v___y_2623_;
v___y_2605_ = v___y_2624_;
v___y_2606_ = v___y_2626_;
v___y_2607_ = v___y_2625_;
v___y_2608_ = v___y_2629_;
v___y_2609_ = v___y_2628_;
v___y_2610_ = v___y_2632_;
v___y_2611_ = v___y_2631_;
v___y_2612_ = v___y_2630_;
v___y_2613_ = v___x_2635_;
v___y_2614_ = v___x_2647_;
goto v___jp_2603_;
}
}
v___jp_2648_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = l_Array_append___redArg(v___x_2432_, v___y_2659_);
lean_dec_ref(v___y_2659_);
lean_inc(v___y_2650_);
v___x_2661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2661_, 0, v___y_2650_);
lean_ctor_set(v___x_2661_, 1, v___x_2431_);
lean_ctor_set(v___x_2661_, 2, v___x_2660_);
if (lean_obj_tag(v___y_2652_) == 1)
{
lean_object* v_val_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_val_2662_ = lean_ctor_get(v___y_2652_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v___y_2652_, 1);
v___x_2663_ = l_Lean_SourceInfo_fromRef(v_val_2662_, v___x_2341_);
lean_dec(v_val_2662_);
v___x_2664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = l_Array_mkArray1___redArg(v___x_2665_);
v___y_2623_ = v___y_2649_;
v___y_2624_ = v___y_2650_;
v___y_2625_ = v___x_2661_;
v___y_2626_ = v___y_2651_;
v___y_2627_ = v___y_2655_;
v___y_2628_ = v___y_2654_;
v___y_2629_ = v___y_2653_;
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2657_;
v___y_2632_ = v___y_2656_;
v___y_2633_ = v___x_2666_;
goto v___jp_2622_;
}
else
{
lean_object* v___x_2667_; 
lean_dec(v___y_2652_);
v___x_2667_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2623_ = v___y_2649_;
v___y_2624_ = v___y_2650_;
v___y_2625_ = v___x_2661_;
v___y_2626_ = v___y_2651_;
v___y_2627_ = v___y_2655_;
v___y_2628_ = v___y_2654_;
v___y_2629_ = v___y_2653_;
v___y_2630_ = v___y_2658_;
v___y_2631_ = v___y_2657_;
v___y_2632_ = v___y_2656_;
v___y_2633_ = v___x_2667_;
goto v___jp_2622_;
}
}
v___jp_2668_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2682_ = l_Array_append___redArg(v___x_2432_, v___y_2681_);
lean_dec_ref(v___y_2681_);
lean_inc_n(v___y_2670_, 3);
v___x_2683_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2683_, 0, v___y_2670_);
lean_ctor_set(v___x_2683_, 1, v___x_2431_);
lean_ctor_set(v___x_2683_, 2, v___x_2682_);
v___x_2684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16));
v___x_2685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___y_2670_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_Lean_Syntax_node6(v___y_2670_, v___y_2676_, v___y_2677_, v___y_2669_, v___y_2678_, v___x_2683_, v___x_2685_, v___y_2675_);
lean_inc(v___y_2673_);
v___x_2687_ = l_Lean_Syntax_node4(v___y_2670_, v___y_2671_, v___y_2680_, v___y_2673_, v___y_2673_, v___x_2686_);
v___y_2398_ = v___y_2674_;
v_stx_2399_ = v___x_2687_;
v___y_2400_ = v___y_2672_;
v___y_2401_ = v___y_2679_;
goto v___jp_2397_;
}
v___jp_2688_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = l_Array_append___redArg(v___x_2432_, v___y_2701_);
lean_dec_ref(v___y_2701_);
lean_inc(v___y_2690_);
v___x_2703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___y_2690_);
lean_ctor_set(v___x_2703_, 1, v___x_2431_);
lean_ctor_set(v___x_2703_, 2, v___x_2702_);
if (lean_obj_tag(v___y_2693_) == 1)
{
lean_object* v_val_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec(v___x_2340_);
v_val_2704_ = lean_ctor_get(v___y_2693_, 0);
lean_inc(v_val_2704_);
lean_dec_ref_known(v___y_2693_, 1);
v___x_2705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12));
v___x_2706_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2705_);
v___x_2707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_2690_, 4);
v___x_2708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___y_2690_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Array_append___redArg(v___x_2432_, v_val_2704_);
lean_dec(v_val_2704_);
v___x_2710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2710_, 0, v___y_2690_);
lean_ctor_set(v___x_2710_, 1, v___x_2431_);
lean_ctor_set(v___x_2710_, 2, v___x_2709_);
v___x_2711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_2712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___y_2690_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = l_Lean_Syntax_node3(v___y_2690_, v___x_2706_, v___x_2708_, v___x_2710_, v___x_2712_);
v___x_2714_ = l_Array_mkArray1___redArg(v___x_2713_);
v___y_2669_ = v___y_2689_;
v___y_2670_ = v___y_2690_;
v___y_2671_ = v___y_2691_;
v___y_2672_ = v___y_2692_;
v___y_2673_ = v___y_2694_;
v___y_2674_ = v___y_2695_;
v___y_2675_ = v___y_2696_;
v___y_2676_ = v___y_2697_;
v___y_2677_ = v___y_2698_;
v___y_2678_ = v___x_2703_;
v___y_2679_ = v___y_2699_;
v___y_2680_ = v___y_2700_;
v___y_2681_ = v___x_2714_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2715_; 
lean_dec(v___y_2693_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2715_ = lean_mk_empty_array_with_capacity(v___x_2340_);
lean_dec(v___x_2340_);
v___y_2669_ = v___y_2689_;
v___y_2670_ = v___y_2690_;
v___y_2671_ = v___y_2691_;
v___y_2672_ = v___y_2692_;
v___y_2673_ = v___y_2694_;
v___y_2674_ = v___y_2695_;
v___y_2675_ = v___y_2696_;
v___y_2676_ = v___y_2697_;
v___y_2677_ = v___y_2698_;
v___y_2678_ = v___x_2703_;
v___y_2679_ = v___y_2699_;
v___y_2680_ = v___y_2700_;
v___y_2681_ = v___x_2715_;
goto v___jp_2668_;
}
}
v___jp_2716_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = l_Array_append___redArg(v___x_2432_, v___y_2729_);
lean_dec_ref(v___y_2729_);
lean_inc(v___y_2717_);
v___x_2731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2731_, 0, v___y_2717_);
lean_ctor_set(v___x_2731_, 1, v___x_2431_);
lean_ctor_set(v___x_2731_, 2, v___x_2730_);
if (lean_obj_tag(v___y_2719_) == 1)
{
lean_object* v_val_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_val_2732_ = lean_ctor_get(v___y_2719_, 0);
lean_inc(v_val_2732_);
lean_dec_ref_known(v___y_2719_, 1);
v___x_2733_ = l_Lean_SourceInfo_fromRef(v_val_2732_, v___x_2341_);
lean_dec(v_val_2732_);
v___x_2734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_2735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = l_Array_mkArray1___redArg(v___x_2735_);
v___y_2689_ = v___x_2731_;
v___y_2690_ = v___y_2717_;
v___y_2691_ = v___y_2718_;
v___y_2692_ = v___y_2720_;
v___y_2693_ = v___y_2721_;
v___y_2694_ = v___y_2722_;
v___y_2695_ = v___y_2723_;
v___y_2696_ = v___y_2724_;
v___y_2697_ = v___y_2725_;
v___y_2698_ = v___y_2726_;
v___y_2699_ = v___y_2727_;
v___y_2700_ = v___y_2728_;
v___y_2701_ = v___x_2736_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2737_; 
lean_dec(v___y_2719_);
v___x_2737_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2689_ = v___x_2731_;
v___y_2690_ = v___y_2717_;
v___y_2691_ = v___y_2718_;
v___y_2692_ = v___y_2720_;
v___y_2693_ = v___y_2721_;
v___y_2694_ = v___y_2722_;
v___y_2695_ = v___y_2723_;
v___y_2696_ = v___y_2724_;
v___y_2697_ = v___y_2725_;
v___y_2698_ = v___y_2726_;
v___y_2699_ = v___y_2727_;
v___y_2700_ = v___y_2728_;
v___y_2701_ = v___x_2737_;
goto v___jp_2688_;
}
}
v___jp_2738_:
{
if (v___y_2751_ == 0)
{
if (v_useReducible_2344_ == 0)
{
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
if (lean_obj_tag(v___y_2749_) == 0)
{
lean_dec(v___y_2753_);
lean_dec(v___y_2748_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___y_2404_ = v___y_2747_;
v___y_2405_ = v___y_2745_;
v___y_2406_ = v___y_2744_;
v___y_2407_ = v___y_2742_;
v___y_2408_ = v___y_2739_;
v___y_2409_ = v___y_2752_;
v___y_2410_ = v___y_2746_;
v___y_2411_ = v___y_2743_;
v___y_2412_ = v___y_2750_;
goto v___jp_2403_;
}
else
{
lean_object* v_val_2754_; lean_object* v___x_2755_; 
v_val_2754_ = lean_ctor_get(v___y_2749_, 0);
lean_inc(v_val_2754_);
lean_dec_ref_known(v___y_2749_, 1);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2743_);
v___x_2755_ = lean_apply_9(v___f_2345_, v___y_2745_, v___y_2744_, v___y_2742_, v___y_2739_, v___y_2752_, v___y_2746_, v___y_2743_, v___y_2750_, lean_box(0));
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_n(v_a_2756_, 3);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2339_, 2);
lean_inc_ref_n(v___x_2338_, 2);
lean_inc_ref_n(v___x_2337_, 2);
v___x_2758_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2756_);
lean_ctor_set(v___x_2759_, 1, v___x_2346_);
v___x_2760_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2760_, 0, v_a_2756_);
lean_ctor_set(v___x_2760_, 1, v___x_2431_);
lean_ctor_set(v___x_2760_, 2, v___x_2432_);
v___x_2761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2762_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2761_);
if (lean_obj_tag(v___y_2753_) == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2717_ = v_a_2756_;
v___y_2718_ = v___x_2758_;
v___y_2719_ = v___y_2740_;
v___y_2720_ = v___y_2743_;
v___y_2721_ = v___y_2741_;
v___y_2722_ = v___x_2760_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v_val_2754_;
v___y_2725_ = v___x_2762_;
v___y_2726_ = v___y_2748_;
v___y_2727_ = v___y_2750_;
v___y_2728_ = v___x_2759_;
v___y_2729_ = v___x_2763_;
goto v___jp_2716_;
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v_val_2764_ = lean_ctor_get(v___y_2753_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___y_2753_, 1);
v___x_2765_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___x_2766_ = lean_array_push(v___x_2765_, v_val_2764_);
v___y_2717_ = v_a_2756_;
v___y_2718_ = v___x_2758_;
v___y_2719_ = v___y_2740_;
v___y_2720_ = v___y_2743_;
v___y_2721_ = v___y_2741_;
v___y_2722_ = v___x_2760_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v_val_2754_;
v___y_2725_ = v___x_2762_;
v___y_2726_ = v___y_2748_;
v___y_2727_ = v___y_2750_;
v___y_2728_ = v___x_2759_;
v___y_2729_ = v___x_2766_;
goto v___jp_2716_;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_val_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2750_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2346_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v_a_2767_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2755_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2755_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
else
{
lean_object* v___x_2775_; 
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2743_);
v___x_2775_ = lean_apply_9(v___f_2345_, v___y_2745_, v___y_2744_, v___y_2742_, v___y_2739_, v___y_2752_, v___y_2746_, v___y_2743_, v___y_2750_, lean_box(0));
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc_n(v_a_2776_, 3);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2777_, 0, v_a_2776_);
lean_ctor_set(v___x_2777_, 1, v___x_2346_);
v___x_2778_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2778_, 0, v_a_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2431_);
lean_ctor_set(v___x_2778_, 2, v___x_2432_);
if (lean_obj_tag(v___y_2753_) == 0)
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2649_ = v___y_2747_;
v___y_2650_ = v_a_2776_;
v___y_2651_ = v___y_2748_;
v___y_2652_ = v___y_2740_;
v___y_2653_ = v___y_2749_;
v___y_2654_ = v___y_2743_;
v___y_2655_ = v___y_2741_;
v___y_2656_ = v___x_2777_;
v___y_2657_ = v___x_2778_;
v___y_2658_ = v___y_2750_;
v___y_2659_ = v___x_2779_;
goto v___jp_2648_;
}
else
{
lean_object* v_val_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v_val_2780_ = lean_ctor_get(v___y_2753_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v___y_2753_, 1);
v___x_2781_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___x_2782_ = lean_array_push(v___x_2781_, v_val_2780_);
v___y_2649_ = v___y_2747_;
v___y_2650_ = v_a_2776_;
v___y_2651_ = v___y_2748_;
v___y_2652_ = v___y_2740_;
v___y_2653_ = v___y_2749_;
v___y_2654_ = v___y_2743_;
v___y_2655_ = v___y_2741_;
v___y_2656_ = v___x_2777_;
v___y_2657_ = v___x_2778_;
v___y_2658_ = v___y_2750_;
v___y_2659_ = v___x_2782_;
goto v___jp_2648_;
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v___y_2753_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2346_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v_a_2783_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2775_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2775_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
else
{
lean_dec(v___x_2343_);
if (v_useReducible_2344_ == 0)
{
lean_dec(v___x_2342_);
if (lean_obj_tag(v___y_2749_) == 0)
{
lean_dec(v___y_2753_);
lean_dec(v___y_2748_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___y_2404_ = v___y_2747_;
v___y_2405_ = v___y_2745_;
v___y_2406_ = v___y_2744_;
v___y_2407_ = v___y_2742_;
v___y_2408_ = v___y_2739_;
v___y_2409_ = v___y_2752_;
v___y_2410_ = v___y_2746_;
v___y_2411_ = v___y_2743_;
v___y_2412_ = v___y_2750_;
goto v___jp_2403_;
}
else
{
lean_object* v_val_2791_; lean_object* v___x_2792_; 
v_val_2791_ = lean_ctor_get(v___y_2749_, 0);
lean_inc(v_val_2791_);
lean_dec_ref_known(v___y_2749_, 1);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2743_);
v___x_2792_ = lean_apply_9(v___f_2345_, v___y_2745_, v___y_2744_, v___y_2742_, v___y_2739_, v___y_2752_, v___y_2746_, v___y_2743_, v___y_2750_, lean_box(0));
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc_n(v_a_2793_, 5);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17));
lean_inc_ref_n(v___x_2339_, 2);
lean_inc_ref_n(v___x_2338_, 2);
lean_inc_ref_n(v___x_2337_, 2);
v___x_2795_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2793_);
lean_ctor_set(v___x_2796_, 1, v___x_2346_);
v___x_2797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2797_, 0, v_a_2793_);
lean_ctor_set(v___x_2797_, 1, v___x_2431_);
lean_ctor_set(v___x_2797_, 2, v___x_2432_);
v___x_2798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_2799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_a_2793_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = l_Lean_Syntax_node1(v_a_2793_, v___x_2431_, v___x_2799_);
v___x_2801_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18));
v___x_2802_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2801_);
if (lean_obj_tag(v___y_2753_) == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2565_ = v_a_2793_;
v___y_2566_ = v___y_2740_;
v___y_2567_ = v___y_2741_;
v___y_2568_ = v___y_2743_;
v___y_2569_ = v___x_2796_;
v___y_2570_ = v___y_2747_;
v___y_2571_ = v___x_2795_;
v___y_2572_ = v___x_2797_;
v___y_2573_ = v___x_2800_;
v___y_2574_ = v___y_2748_;
v___y_2575_ = v___x_2802_;
v___y_2576_ = v_val_2791_;
v___y_2577_ = v___y_2750_;
v___y_2578_ = v___x_2803_;
goto v___jp_2564_;
}
else
{
lean_object* v_val_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_val_2804_ = lean_ctor_get(v___y_2753_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v___y_2753_, 1);
v___x_2805_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___x_2806_ = lean_array_push(v___x_2805_, v_val_2804_);
v___y_2565_ = v_a_2793_;
v___y_2566_ = v___y_2740_;
v___y_2567_ = v___y_2741_;
v___y_2568_ = v___y_2743_;
v___y_2569_ = v___x_2796_;
v___y_2570_ = v___y_2747_;
v___y_2571_ = v___x_2795_;
v___y_2572_ = v___x_2797_;
v___y_2573_ = v___x_2800_;
v___y_2574_ = v___y_2748_;
v___y_2575_ = v___x_2802_;
v___y_2576_ = v_val_2791_;
v___y_2577_ = v___y_2750_;
v___y_2578_ = v___x_2806_;
goto v___jp_2564_;
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_val_2791_);
lean_dec(v___y_2753_);
lean_dec(v___y_2750_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___x_2346_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v_a_2807_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2792_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2792_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
else
{
lean_object* v___x_2815_; 
lean_dec_ref(v___x_2346_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2743_);
v___x_2815_ = lean_apply_9(v___f_2345_, v___y_2745_, v___y_2744_, v___y_2742_, v___y_2739_, v___y_2752_, v___y_2746_, v___y_2743_, v___y_2750_, lean_box(0));
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc_n(v_a_2816_, 2);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20));
lean_inc_ref(v___x_2339_);
lean_inc_ref(v___x_2338_);
lean_inc_ref(v___x_2337_);
v___x_2818_ = l_Lean_Name_mkStr4(v___x_2337_, v___x_2338_, v___x_2339_, v___x_2817_);
v___x_2819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21));
v___x_2820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_a_2816_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
if (lean_obj_tag(v___y_2753_) == 0)
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_2495_ = v___y_2747_;
v___y_2496_ = v_a_2816_;
v___y_2497_ = v___y_2748_;
v___y_2498_ = v___x_2820_;
v___y_2499_ = v___y_2740_;
v___y_2500_ = v___y_2749_;
v___y_2501_ = v___y_2743_;
v___y_2502_ = v___y_2741_;
v___y_2503_ = v___y_2750_;
v___y_2504_ = v___x_2818_;
v___y_2505_ = v___x_2821_;
goto v___jp_2494_;
}
else
{
lean_object* v_val_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_val_2822_ = lean_ctor_get(v___y_2753_, 0);
lean_inc(v_val_2822_);
lean_dec_ref_known(v___y_2753_, 1);
v___x_2823_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___x_2824_ = lean_array_push(v___x_2823_, v_val_2822_);
v___y_2495_ = v___y_2747_;
v___y_2496_ = v_a_2816_;
v___y_2497_ = v___y_2748_;
v___y_2498_ = v___x_2820_;
v___y_2499_ = v___y_2740_;
v___y_2500_ = v___y_2749_;
v___y_2501_ = v___y_2743_;
v___y_2502_ = v___y_2741_;
v___y_2503_ = v___y_2750_;
v___y_2504_ = v___x_2818_;
v___y_2505_ = v___x_2824_;
goto v___jp_2494_;
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v___y_2753_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v_a_2825_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2815_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2815_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
v___jp_2833_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(5u);
v___x_2851_ = l_Lean_Syntax_getArg(v___y_2838_, v___x_2850_);
lean_dec(v___y_2838_);
v___x_2852_ = l_Lean_Syntax_matchesNull(v___x_2851_, v___x_2340_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec(v_args_2841_);
lean_dec(v___y_2839_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2854_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2853_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___y_2398_ = v___y_2834_;
v_stx_2399_ = v_a_2855_;
v___y_2400_ = v___y_2848_;
v___y_2401_ = v___y_2849_;
goto v___jp_2397_;
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v___y_2834_);
lean_dec(v_tk_2336_);
v_a_2856_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2854_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2854_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Syntax_getOptional_x3f(v___y_2839_);
lean_dec(v___y_2839_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_box(0);
v___y_2739_ = v___y_2845_;
v___y_2740_ = v___y_2836_;
v___y_2741_ = v_args_2841_;
v___y_2742_ = v___y_2844_;
v___y_2743_ = v___y_2848_;
v___y_2744_ = v___y_2843_;
v___y_2745_ = v___y_2842_;
v___y_2746_ = v___y_2847_;
v___y_2747_ = v___y_2834_;
v___y_2748_ = v___y_2835_;
v___y_2749_ = v___y_2837_;
v___y_2750_ = v___y_2849_;
v___y_2751_ = v___y_2840_;
v___y_2752_ = v___y_2846_;
v___y_2753_ = v___x_2865_;
goto v___jp_2738_;
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
v_val_2866_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2864_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_val_2866_);
lean_dec(v___x_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_val_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
v___y_2739_ = v___y_2845_;
v___y_2740_ = v___y_2836_;
v___y_2741_ = v_args_2841_;
v___y_2742_ = v___y_2844_;
v___y_2743_ = v___y_2848_;
v___y_2744_ = v___y_2843_;
v___y_2745_ = v___y_2842_;
v___y_2746_ = v___y_2847_;
v___y_2747_ = v___y_2834_;
v___y_2748_ = v___y_2835_;
v___y_2749_ = v___y_2837_;
v___y_2750_ = v___y_2849_;
v___y_2751_ = v___y_2840_;
v___y_2752_ = v___y_2846_;
v___y_2753_ = v___x_2871_;
goto v___jp_2738_;
}
}
}
}
}
v___jp_2874_:
{
lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2890_ = l_Lean_Syntax_getArg(v___y_2878_, v___x_2347_);
v___x_2891_ = l_Lean_Syntax_isNone(v___x_2890_);
if (v___x_2891_ == 0)
{
uint8_t v___x_2892_; 
lean_inc(v___x_2890_);
v___x_2892_ = l_Lean_Syntax_matchesNull(v___x_2890_, v___x_2348_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec(v___x_2890_);
lean_dec(v_only_2881_);
lean_dec(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2893_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2894_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2893_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___y_2398_ = v___y_2875_;
v_stx_2399_ = v_a_2895_;
v___y_2400_ = v___y_2888_;
v___y_2401_ = v___y_2889_;
goto v___jp_2397_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v___y_2875_);
lean_dec(v_tk_2336_);
v_a_2896_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2894_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2894_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = l_Lean_Syntax_getArg(v___x_2890_, v___x_2349_);
lean_dec(v___x_2349_);
lean_dec(v___x_2890_);
v___x_2905_ = l_Lean_Syntax_getArgs(v___x_2904_);
lean_dec(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
v___y_2834_ = v___y_2875_;
v___y_2835_ = v___y_2876_;
v___y_2836_ = v_only_2881_;
v___y_2837_ = v___y_2877_;
v___y_2838_ = v___y_2878_;
v___y_2839_ = v___y_2879_;
v___y_2840_ = v___y_2880_;
v_args_2841_ = v___x_2906_;
v___y_2842_ = v___y_2882_;
v___y_2843_ = v___y_2883_;
v___y_2844_ = v___y_2884_;
v___y_2845_ = v___y_2885_;
v___y_2846_ = v___y_2886_;
v___y_2847_ = v___y_2887_;
v___y_2848_ = v___y_2888_;
v___y_2849_ = v___y_2889_;
goto v___jp_2833_;
}
}
else
{
lean_object* v___x_2907_; 
lean_dec(v___x_2890_);
lean_dec(v___x_2349_);
v___x_2907_ = lean_box(0);
v___y_2834_ = v___y_2875_;
v___y_2835_ = v___y_2876_;
v___y_2836_ = v_only_2881_;
v___y_2837_ = v___y_2877_;
v___y_2838_ = v___y_2878_;
v___y_2839_ = v___y_2879_;
v___y_2840_ = v___y_2880_;
v_args_2841_ = v___x_2907_;
v___y_2842_ = v___y_2882_;
v___y_2843_ = v___y_2883_;
v___y_2844_ = v___y_2884_;
v___y_2845_ = v___y_2885_;
v___y_2846_ = v___y_2886_;
v___y_2847_ = v___y_2887_;
v___y_2848_ = v___y_2888_;
v___y_2849_ = v___y_2889_;
goto v___jp_2833_;
}
}
v___jp_2908_:
{
lean_object* v_usedTheorems_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_usedTheorems_2913_ = lean_ctor_get(v___y_2909_, 0);
v___x_2914_ = l_Lean_Syntax_unsetTrailing(v___y_2910_);
v___x_2915_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_2914_, v_usedTheorems_2913_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; uint8_t v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc_n(v_a_2916_, 2);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = l_Lean_Syntax_isOfKind(v_a_2916_, v___x_2429_);
lean_dec(v___x_2429_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_inc(v_ref_2425_);
lean_dec(v_a_2916_);
lean_dec(v___y_2912_);
lean_dec(v___x_2351_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2918_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2919_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2918_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___y_2375_ = v___y_2909_;
v_stx_2376_ = v_a_2920_;
v___y_2377_ = v___y_2367_;
v_ref_2378_ = v_ref_2425_;
v___y_2379_ = v___y_2368_;
goto v___jp_2374_;
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v___y_2909_);
lean_dec(v_ref_2425_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_tk_2336_);
v_a_2921_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2919_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2919_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2929_ = l_Lean_Syntax_getArg(v_a_2916_, v___x_2349_);
lean_inc(v___x_2929_);
v___x_2930_ = l_Lean_Syntax_isOfKind(v___x_2929_, v___x_2350_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_inc(v_ref_2425_);
lean_dec(v___x_2929_);
lean_dec(v_a_2916_);
lean_dec(v___y_2912_);
lean_dec(v___x_2351_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2931_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2932_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2931_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___y_2375_ = v___y_2909_;
v_stx_2376_ = v_a_2933_;
v___y_2377_ = v___y_2367_;
v_ref_2378_ = v_ref_2425_;
v___y_2379_ = v___y_2368_;
goto v___jp_2374_;
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v___y_2909_);
lean_dec(v_ref_2425_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_tk_2336_);
v_a_2934_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2932_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2932_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2942_ = l_Lean_Syntax_getArg(v_a_2916_, v___x_2351_);
lean_dec(v___x_2351_);
v___x_2943_ = l_Lean_Syntax_getArg(v_a_2916_, v___x_2348_);
v___x_2944_ = l_Lean_Syntax_isNone(v___x_2943_);
if (v___x_2944_ == 0)
{
uint8_t v___x_2945_; 
lean_inc(v___x_2943_);
v___x_2945_ = l_Lean_Syntax_matchesNull(v___x_2943_, v___x_2349_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_inc(v_ref_2425_);
lean_dec(v___x_2943_);
lean_dec(v___x_2942_);
lean_dec(v___x_2929_);
lean_dec(v_a_2916_);
lean_dec(v___y_2912_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
v___x_2946_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
v___x_2947_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_2946_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___y_2375_ = v___y_2909_;
v_stx_2376_ = v_a_2948_;
v___y_2377_ = v___y_2367_;
v_ref_2378_ = v_ref_2425_;
v___y_2379_ = v___y_2368_;
goto v___jp_2374_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v___y_2909_);
lean_dec(v_ref_2425_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_tk_2336_);
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
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = l_Lean_Syntax_getArg(v___x_2943_, v___x_2340_);
lean_dec(v___x_2943_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
v___y_2875_ = v___y_2909_;
v___y_2876_ = v___x_2929_;
v___y_2877_ = v___y_2912_;
v___y_2878_ = v_a_2916_;
v___y_2879_ = v___x_2942_;
v___y_2880_ = v___y_2911_;
v_only_2881_ = v___x_2958_;
v___y_2882_ = v___y_2361_;
v___y_2883_ = v___y_2362_;
v___y_2884_ = v___y_2363_;
v___y_2885_ = v___y_2364_;
v___y_2886_ = v___y_2365_;
v___y_2887_ = v___y_2366_;
v___y_2888_ = v___y_2367_;
v___y_2889_ = v___y_2368_;
goto v___jp_2874_;
}
}
else
{
lean_object* v___x_2959_; 
lean_dec(v___x_2943_);
v___x_2959_ = lean_box(0);
v___y_2875_ = v___y_2909_;
v___y_2876_ = v___x_2929_;
v___y_2877_ = v___y_2912_;
v___y_2878_ = v_a_2916_;
v___y_2879_ = v___x_2942_;
v___y_2880_ = v___y_2911_;
v_only_2881_ = v___x_2959_;
v___y_2882_ = v___y_2361_;
v___y_2883_ = v___y_2362_;
v___y_2884_ = v___y_2363_;
v___y_2885_ = v___y_2364_;
v___y_2886_ = v___y_2365_;
v___y_2887_ = v___y_2366_;
v___y_2888_ = v___y_2367_;
v___y_2889_ = v___y_2368_;
goto v___jp_2874_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2909_);
lean_dec(v___x_2429_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___x_2351_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v_a_2960_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2915_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2915_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
v___jp_2968_:
{
if (lean_obj_tag(v_usingArg_2352_) == 0)
{
v___y_2909_ = v___y_2969_;
v___y_2910_ = v___y_2970_;
v___y_2911_ = v___y_2971_;
v___y_2912_ = v_usingArg_2352_;
goto v___jp_2908_;
}
else
{
lean_object* v_val_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
v_val_2972_ = lean_ctor_get(v_usingArg_2352_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_usingArg_2352_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2974_ = v_usingArg_2352_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_val_2972_);
lean_dec(v_usingArg_2352_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = l_Lean_Syntax_unsetTrailing(v_val_2972_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
v___y_2909_ = v___y_2969_;
v___y_2910_ = v___y_2970_;
v___y_2911_ = v___y_2971_;
v___y_2912_ = v___x_2978_;
goto v___jp_2908_;
}
}
}
}
v___jp_2981_:
{
if (v___y_2985_ == 0)
{
lean_dec(v___y_2983_);
lean_dec(v___x_2429_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_usingArg_2352_);
lean_dec(v___x_2351_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v___y_2371_ = v___y_2982_;
goto v___jp_2370_;
}
else
{
v___y_2969_ = v___y_2982_;
v___y_2970_ = v___y_2983_;
v___y_2971_ = v___y_2984_;
goto v___jp_2968_;
}
}
v___jp_2986_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___f_2997_; lean_object* v___x_2998_; 
v___x_2992_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_2991_, v___x_2426_);
v___x_2993_ = lean_box(v___x_2341_);
v___x_2994_ = lean_box(v___x_2426_);
v___x_2995_ = lean_box(v_useReducible_2344_);
v___x_2996_ = lean_box(v___x_2354_);
lean_inc(v___x_2349_);
lean_inc_ref(v___x_2346_);
lean_inc(v_usingArg_2352_);
lean_inc(v___x_2340_);
lean_inc(v_tk_2336_);
lean_inc(v___x_2351_);
v___f_2997_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 24, 14);
lean_closure_set(v___f_2997_, 0, v___x_2351_);
lean_closure_set(v___f_2997_, 1, v_tk_2336_);
lean_closure_set(v___f_2997_, 2, v___x_2431_);
lean_closure_set(v___f_2997_, 3, v___x_2340_);
lean_closure_set(v___f_2997_, 4, v___x_2992_);
lean_closure_set(v___f_2997_, 5, v___y_2987_);
lean_closure_set(v___f_2997_, 6, v___x_2993_);
lean_closure_set(v___f_2997_, 7, v_usingArg_2352_);
lean_closure_set(v___f_2997_, 8, v___x_2994_);
lean_closure_set(v___f_2997_, 9, v___x_2346_);
lean_closure_set(v___f_2997_, 10, v___x_2995_);
lean_closure_set(v___f_2997_, 11, v___x_2996_);
lean_closure_set(v___f_2997_, 12, v___x_2349_);
lean_closure_set(v___f_2997_, 13, v_usingTk_x3f_2355_);
v___x_2998_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_2989_, v___f_2997_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2989_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3001_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_2424_, v___x_3000_);
if (v___x_3001_ == 0)
{
if (lean_obj_tag(v_squeeze_2356_) == 0)
{
v___y_2982_ = v_a_2999_;
v___y_2983_ = v___y_2988_;
v___y_2984_ = v___y_2990_;
v___y_2985_ = v___x_3001_;
goto v___jp_2981_;
}
else
{
v___y_2982_ = v_a_2999_;
v___y_2983_ = v___y_2988_;
v___y_2984_ = v___y_2990_;
v___y_2985_ = v___x_2354_;
goto v___jp_2981_;
}
}
else
{
v___y_2969_ = v_a_2999_;
v___y_2970_ = v___y_2988_;
v___y_2971_ = v___y_2990_;
goto v___jp_2968_;
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v___y_2988_);
lean_dec(v___x_2429_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_usingArg_2352_);
lean_dec(v___x_2351_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v_a_3002_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2998_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2998_);
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
v___jp_3010_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3014_ = l_Array_append___redArg(v___x_2432_, v___y_3013_);
lean_dec_ref(v___y_3013_);
lean_inc_n(v___x_2427_, 2);
v___x_3015_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3015_, 0, v___x_2427_);
lean_ctor_set(v___x_3015_, 1, v___x_2431_);
lean_ctor_set(v___x_3015_, 2, v___x_3014_);
v___x_3016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3016_, 0, v___x_2427_);
lean_ctor_set(v___x_3016_, 1, v___x_2431_);
lean_ctor_set(v___x_3016_, 2, v___x_2432_);
lean_inc(v___x_2429_);
v___x_3017_ = l_Lean_Syntax_node6(v___x_2427_, v___x_2429_, v___x_2430_, v___x_2353_, v___y_3012_, v___y_3011_, v___x_3015_, v___x_3016_);
v___x_3018_ = 0;
v___x_3019_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23));
v___x_3020_ = lean_box(v___x_2426_);
v___x_3021_ = lean_box(v___x_3018_);
v___x_3022_ = lean_box(v___x_2426_);
lean_inc(v___x_3017_);
v___x_3023_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3023_, 0, v___x_3017_);
lean_closure_set(v___x_3023_, 1, v___x_3020_);
lean_closure_set(v___x_3023_, 2, v___x_3021_);
lean_closure_set(v___x_3023_, 3, v___x_3022_);
lean_closure_set(v___x_3023_, 4, v___x_3019_);
v___x_3024_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3023_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
if (lean_obj_tag(v_unfold_2357_) == 0)
{
lean_object* v_ctx_3026_; lean_object* v_simprocs_3027_; lean_object* v_dischargeWrapper_3028_; 
v_ctx_3026_ = lean_ctor_get(v_a_3025_, 0);
lean_inc_ref(v_ctx_3026_);
v_simprocs_3027_ = lean_ctor_get(v_a_3025_, 1);
lean_inc_ref(v_simprocs_3027_);
v_dischargeWrapper_3028_ = lean_ctor_get(v_a_3025_, 2);
lean_inc(v_dischargeWrapper_3028_);
lean_dec(v_a_3025_);
v___y_2987_ = v_simprocs_3027_;
v___y_2988_ = v___x_3017_;
v___y_2989_ = v_dischargeWrapper_3028_;
v___y_2990_ = v___x_2426_;
v___y_2991_ = v_ctx_3026_;
goto v___jp_2986_;
}
else
{
if (v___x_2354_ == 0)
{
lean_object* v_ctx_3029_; lean_object* v_simprocs_3030_; lean_object* v_dischargeWrapper_3031_; 
v_ctx_3029_ = lean_ctor_get(v_a_3025_, 0);
lean_inc_ref(v_ctx_3029_);
v_simprocs_3030_ = lean_ctor_get(v_a_3025_, 1);
lean_inc_ref(v_simprocs_3030_);
v_dischargeWrapper_3031_ = lean_ctor_get(v_a_3025_, 2);
lean_inc(v_dischargeWrapper_3031_);
lean_dec(v_a_3025_);
v___y_2987_ = v_simprocs_3030_;
v___y_2988_ = v___x_3017_;
v___y_2989_ = v_dischargeWrapper_3031_;
v___y_2990_ = v___x_2354_;
v___y_2991_ = v_ctx_3029_;
goto v___jp_2986_;
}
else
{
lean_object* v_ctx_3032_; lean_object* v_simprocs_3033_; lean_object* v_dischargeWrapper_3034_; lean_object* v___x_3035_; 
v_ctx_3032_ = lean_ctor_get(v_a_3025_, 0);
lean_inc_ref(v_ctx_3032_);
v_simprocs_3033_ = lean_ctor_get(v_a_3025_, 1);
lean_inc_ref(v_simprocs_3033_);
v_dischargeWrapper_3034_ = lean_ctor_get(v_a_3025_, 2);
lean_inc(v_dischargeWrapper_3034_);
lean_dec(v_a_3025_);
v___x_3035_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3032_);
v___y_2987_ = v_simprocs_3033_;
v___y_2988_ = v___x_3017_;
v___y_2989_ = v_dischargeWrapper_3034_;
v___y_2990_ = v___x_2354_;
v___y_2991_ = v___x_3035_;
goto v___jp_2986_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v___x_3017_);
lean_dec(v___x_2429_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_usingTk_x3f_2355_);
lean_dec(v_usingArg_2352_);
lean_dec(v___x_2351_);
lean_dec(v___x_2349_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___f_2345_);
lean_dec(v___x_2343_);
lean_dec(v___x_2342_);
lean_dec(v___x_2340_);
lean_dec_ref(v___x_2339_);
lean_dec_ref(v___x_2338_);
lean_dec_ref(v___x_2337_);
lean_dec(v_tk_2336_);
v_a_3036_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3024_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3024_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
v___jp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = l_Array_append___redArg(v___x_2432_, v___y_3046_);
lean_dec_ref(v___y_3046_);
lean_inc(v___x_2427_);
v___x_3048_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___x_2427_);
lean_ctor_set(v___x_3048_, 1, v___x_2431_);
lean_ctor_set(v___x_3048_, 2, v___x_3047_);
if (lean_obj_tag(v_args_2358_) == 1)
{
lean_object* v_val_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_val_3049_ = lean_ctor_get(v_args_2358_, 0);
v___x_3050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___x_2427_, 3);
v___x_3051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_2427_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = l_Array_append___redArg(v___x_2432_, v_val_3049_);
v___x_3053_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3053_, 0, v___x_2427_);
lean_ctor_set(v___x_3053_, 1, v___x_2431_);
lean_ctor_set(v___x_3053_, 2, v___x_3052_);
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_2427_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = l_Array_mkArray3___redArg(v___x_3051_, v___x_3053_, v___x_3055_);
v___y_3011_ = v___x_3048_;
v___y_3012_ = v___y_3045_;
v___y_3013_ = v___x_3056_;
goto v___jp_3010_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_3011_ = v___x_3048_;
v___y_3012_ = v___y_3045_;
v___y_3013_ = v___x_3057_;
goto v___jp_3010_;
}
}
v___jp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = l_Array_append___redArg(v___x_2432_, v___y_3059_);
lean_dec_ref(v___y_3059_);
lean_inc(v___x_2427_);
v___x_3061_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3061_, 0, v___x_2427_);
lean_ctor_set(v___x_3061_, 1, v___x_2431_);
lean_ctor_set(v___x_3061_, 2, v___x_3060_);
if (lean_obj_tag(v_only_2359_) == 1)
{
lean_object* v_val_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_val_3062_ = lean_ctor_get(v_only_2359_, 0);
v___x_3063_ = l_Lean_SourceInfo_fromRef(v_val_3062_, v___x_2341_);
v___x_3064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l_Array_mkArray1___redArg(v___x_3065_);
v___y_3045_ = v___x_3061_;
v___y_3046_ = v___x_3066_;
goto v___jp_3044_;
}
else
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___y_3045_ = v___x_3061_;
v___y_3046_ = v___x_3067_;
goto v___jp_3044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v_tk_3072_ = _args[0];
lean_object* v___x_3073_ = _args[1];
lean_object* v___x_3074_ = _args[2];
lean_object* v___x_3075_ = _args[3];
lean_object* v___x_3076_ = _args[4];
lean_object* v___x_3077_ = _args[5];
lean_object* v___x_3078_ = _args[6];
lean_object* v___x_3079_ = _args[7];
lean_object* v_useReducible_3080_ = _args[8];
lean_object* v___f_3081_ = _args[9];
lean_object* v___x_3082_ = _args[10];
lean_object* v___x_3083_ = _args[11];
lean_object* v___x_3084_ = _args[12];
lean_object* v___x_3085_ = _args[13];
lean_object* v___x_3086_ = _args[14];
lean_object* v___x_3087_ = _args[15];
lean_object* v_usingArg_3088_ = _args[16];
lean_object* v___x_3089_ = _args[17];
lean_object* v___x_3090_ = _args[18];
lean_object* v_usingTk_x3f_3091_ = _args[19];
lean_object* v_squeeze_3092_ = _args[20];
lean_object* v_unfold_3093_ = _args[21];
lean_object* v_args_3094_ = _args[22];
lean_object* v_only_3095_ = _args[23];
lean_object* v___y_3096_ = _args[24];
lean_object* v___y_3097_ = _args[25];
lean_object* v___y_3098_ = _args[26];
lean_object* v___y_3099_ = _args[27];
lean_object* v___y_3100_ = _args[28];
lean_object* v___y_3101_ = _args[29];
lean_object* v___y_3102_ = _args[30];
lean_object* v___y_3103_ = _args[31];
lean_object* v___y_3104_ = _args[32];
lean_object* v___y_3105_ = _args[33];
_start:
{
uint8_t v___x_78394__boxed_3106_; uint8_t v_useReducible_boxed_3107_; uint8_t v___x_78405__boxed_3108_; lean_object* v_res_3109_; 
v___x_78394__boxed_3106_ = lean_unbox(v___x_3077_);
v_useReducible_boxed_3107_ = lean_unbox(v_useReducible_3080_);
v___x_78405__boxed_3108_ = lean_unbox(v___x_3090_);
v_res_3109_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v_tk_3072_, v___x_3073_, v___x_3074_, v___x_3075_, v___x_3076_, v___x_78394__boxed_3106_, v___x_3078_, v___x_3079_, v_useReducible_boxed_3107_, v___f_3081_, v___x_3082_, v___x_3083_, v___x_3084_, v___x_3085_, v___x_3086_, v___x_3087_, v_usingArg_3088_, v___x_3089_, v___x_78405__boxed_3108_, v_usingTk_x3f_3091_, v_squeeze_3092_, v_unfold_3093_, v_args_3094_, v_only_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v_only_3095_);
lean_dec(v_args_3094_);
lean_dec(v_unfold_3093_);
lean_dec(v_squeeze_3092_);
lean_dec(v___x_3086_);
lean_dec(v___x_3084_);
lean_dec(v___x_3083_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3135_, lean_object* v_stx_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_));
v___x_3147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3148_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1));
v___x_3149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3136_);
v___x_3151_ = l_Lean_Syntax_isOfKind(v_stx_3136_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec(v_stx_3136_);
v___x_3152_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3152_;
}
else
{
lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v_tk_3155_; lean_object* v___x_3156_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; uint8_t v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; uint8_t v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v_usingTk_x3f_3207_; lean_object* v_usingArg_3208_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; uint8_t v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v_args_3240_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v_only_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v_unfold_3296_; lean_object* v_squeeze_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___f_3153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3154_ = lean_unsigned_to_nat(0u);
v_tk_3155_ = l_Lean_Syntax_getArg(v_stx_3136_, v___x_3154_);
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3332_ = l_Lean_Syntax_getArg(v_stx_3136_, v___x_3156_);
v___x_3333_ = l_Lean_Syntax_isNone(v___x_3332_);
if (v___x_3333_ == 0)
{
uint8_t v___x_3334_; 
lean_inc(v___x_3332_);
v___x_3334_ = l_Lean_Syntax_matchesNull(v___x_3332_, v___x_3156_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
lean_dec(v___x_3332_);
lean_dec(v_tk_3155_);
lean_dec(v_stx_3136_);
v___x_3335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3335_;
}
else
{
lean_object* v_squeeze_3336_; lean_object* v___x_3337_; 
v_squeeze_3336_ = l_Lean_Syntax_getArg(v___x_3332_, v___x_3154_);
lean_dec(v___x_3332_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_squeeze_3336_);
v_squeeze_3315_ = v___x_3337_;
v___y_3316_ = v_a_3137_;
v___y_3317_ = v_a_3138_;
v___y_3318_ = v_a_3139_;
v___y_3319_ = v_a_3140_;
v___y_3320_ = v_a_3141_;
v___y_3321_ = v_a_3142_;
v___y_3322_ = v_a_3143_;
v___y_3323_ = v_a_3144_;
goto v___jp_3314_;
}
}
else
{
lean_object* v___x_3338_; 
lean_dec(v___x_3332_);
v___x_3338_ = lean_box(0);
v_squeeze_3315_ = v___x_3338_;
v___y_3316_ = v_a_3137_;
v___y_3317_ = v_a_3138_;
v___y_3318_ = v_a_3139_;
v___y_3319_ = v_a_3140_;
v___y_3320_ = v_a_3141_;
v___y_3321_ = v_a_3142_;
v___y_3322_ = v_a_3143_;
v___y_3323_ = v_a_3144_;
goto v___jp_3314_;
}
v___jp_3157_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___f_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3180_ = lean_box(v___x_3151_);
v___x_3181_ = lean_box(v_useReducible_3135_);
v___x_3182_ = lean_box(v___y_3172_);
lean_inc(v___y_3173_);
lean_inc(v___y_3170_);
v___f_3183_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 34, 25);
lean_closure_set(v___f_3183_, 0, v_tk_3155_);
lean_closure_set(v___f_3183_, 1, v___x_3146_);
lean_closure_set(v___f_3183_, 2, v___x_3147_);
lean_closure_set(v___f_3183_, 3, v___x_3148_);
lean_closure_set(v___f_3183_, 4, v___x_3154_);
lean_closure_set(v___f_3183_, 5, v___x_3180_);
lean_closure_set(v___f_3183_, 6, v___y_3170_);
lean_closure_set(v___f_3183_, 7, v___x_3150_);
lean_closure_set(v___f_3183_, 8, v___x_3181_);
lean_closure_set(v___f_3183_, 9, v___f_3153_);
lean_closure_set(v___f_3183_, 10, v___x_3149_);
lean_closure_set(v___f_3183_, 11, v___y_3167_);
lean_closure_set(v___f_3183_, 12, v___y_3164_);
lean_closure_set(v___f_3183_, 13, v___x_3156_);
lean_closure_set(v___f_3183_, 14, v___y_3173_);
lean_closure_set(v___f_3183_, 15, v___y_3158_);
lean_closure_set(v___f_3183_, 16, v___y_3176_);
lean_closure_set(v___f_3183_, 17, v___y_3171_);
lean_closure_set(v___f_3183_, 18, v___x_3182_);
lean_closure_set(v___f_3183_, 19, v___y_3177_);
lean_closure_set(v___f_3183_, 20, v___y_3159_);
lean_closure_set(v___f_3183_, 21, v___y_3160_);
lean_closure_set(v___f_3183_, 22, v___y_3161_);
lean_closure_set(v___f_3183_, 23, v___y_3178_);
lean_closure_set(v___f_3183_, 24, v___y_3179_);
v___x_3184_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3184_, 0, v___f_3183_);
v___x_3185_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3184_, v___y_3165_, v___y_3175_, v___y_3166_, v___y_3162_, v___y_3163_, v___y_3174_, v___y_3168_, v___y_3169_);
return v___x_3185_;
}
v___jp_3186_:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_Syntax_getOptional_x3f(v___y_3187_);
lean_dec(v___y_3187_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_box(0);
v___y_3158_ = v___y_3188_;
v___y_3159_ = v___y_3189_;
v___y_3160_ = v___y_3190_;
v___y_3161_ = v___y_3191_;
v___y_3162_ = v___y_3192_;
v___y_3163_ = v___y_3193_;
v___y_3164_ = v___y_3194_;
v___y_3165_ = v___y_3195_;
v___y_3166_ = v___y_3196_;
v___y_3167_ = v___y_3197_;
v___y_3168_ = v___y_3198_;
v___y_3169_ = v___y_3199_;
v___y_3170_ = v___y_3200_;
v___y_3171_ = v___y_3201_;
v___y_3172_ = v___y_3202_;
v___y_3173_ = v___y_3203_;
v___y_3174_ = v___y_3205_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v_usingArg_3208_;
v___y_3177_ = v_usingTk_x3f_3207_;
v___y_3178_ = v___y_3206_;
v___y_3179_ = v___x_3210_;
goto v___jp_3157_;
}
else
{
lean_object* v_val_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
v_val_3211_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3209_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_val_3211_);
lean_dec(v___x_3209_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_val_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
v___y_3158_ = v___y_3188_;
v___y_3159_ = v___y_3189_;
v___y_3160_ = v___y_3190_;
v___y_3161_ = v___y_3191_;
v___y_3162_ = v___y_3192_;
v___y_3163_ = v___y_3193_;
v___y_3164_ = v___y_3194_;
v___y_3165_ = v___y_3195_;
v___y_3166_ = v___y_3196_;
v___y_3167_ = v___y_3197_;
v___y_3168_ = v___y_3198_;
v___y_3169_ = v___y_3199_;
v___y_3170_ = v___y_3200_;
v___y_3171_ = v___y_3201_;
v___y_3172_ = v___y_3202_;
v___y_3173_ = v___y_3203_;
v___y_3174_ = v___y_3205_;
v___y_3175_ = v___y_3204_;
v___y_3176_ = v_usingArg_3208_;
v___y_3177_ = v_usingTk_x3f_3207_;
v___y_3178_ = v___y_3206_;
v___y_3179_ = v___x_3216_;
goto v___jp_3157_;
}
}
}
}
v___jp_3219_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3241_ = lean_unsigned_to_nat(4u);
v___x_3242_ = l_Lean_Syntax_getArg(v___y_3224_, v___x_3241_);
lean_dec(v___y_3224_);
v___x_3243_ = l_Lean_Syntax_isNone(v___x_3242_);
if (v___x_3243_ == 0)
{
uint8_t v___x_3244_; 
lean_inc(v___x_3242_);
v___x_3244_ = l_Lean_Syntax_matchesNull(v___x_3242_, v___y_3223_);
lean_dec(v___y_3223_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
lean_dec(v___x_3242_);
lean_dec(v_args_3240_);
lean_dec(v___y_3239_);
lean_dec(v___y_3234_);
lean_dec(v___y_3228_);
lean_dec(v___y_3225_);
lean_dec(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec(v_tk_3155_);
v___x_3245_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3245_;
}
else
{
lean_object* v_usingTk_x3f_3246_; lean_object* v_usingArg_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_usingTk_x3f_3246_ = l_Lean_Syntax_getArg(v___x_3242_, v___x_3154_);
v_usingArg_3247_ = l_Lean_Syntax_getArg(v___x_3242_, v___x_3156_);
lean_dec(v___x_3242_);
v___x_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_usingTk_x3f_3246_);
v___x_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3249_, 0, v_usingArg_3247_);
v___y_3187_ = v___y_3220_;
v___y_3188_ = v___y_3221_;
v___y_3189_ = v___y_3222_;
v___y_3190_ = v___y_3225_;
v___y_3191_ = v_args_3240_;
v___y_3192_ = v___y_3226_;
v___y_3193_ = v___y_3227_;
v___y_3194_ = v___y_3228_;
v___y_3195_ = v___y_3229_;
v___y_3196_ = v___y_3230_;
v___y_3197_ = v___x_3241_;
v___y_3198_ = v___y_3231_;
v___y_3199_ = v___y_3232_;
v___y_3200_ = v___y_3233_;
v___y_3201_ = v___y_3234_;
v___y_3202_ = v___y_3235_;
v___y_3203_ = v___y_3236_;
v___y_3204_ = v___y_3238_;
v___y_3205_ = v___y_3237_;
v___y_3206_ = v___y_3239_;
v_usingTk_x3f_3207_ = v___x_3248_;
v_usingArg_3208_ = v___x_3249_;
goto v___jp_3186_;
}
}
else
{
lean_object* v___x_3250_; 
lean_dec(v___x_3242_);
lean_dec(v___y_3223_);
v___x_3250_ = lean_box(0);
v___y_3187_ = v___y_3220_;
v___y_3188_ = v___y_3221_;
v___y_3189_ = v___y_3222_;
v___y_3190_ = v___y_3225_;
v___y_3191_ = v_args_3240_;
v___y_3192_ = v___y_3226_;
v___y_3193_ = v___y_3227_;
v___y_3194_ = v___y_3228_;
v___y_3195_ = v___y_3229_;
v___y_3196_ = v___y_3230_;
v___y_3197_ = v___x_3241_;
v___y_3198_ = v___y_3231_;
v___y_3199_ = v___y_3232_;
v___y_3200_ = v___y_3233_;
v___y_3201_ = v___y_3234_;
v___y_3202_ = v___y_3235_;
v___y_3203_ = v___y_3236_;
v___y_3204_ = v___y_3238_;
v___y_3205_ = v___y_3237_;
v___y_3206_ = v___y_3239_;
v_usingTk_x3f_3207_ = v___x_3250_;
v_usingArg_3208_ = v___x_3250_;
goto v___jp_3186_;
}
}
v___jp_3251_:
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = l_Lean_Syntax_getArg(v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
v___x_3274_ = l_Lean_Syntax_isNone(v___x_3273_);
if (v___x_3274_ == 0)
{
uint8_t v___x_3275_; 
lean_inc(v___x_3273_);
v___x_3275_ = l_Lean_Syntax_matchesNull(v___x_3273_, v___x_3156_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; 
lean_dec(v___x_3273_);
lean_dec(v_only_3264_);
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v_tk_3155_);
v___x_3276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3276_;
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3277_ = l_Lean_Syntax_getArg(v___x_3273_, v___x_3154_);
lean_dec(v___x_3273_);
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3277_);
v___x_3279_ = l_Lean_Syntax_isOfKind(v___x_3277_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
lean_dec(v___x_3277_);
lean_dec(v_only_3264_);
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v_tk_3155_);
v___x_3280_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; lean_object* v_args_3282_; lean_object* v___x_3283_; 
v___x_3281_ = l_Lean_Syntax_getArg(v___x_3277_, v___x_3156_);
lean_dec(v___x_3277_);
v_args_3282_ = l_Lean_Syntax_getArgs(v___x_3281_);
lean_dec(v___x_3281_);
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v_args_3282_);
v___y_3220_ = v___y_3263_;
v___y_3221_ = v___y_3252_;
v___y_3222_ = v___y_3253_;
v___y_3223_ = v___y_3260_;
v___y_3224_ = v___y_3261_;
v___y_3225_ = v___y_3256_;
v___y_3226_ = v___y_3268_;
v___y_3227_ = v___y_3269_;
v___y_3228_ = v___y_3259_;
v___y_3229_ = v___y_3265_;
v___y_3230_ = v___y_3267_;
v___y_3231_ = v___y_3271_;
v___y_3232_ = v___y_3272_;
v___y_3233_ = v___y_3254_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___y_3257_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3270_;
v___y_3238_ = v___y_3266_;
v___y_3239_ = v_only_3264_;
v_args_3240_ = v___x_3283_;
goto v___jp_3219_;
}
}
}
else
{
lean_object* v___x_3284_; 
lean_dec(v___x_3273_);
v___x_3284_ = lean_box(0);
v___y_3220_ = v___y_3263_;
v___y_3221_ = v___y_3252_;
v___y_3222_ = v___y_3253_;
v___y_3223_ = v___y_3260_;
v___y_3224_ = v___y_3261_;
v___y_3225_ = v___y_3256_;
v___y_3226_ = v___y_3268_;
v___y_3227_ = v___y_3269_;
v___y_3228_ = v___y_3259_;
v___y_3229_ = v___y_3265_;
v___y_3230_ = v___y_3267_;
v___y_3231_ = v___y_3271_;
v___y_3232_ = v___y_3272_;
v___y_3233_ = v___y_3254_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___y_3257_;
v___y_3236_ = v___y_3258_;
v___y_3237_ = v___y_3270_;
v___y_3238_ = v___y_3266_;
v___y_3239_ = v_only_3264_;
v_args_3240_ = v___x_3284_;
goto v___jp_3219_;
}
}
v___jp_3285_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3297_ = lean_unsigned_to_nat(3u);
v___x_3298_ = l_Lean_Syntax_getArg(v_stx_3136_, v___x_3297_);
lean_dec(v_stx_3136_);
v___x_3299_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3298_);
v___x_3300_ = l_Lean_Syntax_isOfKind(v___x_3298_, v___x_3299_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; 
lean_dec(v___x_3298_);
lean_dec(v_unfold_3296_);
lean_dec(v___y_3289_);
lean_dec(v___y_3287_);
lean_dec(v_tk_3155_);
v___x_3301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3302_ = l_Lean_Syntax_getArg(v___x_3298_, v___x_3154_);
v___x_3303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3302_);
v___x_3304_ = l_Lean_Syntax_isOfKind(v___x_3302_, v___x_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
lean_dec(v___x_3302_);
lean_dec(v___x_3298_);
lean_dec(v_unfold_3296_);
lean_dec(v___y_3289_);
lean_dec(v___y_3287_);
lean_dec(v_tk_3155_);
v___x_3305_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3305_;
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3306_ = l_Lean_Syntax_getArg(v___x_3298_, v___x_3156_);
v___x_3307_ = l_Lean_Syntax_getArg(v___x_3298_, v___y_3287_);
v___x_3308_ = l_Lean_Syntax_isNone(v___x_3307_);
if (v___x_3308_ == 0)
{
uint8_t v___x_3309_; 
lean_inc(v___x_3307_);
v___x_3309_ = l_Lean_Syntax_matchesNull(v___x_3307_, v___x_3156_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; 
lean_dec(v___x_3307_);
lean_dec(v___x_3306_);
lean_dec(v___x_3302_);
lean_dec(v___x_3298_);
lean_dec(v_unfold_3296_);
lean_dec(v___y_3289_);
lean_dec(v___y_3287_);
lean_dec(v_tk_3155_);
v___x_3310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3310_;
}
else
{
lean_object* v_only_3311_; lean_object* v___x_3312_; 
v_only_3311_ = l_Lean_Syntax_getArg(v___x_3307_, v___x_3154_);
lean_dec(v___x_3307_);
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_only_3311_);
lean_inc(v___y_3287_);
v___y_3252_ = v___y_3287_;
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___x_3299_;
v___y_3255_ = v___x_3302_;
v___y_3256_ = v_unfold_3296_;
v___y_3257_ = v___x_3300_;
v___y_3258_ = v___x_3303_;
v___y_3259_ = v___x_3297_;
v___y_3260_ = v___y_3287_;
v___y_3261_ = v___x_3298_;
v___y_3262_ = v___x_3297_;
v___y_3263_ = v___x_3306_;
v_only_3264_ = v___x_3312_;
v___y_3265_ = v___y_3288_;
v___y_3266_ = v___y_3286_;
v___y_3267_ = v___y_3295_;
v___y_3268_ = v___y_3294_;
v___y_3269_ = v___y_3290_;
v___y_3270_ = v___y_3291_;
v___y_3271_ = v___y_3293_;
v___y_3272_ = v___y_3292_;
goto v___jp_3251_;
}
}
else
{
lean_object* v___x_3313_; 
lean_dec(v___x_3307_);
v___x_3313_ = lean_box(0);
lean_inc(v___y_3287_);
v___y_3252_ = v___y_3287_;
v___y_3253_ = v___y_3289_;
v___y_3254_ = v___x_3299_;
v___y_3255_ = v___x_3302_;
v___y_3256_ = v_unfold_3296_;
v___y_3257_ = v___x_3300_;
v___y_3258_ = v___x_3303_;
v___y_3259_ = v___x_3297_;
v___y_3260_ = v___y_3287_;
v___y_3261_ = v___x_3298_;
v___y_3262_ = v___x_3297_;
v___y_3263_ = v___x_3306_;
v_only_3264_ = v___x_3313_;
v___y_3265_ = v___y_3288_;
v___y_3266_ = v___y_3286_;
v___y_3267_ = v___y_3295_;
v___y_3268_ = v___y_3294_;
v___y_3269_ = v___y_3290_;
v___y_3270_ = v___y_3291_;
v___y_3271_ = v___y_3293_;
v___y_3272_ = v___y_3292_;
goto v___jp_3251_;
}
}
}
}
v___jp_3314_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3324_ = lean_unsigned_to_nat(2u);
v___x_3325_ = l_Lean_Syntax_getArg(v_stx_3136_, v___x_3324_);
v___x_3326_ = l_Lean_Syntax_isNone(v___x_3325_);
if (v___x_3326_ == 0)
{
uint8_t v___x_3327_; 
lean_inc(v___x_3325_);
v___x_3327_ = l_Lean_Syntax_matchesNull(v___x_3325_, v___x_3156_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
lean_dec(v___x_3325_);
lean_dec(v_squeeze_3315_);
lean_dec(v_tk_3155_);
lean_dec(v_stx_3136_);
v___x_3328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3328_;
}
else
{
lean_object* v_unfold_3329_; lean_object* v___x_3330_; 
v_unfold_3329_ = l_Lean_Syntax_getArg(v___x_3325_, v___x_3154_);
lean_dec(v___x_3325_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_unfold_3329_);
v___y_3286_ = v___y_3317_;
v___y_3287_ = v___x_3324_;
v___y_3288_ = v___y_3316_;
v___y_3289_ = v_squeeze_3315_;
v___y_3290_ = v___y_3320_;
v___y_3291_ = v___y_3321_;
v___y_3292_ = v___y_3323_;
v___y_3293_ = v___y_3322_;
v___y_3294_ = v___y_3319_;
v___y_3295_ = v___y_3318_;
v_unfold_3296_ = v___x_3330_;
goto v___jp_3285_;
}
}
else
{
lean_object* v___x_3331_; 
lean_dec(v___x_3325_);
v___x_3331_ = lean_box(0);
v___y_3286_ = v___y_3317_;
v___y_3287_ = v___x_3324_;
v___y_3288_ = v___y_3316_;
v___y_3289_ = v_squeeze_3315_;
v___y_3290_ = v___y_3320_;
v___y_3291_ = v___y_3321_;
v___y_3292_ = v___y_3323_;
v___y_3293_ = v___y_3322_;
v___y_3294_ = v___y_3319_;
v___y_3295_ = v___y_3318_;
v_unfold_3296_ = v___x_3331_;
goto v___jp_3285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3339_, lean_object* v_stx_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
uint8_t v_useReducible_boxed_3350_; lean_object* v_res_3351_; 
v_useReducible_boxed_3350_ = lean_unbox(v_useReducible_3339_);
v_res_3351_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3350_, v_stx_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3352_, lean_object* v_val_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3352_, v_val_3353_, v___y_3359_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3364_, lean_object* v_val_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3364_, v_val_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3376_, v___y_3384_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v_00_u03b1_3398_, lean_object* v_msg_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_3399_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v_00_u03b1_3410_, lean_object* v_msg_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_3410_, v_msg_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_00_u03b1_3422_, lean_object* v_x_3423_, lean_object* v_mkInfoTree_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_3423_, v_mkInfoTree_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_00_u03b1_3435_, lean_object* v_x_3436_, lean_object* v_mkInfoTree_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_3435_, v_x_3436_, v_mkInfoTree_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_, lean_object* v_x_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3449_, v_x_3450_, v_x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3453_, lean_object* v_m_3454_, lean_object* v_a_3455_){
_start:
{
uint8_t v___x_3456_; 
v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3454_, v_a_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_3457_, lean_object* v_m_3458_, lean_object* v_a_3459_){
_start:
{
uint8_t v_res_3460_; lean_object* v_r_3461_; 
v_res_3460_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_3457_, v_m_3458_, v_a_3459_);
lean_dec_ref(v_a_3459_);
lean_dec_ref(v_m_3458_);
v_r_3461_ = lean_box(v_res_3460_);
return v_r_3461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_3462_, lean_object* v_m_3463_, lean_object* v_a_3464_, lean_object* v_b_3465_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_m_3463_, v_a_3464_, v_b_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(lean_object* v_mvarId_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_3467_, v___y_3468_, v___y_3474_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(lean_object* v_mvarId_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(v_mvarId_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v_mvarId_3479_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(lean_object* v_mvarId_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_3491_, v___y_3492_, v___y_3498_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(lean_object* v_mvarId_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_mvarId_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v_mvarId_3503_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(lean_object* v_00_u03b2_3515_, lean_object* v_x_3516_, size_t v_x_3517_, size_t v_x_3518_, lean_object* v_x_3519_, lean_object* v_x_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_3516_, v_x_3517_, v_x_3518_, v_x_3519_, v_x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b2_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_, lean_object* v_x_3525_, lean_object* v_x_3526_, lean_object* v_x_3527_){
_start:
{
size_t v_x_80607__boxed_3528_; size_t v_x_80608__boxed_3529_; lean_object* v_res_3530_; 
v_x_80607__boxed_3528_ = lean_unbox_usize(v_x_3524_);
lean_dec(v_x_3524_);
v_x_80608__boxed_3529_ = lean_unbox_usize(v_x_3525_);
lean_dec(v_x_3525_);
v_res_3530_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_3522_, v_x_3523_, v_x_80607__boxed_3528_, v_x_80608__boxed_3529_, v_x_3526_, v_x_3527_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(lean_object* v_ref_3531_, lean_object* v_msgData_3532_, uint8_t v_severity_3533_, uint8_t v_isSilent_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_3531_, v_msgData_3532_, v_severity_3533_, v_isSilent_3534_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(lean_object* v_ref_3545_, lean_object* v_msgData_3546_, lean_object* v_severity_3547_, lean_object* v_isSilent_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
uint8_t v_severity_boxed_3558_; uint8_t v_isSilent_boxed_3559_; lean_object* v_res_3560_; 
v_severity_boxed_3558_ = lean_unbox(v_severity_3547_);
v_isSilent_boxed_3559_ = lean_unbox(v_isSilent_3548_);
v_res_3560_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(v_ref_3545_, v_msgData_3546_, v_severity_boxed_3558_, v_isSilent_boxed_3559_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v_ref_3545_);
return v_res_3560_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_3561_, lean_object* v_a_3562_, lean_object* v_x_3563_){
_start:
{
uint8_t v___x_3564_; 
v___x_3564_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_3562_, v_x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_3565_, lean_object* v_a_3566_, lean_object* v_x_3567_){
_start:
{
uint8_t v_res_3568_; lean_object* v_r_3569_; 
v_res_3568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_3565_, v_a_3566_, v_x_3567_);
lean_dec(v_x_3567_);
lean_dec_ref(v_a_3566_);
v_r_3569_ = lean_box(v_res_3568_);
return v_r_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_00_u03b2_3570_, lean_object* v_data_3571_){
_start:
{
lean_object* v___x_3572_; 
v___x_3572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_data_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(lean_object* v_00_u03b2_3573_, lean_object* v_n_3574_, lean_object* v_k_3575_, lean_object* v_v_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v_n_3574_, v_k_3575_, v_v_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(lean_object* v_00_u03b2_3578_, size_t v_depth_3579_, lean_object* v_keys_3580_, lean_object* v_vals_3581_, lean_object* v_heq_3582_, lean_object* v_i_3583_, lean_object* v_entries_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_3579_, v_keys_3580_, v_vals_3581_, v_i_3583_, v_entries_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(lean_object* v_00_u03b2_3586_, lean_object* v_depth_3587_, lean_object* v_keys_3588_, lean_object* v_vals_3589_, lean_object* v_heq_3590_, lean_object* v_i_3591_, lean_object* v_entries_3592_){
_start:
{
size_t v_depth_boxed_3593_; lean_object* v_res_3594_; 
v_depth_boxed_3593_ = lean_unbox_usize(v_depth_3587_);
lean_dec(v_depth_3587_);
v_res_3594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_3586_, v_depth_boxed_3593_, v_keys_3588_, v_vals_3589_, v_heq_3590_, v_i_3591_, v_entries_3592_);
lean_dec_ref(v_vals_3589_);
lean_dec_ref(v_keys_3588_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(lean_object* v_00_u03b2_3595_, lean_object* v_i_3596_, lean_object* v_source_3597_, lean_object* v_target_3598_){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_3596_, v_source_3597_, v_target_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(lean_object* v_00_u03b2_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_3601_, v_x_3602_, v_x_3603_, v_x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(lean_object* v_00_u03b2_3606_, lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_3607_, v_x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
uint8_t v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = 1;
v___x_3621_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_3620_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3642_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3645_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_3646_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3642_, v___x_3643_, v___x_3644_, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_3676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_3677_ = l_Lean_addBuiltinDeclarationRanges(v___x_3675_, v___x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_3684_);
lean_dec(v_x_3684_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; uint8_t v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v___x_3738_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_3697_);
v___x_3739_ = l_Lean_Syntax_isOfKind(v_stx_3697_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; 
lean_dec(v_stx_3697_);
v___x_3740_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3740_;
}
else
{
lean_object* v___x_3741_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; uint8_t v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; uint8_t v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; uint8_t v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v_tk_3868_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v_args_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___x_3928_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v_only_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v_unfold_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v_squeeze_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_3741_ = lean_unsigned_to_nat(0u);
v_tk_3868_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3741_);
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_4004_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3928_);
v___x_4005_ = l_Lean_Syntax_isNone(v___x_4004_);
if (v___x_4005_ == 0)
{
uint8_t v___x_4006_; 
lean_inc(v___x_4004_);
v___x_4006_ = l_Lean_Syntax_matchesNull(v___x_4004_, v___x_3928_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; 
lean_dec(v___x_4004_);
lean_dec(v_tk_3868_);
lean_dec(v_stx_3697_);
v___x_4007_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4007_;
}
else
{
lean_object* v_squeeze_4008_; lean_object* v___x_4009_; 
v_squeeze_4008_ = l_Lean_Syntax_getArg(v___x_4004_, v___x_3741_);
lean_dec(v___x_4004_);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v_squeeze_4008_);
v_squeeze_3987_ = v___x_4009_;
v___y_3988_ = v_a_3698_;
v___y_3989_ = v_a_3699_;
v___y_3990_ = v_a_3700_;
v___y_3991_ = v_a_3701_;
v___y_3992_ = v_a_3702_;
v___y_3993_ = v_a_3703_;
v___y_3994_ = v_a_3704_;
v___y_3995_ = v_a_3705_;
goto v___jp_3986_;
}
}
else
{
lean_object* v___x_4010_; 
lean_dec(v___x_4004_);
v___x_4010_ = lean_box(0);
v_squeeze_3987_ = v___x_4010_;
v___y_3988_ = v_a_3698_;
v___y_3989_ = v_a_3699_;
v___y_3990_ = v_a_3700_;
v___y_3991_ = v_a_3701_;
v___y_3992_ = v_a_3702_;
v___y_3993_ = v_a_3703_;
v___y_3994_ = v_a_3704_;
v___y_3995_ = v_a_3705_;
goto v___jp_3986_;
}
v___jp_3742_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_inc_ref(v___y_3756_);
v___x_3765_ = l_Array_append___redArg(v___y_3756_, v___y_3764_);
lean_dec_ref(v___y_3764_);
lean_inc(v___y_3760_);
lean_inc(v___y_3747_);
v___x_3766_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3766_, 0, v___y_3747_);
lean_ctor_set(v___x_3766_, 1, v___y_3760_);
lean_ctor_set(v___x_3766_, 2, v___x_3765_);
if (lean_obj_tag(v___y_3752_) == 1)
{
lean_object* v_val_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_val_3767_ = lean_ctor_get(v___y_3752_, 0);
lean_inc(v_val_3767_);
lean_dec_ref_known(v___y_3752_, 1);
v___x_3768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13));
lean_inc_n(v___y_3747_, 4);
v___x_3770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___y_3747_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
lean_inc_ref(v___y_3756_);
v___x_3771_ = l_Array_append___redArg(v___y_3756_, v_val_3767_);
lean_dec(v_val_3767_);
lean_inc(v___y_3760_);
v___x_3772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3772_, 0, v___y_3747_);
lean_ctor_set(v___x_3772_, 1, v___y_3760_);
lean_ctor_set(v___x_3772_, 2, v___x_3771_);
v___x_3773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14));
v___x_3774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___y_3747_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = l_Lean_Syntax_node3(v___y_3747_, v___x_3768_, v___x_3770_, v___x_3772_, v___x_3774_);
v___x_3776_ = l_Array_mkArray1___redArg(v___x_3775_);
v___y_3708_ = v___y_3743_;
v___y_3709_ = v___y_3744_;
v___y_3710_ = v___y_3745_;
v___y_3711_ = v___y_3746_;
v___y_3712_ = v___y_3747_;
v___y_3713_ = v___y_3748_;
v___y_3714_ = v___y_3749_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v___y_3751_;
v___y_3717_ = v___y_3753_;
v___y_3718_ = v___y_3754_;
v___y_3719_ = v___y_3756_;
v___y_3720_ = v___y_3755_;
v___y_3721_ = v___y_3757_;
v___y_3722_ = v___y_3758_;
v___y_3723_ = v___y_3760_;
v___y_3724_ = v___y_3759_;
v___y_3725_ = v___y_3761_;
v___y_3726_ = v___y_3763_;
v___y_3727_ = v___x_3766_;
v___y_3728_ = v___y_3762_;
v___y_3729_ = v___x_3776_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3777_; 
lean_dec(v___y_3752_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3708_ = v___y_3743_;
v___y_3709_ = v___y_3744_;
v___y_3710_ = v___y_3745_;
v___y_3711_ = v___y_3746_;
v___y_3712_ = v___y_3747_;
v___y_3713_ = v___y_3748_;
v___y_3714_ = v___y_3749_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v___y_3751_;
v___y_3717_ = v___y_3753_;
v___y_3718_ = v___y_3754_;
v___y_3719_ = v___y_3756_;
v___y_3720_ = v___y_3755_;
v___y_3721_ = v___y_3757_;
v___y_3722_ = v___y_3758_;
v___y_3723_ = v___y_3760_;
v___y_3724_ = v___y_3759_;
v___y_3725_ = v___y_3761_;
v___y_3726_ = v___y_3763_;
v___y_3727_ = v___x_3766_;
v___y_3728_ = v___y_3762_;
v___y_3729_ = v___x_3777_;
goto v___jp_3707_;
}
}
v___jp_3778_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_inc_ref(v___y_3791_);
v___x_3801_ = l_Array_append___redArg(v___y_3791_, v___y_3800_);
lean_dec_ref(v___y_3800_);
lean_inc(v___y_3795_);
lean_inc(v___y_3782_);
v___x_3802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3802_, 0, v___y_3782_);
lean_ctor_set(v___x_3802_, 1, v___y_3795_);
lean_ctor_set(v___x_3802_, 2, v___x_3801_);
if (lean_obj_tag(v___y_3797_) == 1)
{
lean_object* v_val_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v_val_3803_ = lean_ctor_get(v___y_3797_, 0);
lean_inc(v_val_3803_);
lean_dec_ref_known(v___y_3797_, 1);
v___x_3804_ = l_Lean_SourceInfo_fromRef(v_val_3803_, v___x_3739_);
lean_dec(v_val_3803_);
v___x_3805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15));
v___x_3806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = l_Array_mkArray1___redArg(v___x_3806_);
v___y_3743_ = v___y_3779_;
v___y_3744_ = v___x_3802_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3782_;
v___y_3748_ = v___y_3783_;
v___y_3749_ = v___y_3784_;
v___y_3750_ = v___y_3785_;
v___y_3751_ = v___y_3786_;
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
v___y_3764_ = v___x_3807_;
goto v___jp_3742_;
}
else
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3797_);
lean_dec(v___y_3797_);
v___y_3743_ = v___y_3779_;
v___y_3744_ = v___x_3802_;
v___y_3745_ = v___y_3780_;
v___y_3746_ = v___y_3781_;
v___y_3747_ = v___y_3782_;
v___y_3748_ = v___y_3783_;
v___y_3749_ = v___y_3784_;
v___y_3750_ = v___y_3785_;
v___y_3751_ = v___y_3786_;
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
v___y_3764_ = v___x_3808_;
goto v___jp_3742_;
}
}
v___jp_3809_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_inc_ref(v___y_3821_);
v___x_3831_ = l_Array_append___redArg(v___y_3821_, v___y_3830_);
lean_dec_ref(v___y_3830_);
lean_inc(v___y_3826_);
lean_inc(v___y_3813_);
v___x_3832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3832_, 0, v___y_3813_);
lean_ctor_set(v___x_3832_, 1, v___y_3826_);
lean_ctor_set(v___x_3832_, 2, v___x_3831_);
v___x_3833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_3815_) == 0)
{
lean_object* v___x_3834_; 
v___x_3834_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_3779_ = v___y_3810_;
v___y_3780_ = v___y_3811_;
v___y_3781_ = v___y_3812_;
v___y_3782_ = v___y_3813_;
v___y_3783_ = v___x_3833_;
v___y_3784_ = v___y_3814_;
v___y_3785_ = v___y_3816_;
v___y_3786_ = v___y_3817_;
v___y_3787_ = v___y_3818_;
v___y_3788_ = v___y_3819_;
v___y_3789_ = v___y_3820_;
v___y_3790_ = v___y_3822_;
v___y_3791_ = v___y_3821_;
v___y_3792_ = v___y_3823_;
v___y_3793_ = v___y_3824_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v___y_3826_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3829_;
v___y_3798_ = v___y_3828_;
v___y_3799_ = v___x_3832_;
v___y_3800_ = v___x_3834_;
goto v___jp_3778_;
}
else
{
lean_object* v_val_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v_val_3835_ = lean_ctor_get(v___y_3815_, 0);
lean_inc(v_val_3835_);
lean_dec_ref_known(v___y_3815_, 1);
v___x_3836_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_3837_ = lean_array_push(v___x_3836_, v_val_3835_);
v___y_3779_ = v___y_3810_;
v___y_3780_ = v___y_3811_;
v___y_3781_ = v___y_3812_;
v___y_3782_ = v___y_3813_;
v___y_3783_ = v___x_3833_;
v___y_3784_ = v___y_3814_;
v___y_3785_ = v___y_3816_;
v___y_3786_ = v___y_3817_;
v___y_3787_ = v___y_3818_;
v___y_3788_ = v___y_3819_;
v___y_3789_ = v___y_3820_;
v___y_3790_ = v___y_3822_;
v___y_3791_ = v___y_3821_;
v___y_3792_ = v___y_3823_;
v___y_3793_ = v___y_3824_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v___y_3826_;
v___y_3796_ = v___y_3827_;
v___y_3797_ = v___y_3829_;
v___y_3798_ = v___y_3828_;
v___y_3799_ = v___x_3832_;
v___y_3800_ = v___x_3837_;
goto v___jp_3778_;
}
}
v___jp_3838_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
lean_inc_ref(v___y_3851_);
v___x_3860_ = l_Array_append___redArg(v___y_3851_, v___y_3859_);
lean_dec_ref(v___y_3859_);
lean_inc(v___y_3854_);
lean_inc(v___y_3842_);
v___x_3861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3861_, 0, v___y_3842_);
lean_ctor_set(v___x_3861_, 1, v___y_3854_);
lean_ctor_set(v___x_3861_, 2, v___x_3860_);
if (lean_obj_tag(v___y_3855_) == 1)
{
lean_object* v_val_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_val_3862_ = lean_ctor_get(v___y_3855_, 0);
lean_inc(v_val_3862_);
lean_dec_ref_known(v___y_3855_, 1);
v___x_3863_ = l_Lean_SourceInfo_fromRef(v_val_3862_, v___x_3739_);
lean_dec(v_val_3862_);
v___x_3864_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19));
v___x_3865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3863_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = l_Array_mkArray1___redArg(v___x_3865_);
v___y_3810_ = v___y_3839_;
v___y_3811_ = v___y_3840_;
v___y_3812_ = v___y_3841_;
v___y_3813_ = v___y_3842_;
v___y_3814_ = v___y_3843_;
v___y_3815_ = v___y_3844_;
v___y_3816_ = v___y_3845_;
v___y_3817_ = v___y_3846_;
v___y_3818_ = v___y_3847_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3851_;
v___y_3822_ = v___y_3850_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3853_;
v___y_3825_ = v___x_3861_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3857_;
v___y_3830_ = v___x_3866_;
goto v___jp_3809_;
}
else
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3855_);
lean_dec(v___y_3855_);
v___y_3810_ = v___y_3839_;
v___y_3811_ = v___y_3840_;
v___y_3812_ = v___y_3841_;
v___y_3813_ = v___y_3842_;
v___y_3814_ = v___y_3843_;
v___y_3815_ = v___y_3844_;
v___y_3816_ = v___y_3845_;
v___y_3817_ = v___y_3846_;
v___y_3818_ = v___y_3847_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3849_;
v___y_3821_ = v___y_3851_;
v___y_3822_ = v___y_3850_;
v___y_3823_ = v___y_3852_;
v___y_3824_ = v___y_3853_;
v___y_3825_ = v___x_3861_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v___y_3856_;
v___y_3828_ = v___y_3858_;
v___y_3829_ = v___y_3857_;
v___y_3830_ = v___x_3867_;
goto v___jp_3809_;
}
}
v___jp_3869_:
{
lean_object* v_ref_3885_; uint8_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_ref_3885_ = lean_ctor_get(v___y_3874_, 5);
v___x_3886_ = 0;
v___x_3887_ = l_Lean_SourceInfo_fromRef(v_ref_3885_, v___x_3886_);
v___x_3888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_3890_ = l_Lean_SourceInfo_fromRef(v_tk_3868_, v___x_3739_);
lean_dec(v_tk_3868_);
v___x_3891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v___x_3888_);
v___x_3892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9));
v___x_3893_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
if (lean_obj_tag(v___y_3873_) == 1)
{
lean_object* v_val_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v_val_3894_ = lean_ctor_get(v___y_3873_, 0);
lean_inc(v_val_3894_);
lean_dec_ref_known(v___y_3873_, 1);
v___x_3895_ = l_Lean_SourceInfo_fromRef(v_val_3894_, v___x_3739_);
lean_dec(v_val_3894_);
v___x_3896_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_3897_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = l_Array_mkArray1___redArg(v___x_3897_);
v___y_3839_ = v___y_3870_;
v___y_3840_ = v___y_3871_;
v___y_3841_ = v___y_3872_;
v___y_3842_ = v___x_3887_;
v___y_3843_ = v___x_3891_;
v___y_3844_ = v___y_3884_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___y_3875_;
v___y_3847_ = v___y_3876_;
v___y_3848_ = v___y_3877_;
v___y_3849_ = v___y_3878_;
v___y_3850_ = v___x_3886_;
v___y_3851_ = v___x_3893_;
v___y_3852_ = v___y_3879_;
v___y_3853_ = v___y_3880_;
v___y_3854_ = v___x_3892_;
v___y_3855_ = v___y_3881_;
v___y_3856_ = v___x_3889_;
v___y_3857_ = v___y_3883_;
v___y_3858_ = v___y_3882_;
v___y_3859_ = v___x_3898_;
goto v___jp_3838_;
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_3873_);
lean_dec(v___y_3873_);
v___y_3839_ = v___y_3870_;
v___y_3840_ = v___y_3871_;
v___y_3841_ = v___y_3872_;
v___y_3842_ = v___x_3887_;
v___y_3843_ = v___x_3891_;
v___y_3844_ = v___y_3884_;
v___y_3845_ = v___y_3874_;
v___y_3846_ = v___y_3875_;
v___y_3847_ = v___y_3876_;
v___y_3848_ = v___y_3877_;
v___y_3849_ = v___y_3878_;
v___y_3850_ = v___x_3886_;
v___y_3851_ = v___x_3893_;
v___y_3852_ = v___y_3879_;
v___y_3853_ = v___y_3880_;
v___y_3854_ = v___x_3892_;
v___y_3855_ = v___y_3881_;
v___y_3856_ = v___x_3889_;
v___y_3857_ = v___y_3883_;
v___y_3858_ = v___y_3882_;
v___y_3859_ = v___x_3899_;
goto v___jp_3838_;
}
}
v___jp_3900_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_unsigned_to_nat(5u);
v___x_3917_ = l_Lean_Syntax_getArg(v___y_3904_, v___x_3916_);
lean_dec(v___y_3904_);
v___x_3918_ = l_Lean_Syntax_getOptional_x3f(v___y_3901_);
lean_dec(v___y_3901_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_box(0);
v___y_3870_ = v___y_3908_;
v___y_3871_ = v___y_3915_;
v___y_3872_ = v___x_3917_;
v___y_3873_ = v___y_3902_;
v___y_3874_ = v___y_3914_;
v___y_3875_ = v___y_3911_;
v___y_3876_ = v_args_3907_;
v___y_3877_ = v___y_3906_;
v___y_3878_ = v___y_3913_;
v___y_3879_ = v___y_3909_;
v___y_3880_ = v___y_3910_;
v___y_3881_ = v___y_3903_;
v___y_3882_ = v___y_3912_;
v___y_3883_ = v___y_3905_;
v___y_3884_ = v___x_3919_;
goto v___jp_3869_;
}
else
{
lean_object* v_val_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
v_val_3920_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3918_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_val_3920_);
lean_dec(v___x_3918_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_val_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
v___y_3870_ = v___y_3908_;
v___y_3871_ = v___y_3915_;
v___y_3872_ = v___x_3917_;
v___y_3873_ = v___y_3902_;
v___y_3874_ = v___y_3914_;
v___y_3875_ = v___y_3911_;
v___y_3876_ = v_args_3907_;
v___y_3877_ = v___y_3906_;
v___y_3878_ = v___y_3913_;
v___y_3879_ = v___y_3909_;
v___y_3880_ = v___y_3910_;
v___y_3881_ = v___y_3903_;
v___y_3882_ = v___y_3912_;
v___y_3883_ = v___y_3905_;
v___y_3884_ = v___x_3925_;
goto v___jp_3869_;
}
}
}
}
v___jp_3929_:
{
lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3945_ = l_Lean_Syntax_getArg(v___y_3933_, v___y_3931_);
v___x_3946_ = l_Lean_Syntax_isNone(v___x_3945_);
if (v___x_3946_ == 0)
{
uint8_t v___x_3947_; 
lean_inc(v___x_3945_);
v___x_3947_ = l_Lean_Syntax_matchesNull(v___x_3945_, v___x_3928_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; 
lean_dec(v___x_3945_);
lean_dec(v_only_3936_);
lean_dec(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec(v___y_3930_);
lean_dec(v_tk_3868_);
v___x_3948_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3948_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3949_ = l_Lean_Syntax_getArg(v___x_3945_, v___x_3741_);
lean_dec(v___x_3945_);
v___x_3950_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3949_);
v___x_3951_ = l_Lean_Syntax_isOfKind(v___x_3949_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; 
lean_dec(v___x_3949_);
lean_dec(v_only_3936_);
lean_dec(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec(v___y_3930_);
lean_dec(v_tk_3868_);
v___x_3952_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3952_;
}
else
{
lean_object* v___x_3953_; lean_object* v_args_3954_; lean_object* v___x_3955_; 
v___x_3953_ = l_Lean_Syntax_getArg(v___x_3949_, v___x_3928_);
lean_dec(v___x_3949_);
v_args_3954_ = l_Lean_Syntax_getArgs(v___x_3953_);
lean_dec(v___x_3953_);
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v_args_3954_);
v___y_3901_ = v___y_3930_;
v___y_3902_ = v___y_3932_;
v___y_3903_ = v___y_3934_;
v___y_3904_ = v___y_3933_;
v___y_3905_ = v_only_3936_;
v___y_3906_ = v___y_3935_;
v_args_3907_ = v___x_3955_;
v___y_3908_ = v___y_3937_;
v___y_3909_ = v___y_3938_;
v___y_3910_ = v___y_3939_;
v___y_3911_ = v___y_3940_;
v___y_3912_ = v___y_3941_;
v___y_3913_ = v___y_3942_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3944_;
goto v___jp_3900_;
}
}
}
else
{
lean_object* v___x_3956_; 
lean_dec(v___x_3945_);
v___x_3956_ = lean_box(0);
v___y_3901_ = v___y_3930_;
v___y_3902_ = v___y_3932_;
v___y_3903_ = v___y_3934_;
v___y_3904_ = v___y_3933_;
v___y_3905_ = v_only_3936_;
v___y_3906_ = v___y_3935_;
v_args_3907_ = v___x_3956_;
v___y_3908_ = v___y_3937_;
v___y_3909_ = v___y_3938_;
v___y_3910_ = v___y_3939_;
v___y_3911_ = v___y_3940_;
v___y_3912_ = v___y_3941_;
v___y_3913_ = v___y_3942_;
v___y_3914_ = v___y_3943_;
v___y_3915_ = v___y_3944_;
goto v___jp_3900_;
}
}
v___jp_3957_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v___x_3969_ = lean_unsigned_to_nat(3u);
v___x_3970_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3969_);
lean_dec(v_stx_3697_);
v___x_3971_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_3970_);
v___x_3972_ = l_Lean_Syntax_isOfKind(v___x_3970_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; 
lean_dec(v___x_3970_);
lean_dec(v_unfold_3960_);
lean_dec(v___y_3958_);
lean_dec(v_tk_3868_);
v___x_3973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3973_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3974_ = l_Lean_Syntax_getArg(v___x_3970_, v___x_3741_);
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3974_);
v___x_3976_ = l_Lean_Syntax_isOfKind(v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; 
lean_dec(v___x_3974_);
lean_dec(v___x_3970_);
lean_dec(v_unfold_3960_);
lean_dec(v___y_3958_);
lean_dec(v_tk_3868_);
v___x_3977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3977_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3978_ = l_Lean_Syntax_getArg(v___x_3970_, v___x_3928_);
v___x_3979_ = l_Lean_Syntax_getArg(v___x_3970_, v___y_3959_);
v___x_3980_ = l_Lean_Syntax_isNone(v___x_3979_);
if (v___x_3980_ == 0)
{
uint8_t v___x_3981_; 
lean_inc(v___x_3979_);
v___x_3981_ = l_Lean_Syntax_matchesNull(v___x_3979_, v___x_3928_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; 
lean_dec(v___x_3979_);
lean_dec(v___x_3978_);
lean_dec(v___x_3974_);
lean_dec(v___x_3970_);
lean_dec(v_unfold_3960_);
lean_dec(v___y_3958_);
lean_dec(v_tk_3868_);
v___x_3982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3982_;
}
else
{
lean_object* v_only_3983_; lean_object* v___x_3984_; 
v_only_3983_ = l_Lean_Syntax_getArg(v___x_3979_, v___x_3741_);
lean_dec(v___x_3979_);
v___x_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3984_, 0, v_only_3983_);
v___y_3930_ = v___x_3978_;
v___y_3931_ = v___x_3969_;
v___y_3932_ = v___y_3958_;
v___y_3933_ = v___x_3970_;
v___y_3934_ = v_unfold_3960_;
v___y_3935_ = v___x_3974_;
v_only_3936_ = v___x_3984_;
v___y_3937_ = v___y_3961_;
v___y_3938_ = v___y_3962_;
v___y_3939_ = v___y_3963_;
v___y_3940_ = v___y_3964_;
v___y_3941_ = v___y_3965_;
v___y_3942_ = v___y_3966_;
v___y_3943_ = v___y_3967_;
v___y_3944_ = v___y_3968_;
goto v___jp_3929_;
}
}
else
{
lean_object* v___x_3985_; 
lean_dec(v___x_3979_);
v___x_3985_ = lean_box(0);
v___y_3930_ = v___x_3978_;
v___y_3931_ = v___x_3969_;
v___y_3932_ = v___y_3958_;
v___y_3933_ = v___x_3970_;
v___y_3934_ = v_unfold_3960_;
v___y_3935_ = v___x_3974_;
v_only_3936_ = v___x_3985_;
v___y_3937_ = v___y_3961_;
v___y_3938_ = v___y_3962_;
v___y_3939_ = v___y_3963_;
v___y_3940_ = v___y_3964_;
v___y_3941_ = v___y_3965_;
v___y_3942_ = v___y_3966_;
v___y_3943_ = v___y_3967_;
v___y_3944_ = v___y_3968_;
goto v___jp_3929_;
}
}
}
}
v___jp_3986_:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
v___x_3996_ = lean_unsigned_to_nat(2u);
v___x_3997_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3996_);
v___x_3998_ = l_Lean_Syntax_isNone(v___x_3997_);
if (v___x_3998_ == 0)
{
uint8_t v___x_3999_; 
lean_inc(v___x_3997_);
v___x_3999_ = l_Lean_Syntax_matchesNull(v___x_3997_, v___x_3928_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; 
lean_dec(v___x_3997_);
lean_dec(v_squeeze_3987_);
lean_dec(v_tk_3868_);
lean_dec(v_stx_3697_);
v___x_4000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4000_;
}
else
{
lean_object* v_unfold_4001_; lean_object* v___x_4002_; 
v_unfold_4001_ = l_Lean_Syntax_getArg(v___x_3997_, v___x_3741_);
lean_dec(v___x_3997_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v_unfold_4001_);
v___y_3958_ = v_squeeze_3987_;
v___y_3959_ = v___x_3996_;
v_unfold_3960_ = v___x_4002_;
v___y_3961_ = v___y_3988_;
v___y_3962_ = v___y_3989_;
v___y_3963_ = v___y_3990_;
v___y_3964_ = v___y_3991_;
v___y_3965_ = v___y_3992_;
v___y_3966_ = v___y_3993_;
v___y_3967_ = v___y_3994_;
v___y_3968_ = v___y_3995_;
goto v___jp_3957_;
}
}
else
{
lean_object* v___x_4003_; 
lean_dec(v___x_3997_);
v___x_4003_ = lean_box(0);
v___y_3958_ = v_squeeze_3987_;
v___y_3959_ = v___x_3996_;
v_unfold_3960_ = v___x_4003_;
v___y_3961_ = v___y_3988_;
v___y_3962_ = v___y_3989_;
v___y_3963_ = v___y_3990_;
v___y_3964_ = v___y_3991_;
v___y_3965_ = v___y_3992_;
v___y_3966_ = v___y_3993_;
v___y_3967_ = v___y_3994_;
v___y_3968_ = v___y_3995_;
goto v___jp_3957_;
}
}
}
v___jp_3707_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_inc_ref(v___y_3719_);
v___x_3730_ = l_Array_append___redArg(v___y_3719_, v___y_3729_);
lean_dec_ref(v___y_3729_);
lean_inc_n(v___y_3723_, 2);
lean_inc_n(v___y_3712_, 4);
v___x_3731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3731_, 0, v___y_3712_);
lean_ctor_set(v___x_3731_, 1, v___y_3723_);
lean_ctor_set(v___x_3731_, 2, v___x_3730_);
v___x_3732_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11));
v___x_3733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___y_3712_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l_Lean_Syntax_node2(v___y_3712_, v___y_3723_, v___x_3733_, v___y_3711_);
lean_inc(v___y_3713_);
v___x_3735_ = l_Lean_Syntax_node5(v___y_3712_, v___y_3713_, v___y_3717_, v___y_3709_, v___y_3727_, v___x_3731_, v___x_3734_);
lean_inc(v___y_3725_);
v___x_3736_ = l_Lean_Syntax_node4(v___y_3712_, v___y_3725_, v___y_3714_, v___y_3724_, v___y_3728_, v___x_3735_);
v___x_3737_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_3720_, v___x_3736_, v___y_3708_, v___y_3721_, v___y_3722_, v___y_3716_, v___y_3726_, v___y_3718_, v___y_3715_, v___y_3710_);
return v___x_3737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4030_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4031_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4032_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4033_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4034_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4030_, v___x_4031_, v___x_4032_, v___x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4036_;
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
