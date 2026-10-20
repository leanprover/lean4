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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_isValidTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unnecessarySimpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(182, 23, 154, 96, 189, 166, 9, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "enable the 'unnecessary simpa' linter"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(219, 182, 224, 198, 198, 122, 225, 30)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(171, 130, 7, 230, 108, 210, 159, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_linter_unnecessarySimpa;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "`simp` already closes the goal"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Use `simp` instead of `simpa`:"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpAutoUnfold"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simp!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simp\?"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpTraceArgsRest"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpArgs"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticSimp\?!_"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simp\?!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Type mismatch: After simplification, term"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0_value;
static const lean_ctor_object l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1 = (const lean_object*)&l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0;
static lean_once_cell_t l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "locationHyp"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Occurs check failed: Expression"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\ncontains the goal "};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__9_value),LEAN_SCALAR_PTR_LITERAL(38, 116, 214, 236, 212, 160, 188, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.Tactic.Simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Elab.Tactic.Simpa.0.Lean.Elab.Tactic.Simpa.evalSimpaCore"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "using"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "using!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simpaUsingBang"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "simpaUsingBangArgsRest"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticSimpa!_"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simpa!"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12;
static const lean_closure_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_getSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 186, 141, 63, 66, 208, 56, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(158, 198, 190, 154, 66, 126, 242, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpaArgsRest"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value),LEAN_SCALAR_PTR_LITERAL(137, 133, 181, 17, 86, 74, 251, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Simpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalSimpa"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7_value),LEAN_SCALAR_PTR_LITERAL(207, 241, 251, 37, 131, 174, 231, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8_value),LEAN_SCALAR_PTR_LITERAL(8, 141, 117, 125, 176, 67, 228, 117)}};
static const lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "evalSimpaUsingBang"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 230, 37, 137, 25, 71, 189, 138)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 14, 13, 235, 216, 153, 126, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_54_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4____boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_();
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_63_, lean_object* v_opt_64_){
_start:
{
lean_object* v_name_65_; lean_object* v_defValue_66_; lean_object* v_map_67_; lean_object* v___x_68_; 
v_name_65_ = lean_ctor_get(v_opt_64_, 0);
v_defValue_66_ = lean_ctor_get(v_opt_64_, 1);
v_map_67_ = lean_ctor_get(v_opts_63_, 0);
v___x_68_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_67_, v_name_65_);
if (lean_obj_tag(v___x_68_) == 0)
{
uint8_t v___x_69_; 
v___x_69_ = lean_unbox(v_defValue_66_);
return v___x_69_;
}
else
{
lean_object* v_val_70_; 
v_val_70_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_val_70_);
lean_dec_ref_known(v___x_68_, 1);
if (lean_obj_tag(v_val_70_) == 1)
{
uint8_t v_v_71_; 
v_v_71_ = lean_ctor_get_uint8(v_val_70_, 0);
lean_dec_ref_known(v_val_70_, 0);
return v_v_71_;
}
else
{
uint8_t v___x_72_; 
lean_dec(v_val_70_);
v___x_72_ = lean_unbox(v_defValue_66_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_73_, lean_object* v_opt_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_opts_73_, v_opt_74_);
lean_dec_ref(v_opt_74_);
lean_dec_ref(v_opts_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_86_) == 1)
{
lean_object* v_pre_87_; 
v_pre_87_ = lean_ctor_get(v_x_86_, 0);
switch(lean_obj_tag(v_pre_87_))
{
case 1:
{
lean_object* v_pre_88_; 
v_pre_88_ = lean_ctor_get(v_pre_87_, 0);
switch(lean_obj_tag(v_pre_88_))
{
case 0:
{
lean_object* v_str_89_; lean_object* v_str_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_str_89_ = lean_ctor_get(v_x_86_, 1);
v_str_90_ = lean_ctor_get(v_pre_87_, 1);
v___x_91_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_92_ = lean_string_dec_eq(v_str_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_94_ = lean_string_dec_eq(v_str_90_, v___x_93_);
if (v___x_94_ == 0)
{
return v___x_94_;
}
else
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_96_ = lean_string_dec_eq(v_str_89_, v___x_95_);
if (v___x_96_ == 0)
{
return v___x_96_;
}
else
{
return v_suppressElabErrors_85_;
}
}
}
else
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_98_ = lean_string_dec_eq(v_str_89_, v___x_97_);
if (v___x_98_ == 0)
{
return v___x_98_;
}
else
{
return v_suppressElabErrors_85_;
}
}
}
case 1:
{
lean_object* v_pre_99_; 
v_pre_99_ = lean_ctor_get(v_pre_88_, 0);
if (lean_obj_tag(v_pre_99_) == 0)
{
lean_object* v_str_100_; lean_object* v_str_101_; lean_object* v_str_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_str_100_ = lean_ctor_get(v_x_86_, 1);
v_str_101_ = lean_ctor_get(v_pre_87_, 1);
v_str_102_ = lean_ctor_get(v_pre_88_, 1);
v___x_103_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_104_ = lean_string_dec_eq(v_str_102_, v___x_103_);
if (v___x_104_ == 0)
{
return v___x_104_;
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_106_ = lean_string_dec_eq(v_str_101_, v___x_105_);
if (v___x_106_ == 0)
{
return v___x_106_;
}
else
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_108_ = lean_string_dec_eq(v_str_100_, v___x_107_);
if (v___x_108_ == 0)
{
return v___x_108_;
}
else
{
return v_suppressElabErrors_85_;
}
}
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
default: 
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
}
case 0:
{
lean_object* v_str_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_str_111_ = lean_ctor_get(v_x_86_, 1);
v___x_112_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_113_ = lean_string_dec_eq(v_str_111_, v___x_112_);
if (v___x_113_ == 0)
{
return v___x_113_;
}
else
{
return v_suppressElabErrors_85_;
}
}
default: 
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_suppressElabErrors_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_suppressElabErrors_boxed_118_ = lean_unbox(v_suppressElabErrors_116_);
v_res_119_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_118_, v_x_117_);
lean_dec(v_x_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; lean_object* v_env_128_; uint8_t v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_toCold_132_; lean_object* v_mctx_133_; lean_object* v_lctx_134_; lean_object* v_options_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_127_ = lean_st_ref_get(v___y_125_);
v_env_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc_ref(v_env_128_);
lean_dec(v___x_127_);
v___x_129_ = 0;
v_env_130_ = l_Lean_Environment_setRecordingDeps(v_env_128_, v___x_129_);
v___x_131_ = lean_st_ref_get(v___y_123_);
v_toCold_132_ = lean_ctor_get(v___y_124_, 0);
v_mctx_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_mctx_133_);
lean_dec(v___x_131_);
v_lctx_134_ = lean_ctor_get(v___y_122_, 2);
v_options_135_ = lean_ctor_get(v_toCold_132_, 2);
lean_inc_ref(v_options_135_);
lean_inc_ref(v_lctx_134_);
v___x_136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_136_, 0, v_env_130_);
lean_ctor_set(v___x_136_, 1, v_mctx_133_);
lean_ctor_set(v___x_136_, 2, v_lctx_134_);
lean_ctor_set(v___x_136_, 3, v_options_135_);
v___x_137_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_msgData_121_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msgData_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_147_, lean_object* v_msgData_148_, uint8_t v_severity_149_, uint8_t v_isSilent_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___y_157_; lean_object* v___y_158_; uint8_t v___y_159_; uint8_t v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v_toCold_164_; lean_object* v___y_165_; lean_object* v___y_194_; lean_object* v___y_195_; uint8_t v___y_196_; uint8_t v___y_197_; lean_object* v___y_198_; uint8_t v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; uint8_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; uint8_t v___y_226_; lean_object* v___y_227_; uint8_t v___y_231_; uint8_t v___y_232_; uint8_t v___x_242_; uint8_t v___y_244_; uint8_t v___x_250_; 
v___x_242_ = 2;
v___x_250_ = l_Lean_instBEqMessageSeverity_beq(v_severity_149_, v___x_242_);
if (v___x_250_ == 0)
{
v___y_244_ = v___x_250_;
goto v___jp_243_;
}
else
{
uint8_t v___x_251_; 
lean_inc_ref(v_msgData_148_);
v___x_251_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_148_);
if (v___x_251_ == 0)
{
v___y_244_ = v___x_251_;
goto v___jp_243_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v_msgData_148_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
v___jp_156_:
{
lean_object* v_currNamespace_166_; lean_object* v_openDecls_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_env_172_; lean_object* v_nextMacroScope_173_; lean_object* v_ngen_174_; lean_object* v_auxDeclNGen_175_; lean_object* v_traceState_176_; lean_object* v_cache_177_; lean_object* v_recordedDeps_178_; lean_object* v_messages_179_; lean_object* v_infoState_180_; lean_object* v_snapshotTasks_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_192_; 
v_currNamespace_166_ = lean_ctor_get(v_toCold_164_, 4);
v_openDecls_167_ = lean_ctor_get(v_toCold_164_, 5);
lean_inc(v_openDecls_167_);
lean_inc(v_currNamespace_166_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v_currNamespace_166_);
lean_ctor_set(v___x_168_, 1, v_openDecls_167_);
v___x_169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___y_158_);
lean_inc_ref(v___y_162_);
lean_inc_ref(v___y_163_);
v___x_170_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_170_, 0, v___y_163_);
lean_ctor_set(v___x_170_, 1, v___y_157_);
lean_ctor_set(v___x_170_, 2, v___y_161_);
lean_ctor_set(v___x_170_, 3, v___y_162_);
lean_ctor_set(v___x_170_, 4, v___x_169_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*5, v___y_160_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*5 + 1, v___y_159_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*5 + 2, v_isSilent_150_);
v___x_171_ = lean_st_ref_take(v___y_165_);
v_env_172_ = lean_ctor_get(v___x_171_, 0);
v_nextMacroScope_173_ = lean_ctor_get(v___x_171_, 1);
v_ngen_174_ = lean_ctor_get(v___x_171_, 2);
v_auxDeclNGen_175_ = lean_ctor_get(v___x_171_, 3);
v_traceState_176_ = lean_ctor_get(v___x_171_, 4);
v_cache_177_ = lean_ctor_get(v___x_171_, 5);
v_recordedDeps_178_ = lean_ctor_get(v___x_171_, 6);
v_messages_179_ = lean_ctor_get(v___x_171_, 7);
v_infoState_180_ = lean_ctor_get(v___x_171_, 8);
v_snapshotTasks_181_ = lean_ctor_get(v___x_171_, 9);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_192_ == 0)
{
v___x_183_ = v___x_171_;
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snapshotTasks_181_);
lean_inc(v_infoState_180_);
lean_inc(v_messages_179_);
lean_inc(v_recordedDeps_178_);
lean_inc(v_cache_177_);
lean_inc(v_traceState_176_);
lean_inc(v_auxDeclNGen_175_);
lean_inc(v_ngen_174_);
lean_inc(v_nextMacroScope_173_);
lean_inc(v_env_172_);
lean_dec(v___x_171_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_box(0);
v___x_186_ = l_Lean_MessageLog_add(v___x_170_, v_messages_179_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 7, v___x_186_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_env_172_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_nextMacroScope_173_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_ngen_174_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_auxDeclNGen_175_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_traceState_176_);
lean_ctor_set(v_reuseFailAlloc_191_, 5, v_cache_177_);
lean_ctor_set(v_reuseFailAlloc_191_, 6, v_recordedDeps_178_);
lean_ctor_set(v_reuseFailAlloc_191_, 7, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_191_, 8, v_infoState_180_);
lean_ctor_set(v_reuseFailAlloc_191_, 9, v_snapshotTasks_181_);
v___x_188_ = v_reuseFailAlloc_191_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_st_ref_put(v___y_165_, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_185_);
return v___x_190_;
}
}
}
v___jp_193_:
{
lean_object* v_fileName_202_; lean_object* v_fileMap_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_219_; 
v_fileName_202_ = lean_ctor_get(v___y_200_, 0);
v_fileMap_203_ = lean_ctor_get(v___y_200_, 1);
v___x_204_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_148_);
v___x_205_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v___x_204_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_219_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_219_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_219_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_inc_ref_n(v_fileMap_203_, 2);
v___x_210_ = l_Lean_FileMap_toPosition(v_fileMap_203_, v___y_198_);
lean_dec(v___y_198_);
v___x_211_ = l_Lean_FileMap_toPosition(v_fileMap_203_, v___y_201_);
lean_dec(v___y_201_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
v___x_213_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0));
if (v___y_199_ == 0)
{
lean_del_object(v___x_208_);
lean_dec_ref(v___y_194_);
v___y_157_ = v___x_210_;
v___y_158_ = v_a_206_;
v___y_159_ = v___y_196_;
v___y_160_ = v___y_197_;
v___y_161_ = v___x_212_;
v___y_162_ = v___x_213_;
v___y_163_ = v_fileName_202_;
v_toCold_164_ = v___y_195_;
v___y_165_ = v___y_154_;
goto v___jp_156_;
}
else
{
uint8_t v___x_214_; 
lean_inc(v_a_206_);
v___x_214_ = l_Lean_MessageData_hasTag(v___y_194_, v_a_206_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_217_; 
lean_dec_ref_known(v___x_212_, 1);
lean_dec_ref(v___x_210_);
lean_dec(v_a_206_);
v___x_215_ = lean_box(0);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_215_);
v___x_217_ = v___x_208_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
else
{
lean_del_object(v___x_208_);
v___y_157_ = v___x_210_;
v___y_158_ = v_a_206_;
v___y_159_ = v___y_196_;
v___y_160_ = v___y_197_;
v___y_161_ = v___x_212_;
v___y_162_ = v___x_213_;
v___y_163_ = v_fileName_202_;
v_toCold_164_ = v___y_195_;
v___y_165_ = v___y_154_;
goto v___jp_156_;
}
}
}
}
v___jp_220_:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Syntax_getTailPos_x3f(v___y_225_, v___y_226_);
lean_dec(v___y_225_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_inc(v___y_227_);
v___y_194_ = v___y_222_;
v___y_195_ = v___y_223_;
v___y_196_ = v___y_224_;
v___y_197_ = v___y_226_;
v___y_198_ = v___y_227_;
v___y_199_ = v___y_221_;
v___y_200_ = v___y_223_;
v___y_201_ = v___y_227_;
goto v___jp_193_;
}
else
{
lean_object* v_val_229_; 
v_val_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_228_, 1);
v___y_194_ = v___y_222_;
v___y_195_ = v___y_223_;
v___y_196_ = v___y_224_;
v___y_197_ = v___y_226_;
v___y_198_ = v___y_227_;
v___y_199_ = v___y_221_;
v___y_200_ = v___y_223_;
v___y_201_ = v_val_229_;
goto v___jp_193_;
}
}
v___jp_230_:
{
lean_object* v_toCold_233_; lean_object* v_ref_234_; uint8_t v_suppressElabErrors_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v_ref_238_; lean_object* v___x_239_; 
v_toCold_233_ = lean_ctor_get(v___y_153_, 0);
v_ref_234_ = lean_ctor_get(v___y_153_, 2);
v_suppressElabErrors_235_ = lean_ctor_get_uint8(v___y_153_, sizeof(void*)*3 + 2);
v___x_236_ = lean_box(v_suppressElabErrors_235_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_237_, 0, v___x_236_);
v_ref_238_ = l_Lean_replaceRef(v_ref_147_, v_ref_234_);
v___x_239_ = l_Lean_Syntax_getPos_x3f(v_ref_238_, v___y_231_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___y_221_ = v_suppressElabErrors_235_;
v___y_222_ = v___f_237_;
v___y_223_ = v_toCold_233_;
v___y_224_ = v___y_232_;
v___y_225_ = v_ref_238_;
v___y_226_ = v___y_231_;
v___y_227_ = v___x_240_;
goto v___jp_220_;
}
else
{
lean_object* v_val_241_; 
v_val_241_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_239_, 1);
v___y_221_ = v_suppressElabErrors_235_;
v___y_222_ = v___f_237_;
v___y_223_ = v_toCold_233_;
v___y_224_ = v___y_232_;
v___y_225_ = v_ref_238_;
v___y_226_ = v___y_231_;
v___y_227_ = v_val_241_;
goto v___jp_220_;
}
}
v___jp_243_:
{
uint8_t v___x_245_; uint8_t v___x_246_; 
v___x_245_ = 1;
v___x_246_ = l_Lean_instBEqMessageSeverity_beq(v_severity_149_, v___x_245_);
if (v___x_246_ == 0)
{
v___y_231_ = v___y_244_;
v___y_232_ = v_severity_149_;
goto v___jp_230_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_153_);
v___x_248_ = l_Lean_warningAsError;
v___x_249_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_247_, v___x_248_);
lean_dec_ref(v___x_247_);
if (v___x_249_ == 0)
{
v___y_231_ = v___y_244_;
v___y_232_ = v_severity_149_;
goto v___jp_230_;
}
else
{
v___y_231_ = v___y_244_;
v___y_232_ = v___x_242_;
goto v___jp_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_254_, lean_object* v_msgData_255_, lean_object* v_severity_256_, lean_object* v_isSilent_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
uint8_t v_severity_boxed_263_; uint8_t v_isSilent_boxed_264_; lean_object* v_res_265_; 
v_severity_boxed_263_ = lean_unbox(v_severity_256_);
v_isSilent_boxed_264_ = lean_unbox(v_isSilent_257_);
v_res_265_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_254_, v_msgData_255_, v_severity_boxed_263_, v_isSilent_boxed_264_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v_ref_254_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_266_, lean_object* v_msgData_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
uint8_t v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; 
v___x_277_ = 1;
v___x_278_ = 0;
v___x_279_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_266_, v_msgData_267_, v___x_277_, v___x_278_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_280_, lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_280_, v_msgData_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v_ref_280_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_298_, lean_object* v_stx_299_, lean_object* v_msg_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_name_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_328_; 
v_name_310_ = lean_ctor_get(v_linterOption_298_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_linterOption_298_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_linterOption_298_, 1);
lean_dec(v_unused_329_);
v___x_312_ = v_linterOption_298_;
v_isShared_313_ = v_isSharedCheck_328_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_name_310_);
lean_dec(v_linterOption_298_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_328_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_310_);
v___x_315_ = l_Lean_MessageData_ofName(v_name_310_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 7);
lean_ctor_set(v___x_312_, 1, v___x_315_);
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_317_ = v___x_312_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_327_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_disable_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_318_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v_disable_320_ = l_Lean_MessageData_note(v___x_319_);
v___x_321_ = l_Lean_Linter_linterMessageTag;
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v_msg_300_);
lean_ctor_set(v___x_322_, 1, v_disable_320_);
v___x_323_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_324_, 0, v_name_310_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_inc(v_stx_299_);
v___x_325_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_325_, 0, v_stx_299_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_299_, v___x_325_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v_stx_299_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_330_, lean_object* v_stx_331_, lean_object* v_msg_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_330_, v_stx_331_, v_msg_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_342_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v_msg_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_345_ = l_Lean_stringToMessageData(v___x_344_);
return v_msg_345_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_353_ = l_Lean_MessageData_ofFormat(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_354_, lean_object* v_ref_355_, lean_object* v_replacement_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_msg_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v_msg_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_msg_378_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_379_ = lean_box(0);
lean_inc(v_replacement_356_);
v___x_380_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_354_, v_replacement_356_, v___x_379_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; uint8_t v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = lean_unbox(v_a_381_);
lean_dec(v_a_381_);
if (v___x_382_ == 0)
{
lean_dec(v_replacement_356_);
v_msg_367_ = v_msg_378_;
v___y_368_ = v_a_357_;
v___y_369_ = v_a_358_;
v___y_370_ = v_a_359_;
v___y_371_ = v_a_360_;
v___y_372_ = v_a_361_;
v___y_373_ = v_a_362_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
goto v___jp_366_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_replacement_356_);
v___x_385_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_379_);
lean_ctor_set(v___x_385_, 2, v___x_379_);
lean_ctor_set(v___x_385_, 3, v___x_379_);
lean_ctor_set(v___x_385_, 4, v___x_379_);
lean_ctor_set(v___x_385_, 5, v___x_379_);
lean_inc(v_ref_355_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v_ref_355_);
v___x_387_ = 4;
lean_inc_ref(v___x_386_);
v___x_388_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_388_, 0, v___x_385_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_379_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*3, v___x_387_);
v___x_389_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_mk_empty_array_with_capacity(v___x_390_);
v___x_392_ = lean_array_push(v___x_391_, v___x_388_);
v___x_393_ = 0;
v___x_394_ = l_Lean_MessageData_hint(v___x_389_, v___x_392_, v___x_386_, v___x_379_, v___x_393_, v_a_363_, v_a_364_);
lean_dec_ref(v___x_392_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_396_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v_msg_378_);
lean_ctor_set(v___x_396_, 1, v_a_395_);
v_msg_367_ = v___x_396_;
v___y_368_ = v_a_357_;
v___y_369_ = v_a_358_;
v___y_370_ = v_a_359_;
v___y_371_ = v_a_360_;
v___y_372_ = v_a_361_;
v___y_373_ = v_a_362_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
goto v___jp_366_;
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_ref_355_);
v_a_397_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_394_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_394_);
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
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_replacement_356_);
lean_dec(v_ref_355_);
v_a_405_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_380_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_380_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
v___jp_366_:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = l_Lean_linter_unnecessarySimpa;
v___x_377_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_376_, v_ref_355_, v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_413_, lean_object* v_ref_414_, lean_object* v_replacement_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_413_, v_ref_414_, v_replacement_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_426_, lean_object* v_msgData_427_, uint8_t v_severity_428_, uint8_t v_isSilent_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_426_, v_msgData_427_, v_severity_428_, v_isSilent_429_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_440_, lean_object* v_msgData_441_, lean_object* v_severity_442_, lean_object* v_isSilent_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v_severity_boxed_453_; uint8_t v_isSilent_boxed_454_; lean_object* v_res_455_; 
v_severity_boxed_453_ = lean_unbox(v_severity_442_);
v_isSilent_boxed_454_ = lean_unbox(v_isSilent_443_);
v_res_455_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_440_, v_msgData_441_, v_severity_boxed_453_, v_isSilent_boxed_454_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v_ref_440_);
return v_res_455_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_box(0);
v___x_457_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
lean_inc(v___y_490_);
lean_inc_ref(v___y_489_);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
v___x_496_ = lean_apply_9(v_x_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, lean_box(0));
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed(lean_object* v_x_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(v_x_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(lean_object* v_mvarId_508_, lean_object* v_x_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___f_519_; lean_object* v___x_520_; 
lean_inc(v___y_513_);
lean_inc_ref(v___y_512_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
v___f_519_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_519_, 0, v_x_509_);
lean_closure_set(v___f_519_, 1, v___y_510_);
lean_closure_set(v___f_519_, 2, v___y_511_);
lean_closure_set(v___f_519_, 3, v___y_512_);
lean_closure_set(v___f_519_, 4, v___y_513_);
v___x_520_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_508_, v___f_519_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
return v___x_520_;
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___boxed(lean_object* v_mvarId_529_, lean_object* v_x_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_529_, v_x_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v_00_u03b1_541_, lean_object* v_mvarId_542_, lean_object* v_x_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_542_, v_x_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v_00_u03b1_554_, lean_object* v_mvarId_555_, lean_object* v_x_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v_00_u03b1_554_, v_mvarId_555_, v_x_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_566_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(32u);
v___x_568_ = lean_mk_empty_array_with_capacity(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_570_ = ((size_t)5ULL);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_unsigned_to_nat(32u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_575_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v___x_573_);
lean_ctor_set(v___x_575_, 2, v___x_571_);
lean_ctor_set(v___x_575_, 3, v___x_571_);
lean_ctor_set_usize(v___x_575_, 4, v___x_570_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v_infoState_579_; lean_object* v_trees_580_; lean_object* v___x_581_; lean_object* v_infoState_582_; lean_object* v_env_583_; lean_object* v_nextMacroScope_584_; lean_object* v_ngen_585_; lean_object* v_auxDeclNGen_586_; lean_object* v_traceState_587_; lean_object* v_cache_588_; lean_object* v_recordedDeps_589_; lean_object* v_messages_590_; lean_object* v_snapshotTasks_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_612_; 
v___x_578_ = lean_st_ref_get(v___y_576_);
v_infoState_579_ = lean_ctor_get(v___x_578_, 8);
lean_inc_ref(v_infoState_579_);
lean_dec(v___x_578_);
v_trees_580_ = lean_ctor_get(v_infoState_579_, 2);
lean_inc_ref(v_trees_580_);
lean_dec_ref(v_infoState_579_);
v___x_581_ = lean_st_ref_take(v___y_576_);
v_infoState_582_ = lean_ctor_get(v___x_581_, 8);
v_env_583_ = lean_ctor_get(v___x_581_, 0);
v_nextMacroScope_584_ = lean_ctor_get(v___x_581_, 1);
v_ngen_585_ = lean_ctor_get(v___x_581_, 2);
v_auxDeclNGen_586_ = lean_ctor_get(v___x_581_, 3);
v_traceState_587_ = lean_ctor_get(v___x_581_, 4);
v_cache_588_ = lean_ctor_get(v___x_581_, 5);
v_recordedDeps_589_ = lean_ctor_get(v___x_581_, 6);
v_messages_590_ = lean_ctor_get(v___x_581_, 7);
v_snapshotTasks_591_ = lean_ctor_get(v___x_581_, 9);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_612_ == 0)
{
v___x_593_ = v___x_581_;
v_isShared_594_ = v_isSharedCheck_612_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snapshotTasks_591_);
lean_inc(v_infoState_582_);
lean_inc(v_messages_590_);
lean_inc(v_recordedDeps_589_);
lean_inc(v_cache_588_);
lean_inc(v_traceState_587_);
lean_inc(v_auxDeclNGen_586_);
lean_inc(v_ngen_585_);
lean_inc(v_nextMacroScope_584_);
lean_inc(v_env_583_);
lean_dec(v___x_581_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_612_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v_enabled_595_; lean_object* v_assignment_596_; lean_object* v_lazyAssignment_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_610_; 
v_enabled_595_ = lean_ctor_get_uint8(v_infoState_582_, sizeof(void*)*3);
v_assignment_596_ = lean_ctor_get(v_infoState_582_, 0);
v_lazyAssignment_597_ = lean_ctor_get(v_infoState_582_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_infoState_582_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_infoState_582_, 2);
lean_dec(v_unused_611_);
v___x_599_ = v_infoState_582_;
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_lazyAssignment_597_);
lean_inc(v_assignment_596_);
lean_dec(v_infoState_582_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 2, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_assignment_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_lazyAssignment_597_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v___x_601_);
lean_ctor_set_uint8(v_reuseFailAlloc_609_, sizeof(void*)*3, v_enabled_595_);
v___x_603_ = v_reuseFailAlloc_609_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 8, v___x_603_);
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_env_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_nextMacroScope_584_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_ngen_585_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_auxDeclNGen_586_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_traceState_587_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v_cache_588_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_recordedDeps_589_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_messages_590_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_608_, 9, v_snapshotTasks_591_);
v___x_605_ = v_reuseFailAlloc_608_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_st_ref_put(v___y_576_, v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_trees_580_);
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_613_);
lean_dec(v___y_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___f_647_; lean_object* v___x_84726__overap_648_; lean_object* v___x_649_; 
v___f_647_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_84726__overap_648_ = lean_panic_fn_borrowed(v___f_647_, v_msg_637_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
lean_inc(v___y_643_);
lean_inc_ref(v___y_642_);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
v___x_649_ = lean_apply_9(v___x_84726__overap_648_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, lean_box(0));
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_ref_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_ref_670_ = lean_ctor_get(v___y_667_, 2);
v___x_671_ = 0;
v___x_672_ = l_Lean_SourceInfo_fromRef(v_ref_670_, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_683_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Array_mkArray0___redArg();
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v_squeeze_700_, lean_object* v_unfold_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_args_707_, lean_object* v_only_708_, uint8_t v___x_709_, lean_object* v___y_710_, lean_object* v_loc_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
if (lean_obj_tag(v_squeeze_700_) == 0)
{
uint8_t v___x_721_; 
v___x_721_ = 0;
if (lean_obj_tag(v_unfold_701_) == 0)
{
lean_object* v_ref_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_762_; 
v_ref_722_ = lean_ctor_get(v___y_718_, 2);
v___x_723_ = l_Lean_SourceInfo_fromRef(v_ref_722_, v___x_721_);
v___x_724_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
v___x_725_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_724_);
lean_inc(v___x_723_);
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_723_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
v___x_727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_728_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3);
if (lean_obj_tag(v___y_710_) == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_762_ = v___x_771_;
goto v___jp_761_;
}
else
{
lean_object* v_val_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_val_772_ = lean_ctor_get(v___y_710_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v___y_710_, 1);
v___x_773_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_774_ = lean_array_push(v___x_773_, v_val_772_);
v___y_762_ = v___x_774_;
goto v___jp_761_;
}
v___jp_729_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = l_Array_append___redArg(v___x_728_, v___y_733_);
lean_dec_ref(v___y_733_);
lean_inc(v___x_723_);
v___x_735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_735_, 0, v___x_723_);
lean_ctor_set(v___x_735_, 1, v___x_727_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
v___x_736_ = l_Lean_Syntax_node6(v___x_723_, v___x_725_, v___x_726_, v___x_705_, v___y_730_, v___y_731_, v___y_732_, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
v___jp_738_:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = l_Array_append___redArg(v___x_728_, v___y_741_);
lean_dec_ref(v___y_741_);
lean_inc(v___x_723_);
v___x_743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_743_, 0, v___x_723_);
lean_ctor_set(v___x_743_, 1, v___x_727_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
if (lean_obj_tag(v_loc_711_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_745_; 
v_val_744_ = lean_ctor_get(v_loc_711_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v_loc_711_, 1);
v___x_745_ = l_Array_mkArray1___redArg(v_val_744_);
v___y_730_ = v___y_739_;
v___y_731_ = v___y_740_;
v___y_732_ = v___x_743_;
v___y_733_ = v___x_745_;
goto v___jp_729_;
}
else
{
lean_object* v___x_746_; 
lean_dec(v_loc_711_);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_730_ = v___y_739_;
v___y_731_ = v___y_740_;
v___y_732_ = v___x_743_;
v___y_733_ = v___x_746_;
goto v___jp_729_;
}
}
v___jp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = l_Array_append___redArg(v___x_728_, v___y_749_);
lean_dec_ref(v___y_749_);
lean_inc(v___x_723_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___x_723_);
lean_ctor_set(v___x_751_, 1, v___x_727_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_val_752_ = lean_ctor_get(v_args_707_, 0);
v___x_753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___x_723_, 3);
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_723_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Array_append___redArg(v___x_728_, v_val_752_);
v___x_756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_756_, 0, v___x_723_);
lean_ctor_set(v___x_756_, 1, v___x_727_);
lean_ctor_set(v___x_756_, 2, v___x_755_);
v___x_757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_723_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Array_mkArray3___redArg(v___x_754_, v___x_756_, v___x_758_);
v___y_739_ = v___y_748_;
v___y_740_ = v___x_751_;
v___y_741_ = v___x_759_;
goto v___jp_738_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_739_ = v___y_748_;
v___y_740_ = v___x_751_;
v___y_741_ = v___x_760_;
goto v___jp_738_;
}
}
v___jp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = l_Array_append___redArg(v___x_728_, v___y_762_);
lean_dec_ref(v___y_762_);
lean_inc(v___x_723_);
v___x_764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_764_, 0, v___x_723_);
lean_ctor_set(v___x_764_, 1, v___x_727_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_val_765_ = lean_ctor_get(v_only_708_, 0);
v___x_766_ = l_Lean_SourceInfo_fromRef(v_val_765_, v___x_709_);
v___x_767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Array_mkArray1___redArg(v___x_768_);
v___y_748_ = v___x_764_;
v___y_749_ = v___x_769_;
goto v___jp_747_;
}
else
{
lean_object* v___x_770_; 
v___x_770_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_748_ = v___x_764_;
v___y_749_ = v___x_770_;
goto v___jp_747_;
}
}
}
else
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_834_; 
v_isSharedCheck_834_ = !lean_is_exclusive(v_unfold_701_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v_unfold_701_, 0);
lean_dec(v_unused_835_);
v___x_776_ = v_unfold_701_;
v_isShared_777_ = v_isSharedCheck_834_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_unfold_701_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_834_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_ref_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_821_; 
v_ref_778_ = lean_ctor_get(v___y_718_, 2);
v___x_779_ = l_Lean_SourceInfo_fromRef(v_ref_778_, v___x_721_);
v___x_780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7));
v___x_781_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8));
lean_inc(v___x_779_);
v___x_783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_779_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3);
if (lean_obj_tag(v___y_710_) == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_821_ = v___x_830_;
goto v___jp_820_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_val_831_ = lean_ctor_get(v___y_710_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___y_710_, 1);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_833_ = lean_array_push(v___x_832_, v_val_831_);
v___y_821_ = v___x_833_;
goto v___jp_820_;
}
v___jp_786_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_791_ = l_Array_append___redArg(v___x_785_, v___y_790_);
lean_dec_ref(v___y_790_);
lean_inc(v___x_779_);
v___x_792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_792_, 0, v___x_779_);
lean_ctor_set(v___x_792_, 1, v___x_784_);
lean_ctor_set(v___x_792_, 2, v___x_791_);
v___x_793_ = l_Lean_Syntax_node6(v___x_779_, v___x_781_, v___x_783_, v___x_705_, v___y_787_, v___y_788_, v___y_789_, v___x_792_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 0);
lean_ctor_set(v___x_776_, 0, v___x_793_);
v___x_795_ = v___x_776_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
v___jp_797_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_Array_append___redArg(v___x_785_, v___y_800_);
lean_dec_ref(v___y_800_);
lean_inc(v___x_779_);
v___x_802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_802_, 0, v___x_779_);
lean_ctor_set(v___x_802_, 1, v___x_784_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
if (lean_obj_tag(v_loc_711_) == 1)
{
lean_object* v_val_803_; lean_object* v___x_804_; 
v_val_803_ = lean_ctor_get(v_loc_711_, 0);
lean_inc(v_val_803_);
lean_dec_ref_known(v_loc_711_, 1);
v___x_804_ = l_Array_mkArray1___redArg(v_val_803_);
v___y_787_ = v___y_798_;
v___y_788_ = v___y_799_;
v___y_789_ = v___x_802_;
v___y_790_ = v___x_804_;
goto v___jp_786_;
}
else
{
lean_object* v___x_805_; 
lean_dec(v_loc_711_);
v___x_805_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_787_ = v___y_798_;
v___y_788_ = v___y_799_;
v___y_789_ = v___x_802_;
v___y_790_ = v___x_805_;
goto v___jp_786_;
}
}
v___jp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = l_Array_append___redArg(v___x_785_, v___y_808_);
lean_dec_ref(v___y_808_);
lean_inc(v___x_779_);
v___x_810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_810_, 0, v___x_779_);
lean_ctor_set(v___x_810_, 1, v___x_784_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_val_811_ = lean_ctor_get(v_args_707_, 0);
v___x_812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___x_779_, 3);
v___x_813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_779_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Array_append___redArg(v___x_785_, v_val_811_);
v___x_815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_815_, 0, v___x_779_);
lean_ctor_set(v___x_815_, 1, v___x_784_);
lean_ctor_set(v___x_815_, 2, v___x_814_);
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_817_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_779_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Array_mkArray3___redArg(v___x_813_, v___x_815_, v___x_817_);
v___y_798_ = v___y_807_;
v___y_799_ = v___x_810_;
v___y_800_ = v___x_818_;
goto v___jp_797_;
}
else
{
lean_object* v___x_819_; 
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_798_ = v___y_807_;
v___y_799_ = v___x_810_;
v___y_800_ = v___x_819_;
goto v___jp_797_;
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = l_Array_append___redArg(v___x_785_, v___y_821_);
lean_dec_ref(v___y_821_);
lean_inc(v___x_779_);
v___x_823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_779_);
lean_ctor_set(v___x_823_, 1, v___x_784_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_val_824_ = lean_ctor_get(v_only_708_, 0);
v___x_825_ = l_Lean_SourceInfo_fromRef(v_val_824_, v___x_709_);
v___x_826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Array_mkArray1___redArg(v___x_827_);
v___y_807_ = v___x_823_;
v___y_808_ = v___x_828_;
goto v___jp_806_;
}
else
{
lean_object* v___x_829_; 
v___x_829_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_807_ = v___x_823_;
v___y_808_ = v___x_829_;
goto v___jp_806_;
}
}
}
}
}
else
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v_squeeze_700_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v_squeeze_700_, 0);
lean_dec(v_unused_972_);
v___x_837_ = v_squeeze_700_;
v_isShared_838_ = v_isSharedCheck_971_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_squeeze_700_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_971_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
if (lean_obj_tag(v_unfold_701_) == 0)
{
lean_object* v_ref_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_890_; 
v_ref_839_ = lean_ctor_get(v___y_718_, 2);
v___x_840_ = 0;
v___x_841_ = l_Lean_SourceInfo_fromRef(v_ref_839_, v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9));
lean_inc_ref_n(v___x_704_, 2);
lean_inc_ref_n(v___x_703_, 2);
lean_inc_ref_n(v___x_702_, 2);
v___x_843_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_842_);
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10));
lean_inc_n(v___x_841_, 2);
v___x_845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_841_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_847_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3);
v___x_848_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_848_, 0, v___x_841_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
v___x_849_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_850_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_849_);
if (lean_obj_tag(v___y_710_) == 0)
{
lean_object* v___x_899_; 
v___x_899_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_890_ = v___x_899_;
goto v___jp_889_;
}
else
{
lean_object* v_val_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_val_900_ = lean_ctor_get(v___y_710_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v___y_710_, 1);
v___x_901_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_902_ = lean_array_push(v___x_901_, v_val_900_);
v___y_890_ = v___x_902_;
goto v___jp_889_;
}
v___jp_851_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_856_ = l_Array_append___redArg(v___x_847_, v___y_855_);
lean_dec_ref(v___y_855_);
lean_inc_n(v___x_841_, 2);
v___x_857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_857_, 0, v___x_841_);
lean_ctor_set(v___x_857_, 1, v___x_846_);
lean_ctor_set(v___x_857_, 2, v___x_856_);
v___x_858_ = l_Lean_Syntax_node5(v___x_841_, v___x_850_, v___x_705_, v___y_854_, v___y_852_, v___y_853_, v___x_857_);
v___x_859_ = l_Lean_Syntax_node3(v___x_841_, v___x_843_, v___x_845_, v___x_848_, v___x_858_);
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 0);
lean_ctor_set(v___x_837_, 0, v___x_859_);
v___x_861_ = v___x_837_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
v___jp_863_:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = l_Array_append___redArg(v___x_847_, v___y_866_);
lean_dec_ref(v___y_866_);
lean_inc(v___x_841_);
v___x_868_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_868_, 0, v___x_841_);
lean_ctor_set(v___x_868_, 1, v___x_846_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
if (lean_obj_tag(v_loc_711_) == 1)
{
lean_object* v_val_869_; lean_object* v___x_870_; 
v_val_869_ = lean_ctor_get(v_loc_711_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_loc_711_, 1);
v___x_870_ = l_Array_mkArray1___redArg(v_val_869_);
v___y_852_ = v___y_864_;
v___y_853_ = v___x_868_;
v___y_854_ = v___y_865_;
v___y_855_ = v___x_870_;
goto v___jp_851_;
}
else
{
lean_object* v___x_871_; 
lean_dec(v_loc_711_);
v___x_871_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_852_ = v___y_864_;
v___y_853_ = v___x_868_;
v___y_854_ = v___y_865_;
v___y_855_ = v___x_871_;
goto v___jp_851_;
}
}
v___jp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = l_Array_append___redArg(v___x_847_, v___y_874_);
lean_dec_ref(v___y_874_);
lean_inc(v___x_841_);
v___x_876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_876_, 0, v___x_841_);
lean_ctor_set(v___x_876_, 1, v___x_846_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_val_877_ = lean_ctor_get(v_args_707_, 0);
v___x_878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_879_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_878_);
v___x_880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___x_841_, 4);
v___x_881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_841_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Array_append___redArg(v___x_847_, v_val_877_);
v___x_883_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_883_, 0, v___x_841_);
lean_ctor_set(v___x_883_, 1, v___x_846_);
lean_ctor_set(v___x_883_, 2, v___x_882_);
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_841_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_Syntax_node3(v___x_841_, v___x_879_, v___x_881_, v___x_883_, v___x_885_);
v___x_887_ = l_Array_mkArray1___redArg(v___x_886_);
v___y_864_ = v___x_876_;
v___y_865_ = v___y_873_;
v___y_866_ = v___x_887_;
goto v___jp_863_;
}
else
{
lean_object* v___x_888_; 
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_702_);
v___x_888_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_864_ = v___x_876_;
v___y_865_ = v___y_873_;
v___y_866_ = v___x_888_;
goto v___jp_863_;
}
}
v___jp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = l_Array_append___redArg(v___x_847_, v___y_890_);
lean_dec_ref(v___y_890_);
lean_inc(v___x_841_);
v___x_892_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_892_, 0, v___x_841_);
lean_ctor_set(v___x_892_, 1, v___x_846_);
lean_ctor_set(v___x_892_, 2, v___x_891_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_val_893_ = lean_ctor_get(v_only_708_, 0);
v___x_894_ = l_Lean_SourceInfo_fromRef(v_val_893_, v___x_709_);
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_896_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Array_mkArray1___redArg(v___x_896_);
v___y_873_ = v___x_892_;
v___y_874_ = v___x_897_;
goto v___jp_872_;
}
else
{
lean_object* v___x_898_; 
v___x_898_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_873_ = v___x_892_;
v___y_874_ = v___x_898_;
goto v___jp_872_;
}
}
}
else
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_969_; 
lean_del_object(v___x_837_);
v_isSharedCheck_969_ = !lean_is_exclusive(v_unfold_701_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v_unfold_701_, 0);
lean_dec(v_unused_970_);
v___x_904_ = v_unfold_701_;
v_isShared_905_ = v_isSharedCheck_969_;
goto v_resetjp_903_;
}
else
{
lean_dec(v_unfold_701_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_969_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_ref_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_956_; 
v_ref_906_ = lean_ctor_get(v___y_718_, 2);
v___x_907_ = 0;
v___x_908_ = l_Lean_SourceInfo_fromRef(v_ref_906_, v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13));
lean_inc_ref_n(v___x_704_, 2);
lean_inc_ref_n(v___x_703_, 2);
lean_inc_ref_n(v___x_702_, 2);
v___x_910_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_909_);
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14));
lean_inc(v___x_908_);
v___x_912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_908_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_914_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_913_);
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_916_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3);
if (lean_obj_tag(v___y_710_) == 0)
{
lean_object* v___x_965_; 
v___x_965_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_956_ = v___x_965_;
goto v___jp_955_;
}
else
{
lean_object* v_val_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_val_966_ = lean_ctor_get(v___y_710_, 0);
lean_inc(v_val_966_);
lean_dec_ref_known(v___y_710_, 1);
v___x_967_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_968_ = lean_array_push(v___x_967_, v_val_966_);
v___y_956_ = v___x_968_;
goto v___jp_955_;
}
v___jp_917_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_922_ = l_Array_append___redArg(v___x_916_, v___y_921_);
lean_dec_ref(v___y_921_);
lean_inc_n(v___x_908_, 2);
v___x_923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_923_, 0, v___x_908_);
lean_ctor_set(v___x_923_, 1, v___x_915_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
v___x_924_ = l_Lean_Syntax_node5(v___x_908_, v___x_914_, v___x_705_, v___y_919_, v___y_918_, v___y_920_, v___x_923_);
v___x_925_ = l_Lean_Syntax_node2(v___x_908_, v___x_910_, v___x_912_, v___x_924_);
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 0);
lean_ctor_set(v___x_904_, 0, v___x_925_);
v___x_927_ = v___x_904_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
v___jp_929_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = l_Array_append___redArg(v___x_916_, v___y_932_);
lean_dec_ref(v___y_932_);
lean_inc(v___x_908_);
v___x_934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_934_, 0, v___x_908_);
lean_ctor_set(v___x_934_, 1, v___x_915_);
lean_ctor_set(v___x_934_, 2, v___x_933_);
if (lean_obj_tag(v_loc_711_) == 1)
{
lean_object* v_val_935_; lean_object* v___x_936_; 
v_val_935_ = lean_ctor_get(v_loc_711_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_loc_711_, 1);
v___x_936_ = l_Array_mkArray1___redArg(v_val_935_);
v___y_918_ = v___y_930_;
v___y_919_ = v___y_931_;
v___y_920_ = v___x_934_;
v___y_921_ = v___x_936_;
goto v___jp_917_;
}
else
{
lean_object* v___x_937_; 
lean_dec(v_loc_711_);
v___x_937_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_918_ = v___y_930_;
v___y_919_ = v___y_931_;
v___y_920_ = v___x_934_;
v___y_921_ = v___x_937_;
goto v___jp_917_;
}
}
v___jp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = l_Array_append___redArg(v___x_916_, v___y_940_);
lean_dec_ref(v___y_940_);
lean_inc(v___x_908_);
v___x_942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_942_, 0, v___x_908_);
lean_ctor_set(v___x_942_, 1, v___x_915_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_val_943_ = lean_ctor_get(v_args_707_, 0);
v___x_944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_945_ = l_Lean_Name_mkStr4(v___x_702_, v___x_703_, v___x_704_, v___x_944_);
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___x_908_, 4);
v___x_947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_908_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = l_Array_append___redArg(v___x_916_, v_val_943_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_908_);
lean_ctor_set(v___x_949_, 1, v___x_915_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
v___x_950_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_908_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_Syntax_node3(v___x_908_, v___x_945_, v___x_947_, v___x_949_, v___x_951_);
v___x_953_ = l_Array_mkArray1___redArg(v___x_952_);
v___y_930_ = v___x_942_;
v___y_931_ = v___y_939_;
v___y_932_ = v___x_953_;
goto v___jp_929_;
}
else
{
lean_object* v___x_954_; 
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_702_);
v___x_954_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_930_ = v___x_942_;
v___y_931_ = v___y_939_;
v___y_932_ = v___x_954_;
goto v___jp_929_;
}
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = l_Array_append___redArg(v___x_916_, v___y_956_);
lean_dec_ref(v___y_956_);
lean_inc(v___x_908_);
v___x_958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_958_, 0, v___x_908_);
lean_ctor_set(v___x_958_, 1, v___x_915_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_val_959_ = lean_ctor_get(v_only_708_, 0);
v___x_960_ = l_Lean_SourceInfo_fromRef(v_val_959_, v___x_709_);
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_962_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Array_mkArray1___redArg(v___x_962_);
v___y_939_ = v___x_958_;
v___y_940_ = v___x_963_;
goto v___jp_938_;
}
else
{
lean_object* v___x_964_; 
v___x_964_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_939_ = v___x_958_;
v___y_940_ = v___x_964_;
goto v___jp_938_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object** _args){
lean_object* v_squeeze_973_ = _args[0];
lean_object* v_unfold_974_ = _args[1];
lean_object* v___x_975_ = _args[2];
lean_object* v___x_976_ = _args[3];
lean_object* v___x_977_ = _args[4];
lean_object* v___x_978_ = _args[5];
lean_object* v___x_979_ = _args[6];
lean_object* v_args_980_ = _args[7];
lean_object* v_only_981_ = _args[8];
lean_object* v___x_982_ = _args[9];
lean_object* v___y_983_ = _args[10];
lean_object* v_loc_984_ = _args[11];
lean_object* v___y_985_ = _args[12];
lean_object* v___y_986_ = _args[13];
lean_object* v___y_987_ = _args[14];
lean_object* v___y_988_ = _args[15];
lean_object* v___y_989_ = _args[16];
lean_object* v___y_990_ = _args[17];
lean_object* v___y_991_ = _args[18];
lean_object* v___y_992_ = _args[19];
lean_object* v___y_993_ = _args[20];
_start:
{
uint8_t v___x_93893__boxed_994_; lean_object* v_res_995_; 
v___x_93893__boxed_994_ = lean_unbox(v___x_982_);
v_res_995_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v_squeeze_973_, v_unfold_974_, v___x_975_, v___x_976_, v___x_977_, v___x_978_, v___x_979_, v_args_980_, v_only_981_, v___x_93893__boxed_994_, v___y_983_, v_loc_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v_only_981_);
lean_dec(v_args_980_);
lean_dec(v___x_979_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_996_, lean_object* v_trees_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc_ref(v___y_1002_);
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
v___x_1007_ = lean_apply_9(v_a_996_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, lean_box(0));
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1016_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1016_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_a_1008_);
lean_ctor_set(v___x_1012_, 1, v_trees_997_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1012_);
v___x_1014_ = v___x_1010_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_trees_997_);
v_a_1017_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1007_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1007_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object* v_a_1025_, lean_object* v_trees_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1025_, v_trees_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1036_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1043_, lean_object* v_a_1044_, uint8_t v___x_1045_, lean_object* v_a_1046_, lean_object* v_mvarCounter_1047_, lean_object* v___x_1048_, uint8_t v___x_1049_, lean_object* v___x_1050_, uint8_t v_useReducible_1051_, uint8_t v___x_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
lean_inc(v_a_1043_);
v___x_1062_ = l_Lean_MVarId_getType(v_a_1043_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc_n(v_a_1063_, 2);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = l_Lean_mkIdent(v_a_1044_);
v___x_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_a_1063_);
v___x_1066_ = l_Lean_Elab_Term_elabTerm(v___x_1064_, v___x_1065_, v___x_1045_, v___x_1045_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___x_1101_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1101_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1049_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1284_; 
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v___x_1101_, 0);
lean_dec(v_unused_1285_);
v___x_1103_ = v___x_1101_;
v_isShared_1104_ = v_isSharedCheck_1284_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v___x_1101_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1284_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; 
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v_a_1067_);
v___x_1105_ = lean_infer_type(v_a_1067_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; uint8_t v_____do__lift_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1127_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
if (v_useReducible_1051_ == 0)
{
lean_object* v___x_1138_; uint8_t v_foApprox_1139_; uint8_t v_ctxApprox_1140_; uint8_t v_quasiPatternApprox_1141_; uint8_t v_constApprox_1142_; uint8_t v_isDefEqStuckEx_1143_; uint8_t v_unificationHints_1144_; uint8_t v_proofIrrelevance_1145_; uint8_t v_offsetCnstrs_1146_; uint8_t v_transparency_1147_; uint8_t v_etaStruct_1148_; uint8_t v_univApprox_1149_; uint8_t v_iota_1150_; uint8_t v_beta_1151_; uint8_t v_proj_1152_; uint8_t v_zeta_1153_; uint8_t v_zetaDelta_1154_; uint8_t v_zetaUnused_1155_; uint8_t v_zetaHave_1156_; uint8_t v_canUnfoldPredicateConfig_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1188_; 
v___x_1138_ = l_Lean_Meta_Context_config(v___y_1057_);
v_foApprox_1139_ = lean_ctor_get_uint8(v___x_1138_, 0);
v_ctxApprox_1140_ = lean_ctor_get_uint8(v___x_1138_, 1);
v_quasiPatternApprox_1141_ = lean_ctor_get_uint8(v___x_1138_, 2);
v_constApprox_1142_ = lean_ctor_get_uint8(v___x_1138_, 3);
v_isDefEqStuckEx_1143_ = lean_ctor_get_uint8(v___x_1138_, 4);
v_unificationHints_1144_ = lean_ctor_get_uint8(v___x_1138_, 5);
v_proofIrrelevance_1145_ = lean_ctor_get_uint8(v___x_1138_, 6);
v_offsetCnstrs_1146_ = lean_ctor_get_uint8(v___x_1138_, 8);
v_transparency_1147_ = lean_ctor_get_uint8(v___x_1138_, 9);
v_etaStruct_1148_ = lean_ctor_get_uint8(v___x_1138_, 10);
v_univApprox_1149_ = lean_ctor_get_uint8(v___x_1138_, 11);
v_iota_1150_ = lean_ctor_get_uint8(v___x_1138_, 12);
v_beta_1151_ = lean_ctor_get_uint8(v___x_1138_, 13);
v_proj_1152_ = lean_ctor_get_uint8(v___x_1138_, 14);
v_zeta_1153_ = lean_ctor_get_uint8(v___x_1138_, 15);
v_zetaDelta_1154_ = lean_ctor_get_uint8(v___x_1138_, 16);
v_zetaUnused_1155_ = lean_ctor_get_uint8(v___x_1138_, 17);
v_zetaHave_1156_ = lean_ctor_get_uint8(v___x_1138_, 18);
v_canUnfoldPredicateConfig_1157_ = lean_ctor_get_uint8(v___x_1138_, 19);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1159_ = v___x_1138_;
v_isShared_1160_ = v_isSharedCheck_1188_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v___x_1138_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1188_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v_trackZetaDelta_1161_; lean_object* v_zetaDeltaSet_1162_; lean_object* v_lctx_1163_; lean_object* v_localInstances_1164_; lean_object* v_defEqCtx_x3f_1165_; lean_object* v_synthPendingDepth_1166_; lean_object* v_customCanUnfoldPredicate_x3f_1167_; uint8_t v_univApprox_1168_; uint8_t v_inTypeClassResolution_1169_; uint8_t v_cacheInferType_1170_; lean_object* v___x_1172_; 
v_trackZetaDelta_1161_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7);
v_zetaDeltaSet_1162_ = lean_ctor_get(v___y_1057_, 1);
v_lctx_1163_ = lean_ctor_get(v___y_1057_, 2);
v_localInstances_1164_ = lean_ctor_get(v___y_1057_, 3);
v_defEqCtx_x3f_1165_ = lean_ctor_get(v___y_1057_, 4);
v_synthPendingDepth_1166_ = lean_ctor_get(v___y_1057_, 5);
v_customCanUnfoldPredicate_x3f_1167_ = lean_ctor_get(v___y_1057_, 6);
v_univApprox_1168_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1169_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 2);
v_cacheInferType_1170_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 3);
if (v_isShared_1160_ == 0)
{
v___x_1172_ = v___x_1159_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 0, v_foApprox_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 1, v_ctxApprox_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 2, v_quasiPatternApprox_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 3, v_constApprox_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 4, v_isDefEqStuckEx_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 5, v_unificationHints_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 6, v_proofIrrelevance_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 8, v_offsetCnstrs_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 9, v_transparency_1147_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 10, v_etaStruct_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 11, v_univApprox_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 12, v_iota_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 13, v_beta_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 14, v_proj_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 15, v_zeta_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 16, v_zetaDelta_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 17, v_zetaUnused_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 18, v_zetaHave_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, 19, v_canUnfoldPredicateConfig_1157_);
v___x_1172_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
uint64_t v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_ctor_set_uint8(v___x_1172_, 7, v___x_1052_);
v___x_1173_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set_uint64(v___x_1174_, sizeof(void*)*1, v___x_1173_);
lean_inc(v_customCanUnfoldPredicate_x3f_1167_);
lean_inc(v_synthPendingDepth_1166_);
lean_inc(v_defEqCtx_x3f_1165_);
lean_inc_ref(v_localInstances_1164_);
lean_inc_ref(v_lctx_1163_);
lean_inc(v_zetaDeltaSet_1162_);
v___x_1175_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
lean_ctor_set(v___x_1175_, 1, v_zetaDeltaSet_1162_);
lean_ctor_set(v___x_1175_, 2, v_lctx_1163_);
lean_ctor_set(v___x_1175_, 3, v_localInstances_1164_);
lean_ctor_set(v___x_1175_, 4, v_defEqCtx_x3f_1165_);
lean_ctor_set(v___x_1175_, 5, v_synthPendingDepth_1166_);
lean_ctor_set(v___x_1175_, 6, v_customCanUnfoldPredicate_x3f_1167_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*7, v_trackZetaDelta_1161_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*7 + 1, v_univApprox_1168_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1169_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*7 + 3, v_cacheInferType_1170_);
lean_inc(v_a_1106_);
lean_inc(v_a_1063_);
v___x_1176_ = l_Lean_Meta_isExprDefEq(v_a_1063_, v_a_1106_, v___x_1175_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec_ref_known(v___x_1175_, 7);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; uint8_t v___x_1178_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = lean_unbox(v_a_1177_);
lean_dec(v_a_1177_);
v_____do__lift_1108_ = v___x_1178_;
v___y_1109_ = v___y_1053_;
v___y_1110_ = v___y_1054_;
v___y_1111_ = v___y_1055_;
v___y_1112_ = v___y_1056_;
v___y_1113_ = v___y_1057_;
v___y_1114_ = v___y_1058_;
v___y_1115_ = v___y_1059_;
v___y_1116_ = v___y_1060_;
goto v___jp_1107_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_a_1106_);
lean_del_object(v___x_1103_);
lean_dec(v_a_1067_);
lean_dec(v_a_1063_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1043_);
v_a_1179_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1176_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1176_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
else
{
lean_object* v___x_1189_; uint8_t v_foApprox_1190_; uint8_t v_ctxApprox_1191_; uint8_t v_quasiPatternApprox_1192_; uint8_t v_constApprox_1193_; uint8_t v_isDefEqStuckEx_1194_; uint8_t v_unificationHints_1195_; uint8_t v_proofIrrelevance_1196_; uint8_t v_offsetCnstrs_1197_; uint8_t v_transparency_1198_; uint8_t v_etaStruct_1199_; uint8_t v_univApprox_1200_; uint8_t v_iota_1201_; uint8_t v_beta_1202_; uint8_t v_proj_1203_; uint8_t v_zeta_1204_; uint8_t v_zetaDelta_1205_; uint8_t v_zetaUnused_1206_; uint8_t v_zetaHave_1207_; uint8_t v_canUnfoldPredicateConfig_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1275_; 
v___x_1189_ = l_Lean_Meta_Context_config(v___y_1057_);
v_foApprox_1190_ = lean_ctor_get_uint8(v___x_1189_, 0);
v_ctxApprox_1191_ = lean_ctor_get_uint8(v___x_1189_, 1);
v_quasiPatternApprox_1192_ = lean_ctor_get_uint8(v___x_1189_, 2);
v_constApprox_1193_ = lean_ctor_get_uint8(v___x_1189_, 3);
v_isDefEqStuckEx_1194_ = lean_ctor_get_uint8(v___x_1189_, 4);
v_unificationHints_1195_ = lean_ctor_get_uint8(v___x_1189_, 5);
v_proofIrrelevance_1196_ = lean_ctor_get_uint8(v___x_1189_, 6);
v_offsetCnstrs_1197_ = lean_ctor_get_uint8(v___x_1189_, 8);
v_transparency_1198_ = lean_ctor_get_uint8(v___x_1189_, 9);
v_etaStruct_1199_ = lean_ctor_get_uint8(v___x_1189_, 10);
v_univApprox_1200_ = lean_ctor_get_uint8(v___x_1189_, 11);
v_iota_1201_ = lean_ctor_get_uint8(v___x_1189_, 12);
v_beta_1202_ = lean_ctor_get_uint8(v___x_1189_, 13);
v_proj_1203_ = lean_ctor_get_uint8(v___x_1189_, 14);
v_zeta_1204_ = lean_ctor_get_uint8(v___x_1189_, 15);
v_zetaDelta_1205_ = lean_ctor_get_uint8(v___x_1189_, 16);
v_zetaUnused_1206_ = lean_ctor_get_uint8(v___x_1189_, 17);
v_zetaHave_1207_ = lean_ctor_get_uint8(v___x_1189_, 18);
v_canUnfoldPredicateConfig_1208_ = lean_ctor_get_uint8(v___x_1189_, 19);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1210_ = v___x_1189_;
v_isShared_1211_ = v_isSharedCheck_1275_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v___x_1189_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1275_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
uint8_t v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = 2;
v___x_1213_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1198_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v_keyedConfig_1214_; uint8_t v_trackZetaDelta_1215_; lean_object* v_zetaDeltaSet_1216_; lean_object* v_lctx_1217_; lean_object* v_localInstances_1218_; lean_object* v_defEqCtx_x3f_1219_; lean_object* v_synthPendingDepth_1220_; lean_object* v_customCanUnfoldPredicate_x3f_1221_; uint8_t v_univApprox_1222_; uint8_t v_inTypeClassResolution_1223_; uint8_t v_cacheInferType_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v_foApprox_1228_; uint8_t v_ctxApprox_1229_; uint8_t v_quasiPatternApprox_1230_; uint8_t v_constApprox_1231_; uint8_t v_isDefEqStuckEx_1232_; uint8_t v_unificationHints_1233_; uint8_t v_proofIrrelevance_1234_; uint8_t v_offsetCnstrs_1235_; uint8_t v_transparency_1236_; uint8_t v_etaStruct_1237_; uint8_t v_univApprox_1238_; uint8_t v_iota_1239_; uint8_t v_beta_1240_; uint8_t v_proj_1241_; uint8_t v_zeta_1242_; uint8_t v_zetaDelta_1243_; uint8_t v_zetaUnused_1244_; uint8_t v_zetaHave_1245_; uint8_t v_canUnfoldPredicateConfig_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
lean_del_object(v___x_1210_);
v_keyedConfig_1214_ = lean_ctor_get(v___y_1057_, 0);
v_trackZetaDelta_1215_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7);
v_zetaDeltaSet_1216_ = lean_ctor_get(v___y_1057_, 1);
v_lctx_1217_ = lean_ctor_get(v___y_1057_, 2);
v_localInstances_1218_ = lean_ctor_get(v___y_1057_, 3);
v_defEqCtx_x3f_1219_ = lean_ctor_get(v___y_1057_, 4);
v_synthPendingDepth_1220_ = lean_ctor_get(v___y_1057_, 5);
v_customCanUnfoldPredicate_x3f_1221_ = lean_ctor_get(v___y_1057_, 6);
v_univApprox_1222_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1223_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 2);
v_cacheInferType_1224_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1214_);
v___x_1225_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1212_, v_keyedConfig_1214_);
lean_inc(v_customCanUnfoldPredicate_x3f_1221_);
lean_inc(v_synthPendingDepth_1220_);
lean_inc(v_defEqCtx_x3f_1219_);
lean_inc_ref(v_localInstances_1218_);
lean_inc_ref(v_lctx_1217_);
lean_inc(v_zetaDeltaSet_1216_);
v___x_1226_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_zetaDeltaSet_1216_);
lean_ctor_set(v___x_1226_, 2, v_lctx_1217_);
lean_ctor_set(v___x_1226_, 3, v_localInstances_1218_);
lean_ctor_set(v___x_1226_, 4, v_defEqCtx_x3f_1219_);
lean_ctor_set(v___x_1226_, 5, v_synthPendingDepth_1220_);
lean_ctor_set(v___x_1226_, 6, v_customCanUnfoldPredicate_x3f_1221_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7, v_trackZetaDelta_1215_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7 + 1, v_univApprox_1222_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1223_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*7 + 3, v_cacheInferType_1224_);
v___x_1227_ = l_Lean_Meta_Context_config(v___x_1226_);
lean_dec_ref_known(v___x_1226_, 7);
v_foApprox_1228_ = lean_ctor_get_uint8(v___x_1227_, 0);
v_ctxApprox_1229_ = lean_ctor_get_uint8(v___x_1227_, 1);
v_quasiPatternApprox_1230_ = lean_ctor_get_uint8(v___x_1227_, 2);
v_constApprox_1231_ = lean_ctor_get_uint8(v___x_1227_, 3);
v_isDefEqStuckEx_1232_ = lean_ctor_get_uint8(v___x_1227_, 4);
v_unificationHints_1233_ = lean_ctor_get_uint8(v___x_1227_, 5);
v_proofIrrelevance_1234_ = lean_ctor_get_uint8(v___x_1227_, 6);
v_offsetCnstrs_1235_ = lean_ctor_get_uint8(v___x_1227_, 8);
v_transparency_1236_ = lean_ctor_get_uint8(v___x_1227_, 9);
v_etaStruct_1237_ = lean_ctor_get_uint8(v___x_1227_, 10);
v_univApprox_1238_ = lean_ctor_get_uint8(v___x_1227_, 11);
v_iota_1239_ = lean_ctor_get_uint8(v___x_1227_, 12);
v_beta_1240_ = lean_ctor_get_uint8(v___x_1227_, 13);
v_proj_1241_ = lean_ctor_get_uint8(v___x_1227_, 14);
v_zeta_1242_ = lean_ctor_get_uint8(v___x_1227_, 15);
v_zetaDelta_1243_ = lean_ctor_get_uint8(v___x_1227_, 16);
v_zetaUnused_1244_ = lean_ctor_get_uint8(v___x_1227_, 17);
v_zetaHave_1245_ = lean_ctor_get_uint8(v___x_1227_, 18);
v_canUnfoldPredicateConfig_1246_ = lean_ctor_get_uint8(v___x_1227_, 19);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1248_ = v___x_1227_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_dec(v___x_1227_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 0, v_foApprox_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 1, v_ctxApprox_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 2, v_quasiPatternApprox_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 3, v_constApprox_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 4, v_isDefEqStuckEx_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 5, v_unificationHints_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 6, v_proofIrrelevance_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 8, v_offsetCnstrs_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 9, v_transparency_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 10, v_etaStruct_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 11, v_univApprox_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 12, v_iota_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 13, v_beta_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 14, v_proj_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 15, v_zeta_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 16, v_zetaDelta_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 17, v_zetaUnused_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 18, v_zetaHave_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, 19, v_canUnfoldPredicateConfig_1246_);
v___x_1251_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
uint64_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_ctor_set_uint8(v___x_1251_, 7, v___x_1052_);
v___x_1252_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set_uint64(v___x_1253_, sizeof(void*)*1, v___x_1252_);
lean_inc(v_customCanUnfoldPredicate_x3f_1221_);
lean_inc(v_synthPendingDepth_1220_);
lean_inc(v_defEqCtx_x3f_1219_);
lean_inc_ref(v_localInstances_1218_);
lean_inc_ref(v_lctx_1217_);
lean_inc(v_zetaDeltaSet_1216_);
v___x_1254_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v_zetaDeltaSet_1216_);
lean_ctor_set(v___x_1254_, 2, v_lctx_1217_);
lean_ctor_set(v___x_1254_, 3, v_localInstances_1218_);
lean_ctor_set(v___x_1254_, 4, v_defEqCtx_x3f_1219_);
lean_ctor_set(v___x_1254_, 5, v_synthPendingDepth_1220_);
lean_ctor_set(v___x_1254_, 6, v_customCanUnfoldPredicate_x3f_1221_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*7, v_trackZetaDelta_1215_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*7 + 1, v_univApprox_1222_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1223_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*7 + 3, v_cacheInferType_1224_);
lean_inc(v_a_1106_);
lean_inc(v_a_1063_);
v___x_1255_ = l_Lean_Meta_isExprDefEq(v_a_1063_, v_a_1106_, v___x_1254_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec_ref_known(v___x_1254_, 7);
v___y_1127_ = v___x_1255_;
goto v___jp_1126_;
}
}
}
else
{
uint8_t v_trackZetaDelta_1258_; lean_object* v_zetaDeltaSet_1259_; lean_object* v_lctx_1260_; lean_object* v_localInstances_1261_; lean_object* v_defEqCtx_x3f_1262_; lean_object* v_synthPendingDepth_1263_; lean_object* v_customCanUnfoldPredicate_x3f_1264_; uint8_t v_univApprox_1265_; uint8_t v_inTypeClassResolution_1266_; uint8_t v_cacheInferType_1267_; lean_object* v___x_1269_; 
v_trackZetaDelta_1258_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7);
v_zetaDeltaSet_1259_ = lean_ctor_get(v___y_1057_, 1);
v_lctx_1260_ = lean_ctor_get(v___y_1057_, 2);
v_localInstances_1261_ = lean_ctor_get(v___y_1057_, 3);
v_defEqCtx_x3f_1262_ = lean_ctor_get(v___y_1057_, 4);
v_synthPendingDepth_1263_ = lean_ctor_get(v___y_1057_, 5);
v_customCanUnfoldPredicate_x3f_1264_ = lean_ctor_get(v___y_1057_, 6);
v_univApprox_1265_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1266_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 2);
v_cacheInferType_1267_ = lean_ctor_get_uint8(v___y_1057_, sizeof(void*)*7 + 3);
if (v_isShared_1211_ == 0)
{
v___x_1269_ = v___x_1210_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 0, v_foApprox_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 1, v_ctxApprox_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 2, v_quasiPatternApprox_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 3, v_constApprox_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 4, v_isDefEqStuckEx_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 5, v_unificationHints_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 6, v_proofIrrelevance_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 8, v_offsetCnstrs_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 9, v_transparency_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 10, v_etaStruct_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 11, v_univApprox_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 12, v_iota_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 13, v_beta_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 14, v_proj_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 15, v_zeta_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 16, v_zetaDelta_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 17, v_zetaUnused_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 18, v_zetaHave_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, 19, v_canUnfoldPredicateConfig_1208_);
v___x_1269_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
uint64_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_ctor_set_uint8(v___x_1269_, 7, v___x_1052_);
v___x_1270_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set_uint64(v___x_1271_, sizeof(void*)*1, v___x_1270_);
lean_inc(v_customCanUnfoldPredicate_x3f_1264_);
lean_inc(v_synthPendingDepth_1263_);
lean_inc(v_defEqCtx_x3f_1262_);
lean_inc_ref(v_localInstances_1261_);
lean_inc_ref(v_lctx_1260_);
lean_inc(v_zetaDeltaSet_1259_);
v___x_1272_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_zetaDeltaSet_1259_);
lean_ctor_set(v___x_1272_, 2, v_lctx_1260_);
lean_ctor_set(v___x_1272_, 3, v_localInstances_1261_);
lean_ctor_set(v___x_1272_, 4, v_defEqCtx_x3f_1262_);
lean_ctor_set(v___x_1272_, 5, v_synthPendingDepth_1263_);
lean_ctor_set(v___x_1272_, 6, v_customCanUnfoldPredicate_x3f_1264_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7, v_trackZetaDelta_1258_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7 + 1, v_univApprox_1265_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1266_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*7 + 3, v_cacheInferType_1267_);
lean_inc(v_a_1106_);
lean_inc(v_a_1063_);
v___x_1273_ = l_Lean_Meta_isExprDefEq(v_a_1063_, v_a_1106_, v___x_1272_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec_ref_known(v___x_1272_, 7);
v___y_1127_ = v___x_1273_;
goto v___jp_1126_;
}
}
}
}
v___jp_1107_:
{
if (v_____do__lift_1108_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1117_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1);
lean_inc_ref(v_a_1046_);
v___x_1118_ = l_Lean_indentExpr(v_a_1046_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1121_);
v___x_1123_ = v___x_1103_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; 
lean_inc(v_a_1067_);
v___x_1124_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1123_, v_a_1063_, v_a_1106_, v_a_1067_, v___x_1050_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec_ref(v___x_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_dec_ref_known(v___x_1124_, 1);
v___y_1069_ = v___y_1109_;
v___y_1070_ = v___y_1110_;
v___y_1071_ = v___y_1111_;
v___y_1072_ = v___y_1112_;
v___y_1073_ = v___y_1113_;
v___y_1074_ = v___y_1114_;
v___y_1075_ = v___y_1115_;
v___y_1076_ = v___y_1116_;
goto v___jp_1068_;
}
else
{
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v_a_1067_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1043_);
return v___x_1124_;
}
}
}
else
{
lean_dec(v_a_1106_);
lean_del_object(v___x_1103_);
lean_dec(v_a_1063_);
lean_dec(v___x_1050_);
v___y_1069_ = v___y_1109_;
v___y_1070_ = v___y_1110_;
v___y_1071_ = v___y_1111_;
v___y_1072_ = v___y_1112_;
v___y_1073_ = v___y_1113_;
v___y_1074_ = v___y_1114_;
v___y_1075_ = v___y_1115_;
v___y_1076_ = v___y_1116_;
goto v___jp_1068_;
}
}
v___jp_1126_:
{
if (lean_obj_tag(v___y_1127_) == 0)
{
lean_object* v_a_1128_; uint8_t v___x_1129_; 
v_a_1128_ = lean_ctor_get(v___y_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___y_1127_, 1);
v___x_1129_ = lean_unbox(v_a_1128_);
lean_dec(v_a_1128_);
v_____do__lift_1108_ = v___x_1129_;
v___y_1109_ = v___y_1053_;
v___y_1110_ = v___y_1054_;
v___y_1111_ = v___y_1055_;
v___y_1112_ = v___y_1056_;
v___y_1113_ = v___y_1057_;
v___y_1114_ = v___y_1058_;
v___y_1115_ = v___y_1059_;
v___y_1116_ = v___y_1060_;
goto v___jp_1107_;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_a_1106_);
lean_del_object(v___x_1103_);
lean_dec(v_a_1067_);
lean_dec(v_a_1063_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1043_);
v_a_1130_ = lean_ctor_get(v___y_1127_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___y_1127_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___y_1127_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___y_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_del_object(v___x_1103_);
lean_dec(v_a_1067_);
lean_dec(v_a_1063_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1043_);
v_a_1276_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1105_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1105_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_dec(v_a_1067_);
lean_dec(v_a_1063_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1043_);
return v___x_1101_;
}
v___jp_1068_:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_getMVars(v_a_1046_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1078_, v_mvarCounter_1047_, v___y_1074_);
lean_dec(v_a_1078_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1080_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v_a_1080_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; 
lean_dec_ref_known(v___x_1081_, 1);
v___x_1082_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_1043_, v___y_1070_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref_known(v___x_1082_, 1);
v___x_1083_ = l_Lean_Name_mkStr1(v___x_1048_);
v___x_1084_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1083_, v_a_1067_, v___x_1049_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v___x_1084_;
}
else
{
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_a_1067_);
lean_dec_ref(v___x_1048_);
return v___x_1082_;
}
}
else
{
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_a_1067_);
lean_dec_ref(v___x_1048_);
lean_dec(v_a_1043_);
return v___x_1081_;
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_a_1067_);
lean_dec_ref(v___x_1048_);
lean_dec(v_a_1043_);
v_a_1085_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1079_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1079_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_a_1067_);
lean_dec_ref(v___x_1048_);
lean_dec(v_a_1043_);
v_a_1093_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1077_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1077_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
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
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_a_1063_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1043_);
v_a_1286_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1066_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1066_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1044_);
lean_dec(v_a_1043_);
v_a_1294_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1062_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1062_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object** _args){
lean_object* v_a_1302_ = _args[0];
lean_object* v_a_1303_ = _args[1];
lean_object* v___x_1304_ = _args[2];
lean_object* v_a_1305_ = _args[3];
lean_object* v_mvarCounter_1306_ = _args[4];
lean_object* v___x_1307_ = _args[5];
lean_object* v___x_1308_ = _args[6];
lean_object* v___x_1309_ = _args[7];
lean_object* v_useReducible_1310_ = _args[8];
lean_object* v___x_1311_ = _args[9];
lean_object* v___y_1312_ = _args[10];
lean_object* v___y_1313_ = _args[11];
lean_object* v___y_1314_ = _args[12];
lean_object* v___y_1315_ = _args[13];
lean_object* v___y_1316_ = _args[14];
lean_object* v___y_1317_ = _args[15];
lean_object* v___y_1318_ = _args[16];
lean_object* v___y_1319_ = _args[17];
lean_object* v___y_1320_ = _args[18];
_start:
{
uint8_t v___x_94528__boxed_1321_; uint8_t v___x_94531__boxed_1322_; uint8_t v_useReducible_boxed_1323_; uint8_t v___x_94533__boxed_1324_; lean_object* v_res_1325_; 
v___x_94528__boxed_1321_ = lean_unbox(v___x_1304_);
v___x_94531__boxed_1322_ = lean_unbox(v___x_1308_);
v_useReducible_boxed_1323_ = lean_unbox(v_useReducible_1310_);
v___x_94533__boxed_1324_ = lean_unbox(v___x_1311_);
v_res_1325_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1302_, v_a_1303_, v___x_94528__boxed_1321_, v_a_1305_, v_mvarCounter_1306_, v___x_1307_, v___x_94531__boxed_1322_, v___x_1309_, v_useReducible_boxed_1323_, v___x_94533__boxed_1324_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v_mvarCounter_1306_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v_infoState_1337_; lean_object* v_env_1338_; lean_object* v_nextMacroScope_1339_; lean_object* v_ngen_1340_; lean_object* v_auxDeclNGen_1341_; lean_object* v_traceState_1342_; lean_object* v_cache_1343_; lean_object* v_recordedDeps_1344_; lean_object* v_messages_1345_; lean_object* v_snapshotTasks_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1367_; 
v___x_1336_ = lean_st_ref_take(v___y_1334_);
v_infoState_1337_ = lean_ctor_get(v___x_1336_, 8);
v_env_1338_ = lean_ctor_get(v___x_1336_, 0);
v_nextMacroScope_1339_ = lean_ctor_get(v___x_1336_, 1);
v_ngen_1340_ = lean_ctor_get(v___x_1336_, 2);
v_auxDeclNGen_1341_ = lean_ctor_get(v___x_1336_, 3);
v_traceState_1342_ = lean_ctor_get(v___x_1336_, 4);
v_cache_1343_ = lean_ctor_get(v___x_1336_, 5);
v_recordedDeps_1344_ = lean_ctor_get(v___x_1336_, 6);
v_messages_1345_ = lean_ctor_get(v___x_1336_, 7);
v_snapshotTasks_1346_ = lean_ctor_get(v___x_1336_, 9);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1348_ = v___x_1336_;
v_isShared_1349_ = v_isSharedCheck_1367_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snapshotTasks_1346_);
lean_inc(v_infoState_1337_);
lean_inc(v_messages_1345_);
lean_inc(v_recordedDeps_1344_);
lean_inc(v_cache_1343_);
lean_inc(v_traceState_1342_);
lean_inc(v_auxDeclNGen_1341_);
lean_inc(v_ngen_1340_);
lean_inc(v_nextMacroScope_1339_);
lean_inc(v_env_1338_);
lean_dec(v___x_1336_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1367_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
uint8_t v_enabled_1350_; lean_object* v_assignment_1351_; lean_object* v_lazyAssignment_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1365_; 
v_enabled_1350_ = lean_ctor_get_uint8(v_infoState_1337_, sizeof(void*)*3);
v_assignment_1351_ = lean_ctor_get(v_infoState_1337_, 0);
v_lazyAssignment_1352_ = lean_ctor_get(v_infoState_1337_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_infoState_1337_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_infoState_1337_, 2);
lean_dec(v_unused_1366_);
v___x_1354_ = v_infoState_1337_;
v_isShared_1355_ = v_isSharedCheck_1365_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_lazyAssignment_1352_);
lean_inc(v_assignment_1351_);
lean_dec(v_infoState_1337_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1365_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_box(0);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 2, v_a_1326_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_assignment_1351_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_lazyAssignment_1352_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_a_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*3, v_enabled_1350_);
v___x_1358_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 8, v___x_1358_);
v___x_1360_ = v___x_1348_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_env_1338_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_nextMacroScope_1339_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_ngen_1340_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_auxDeclNGen_1341_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_traceState_1342_);
lean_ctor_set(v_reuseFailAlloc_1363_, 5, v_cache_1343_);
lean_ctor_set(v_reuseFailAlloc_1363_, 6, v_recordedDeps_1344_);
lean_ctor_set(v_reuseFailAlloc_1363_, 7, v_messages_1345_);
lean_ctor_set(v_reuseFailAlloc_1363_, 8, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1363_, 9, v_snapshotTasks_1346_);
v___x_1360_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_st_ref_put(v___y_1334_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1356_);
return v___x_1362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1379_, lean_object* v_mkInfoTree_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v_a_1388_, lean_object* v_a_x3f_1389_){
_start:
{
lean_object* v___x_1391_; lean_object* v_infoState_1392_; lean_object* v_trees_1393_; lean_object* v___x_1394_; 
v___x_1391_ = lean_st_ref_get(v___y_1379_);
v_infoState_1392_ = lean_ctor_get(v___x_1391_, 8);
lean_inc_ref(v_infoState_1392_);
lean_dec(v___x_1391_);
v_trees_1393_ = lean_ctor_get(v_infoState_1392_, 2);
lean_inc_ref(v_trees_1393_);
lean_dec_ref(v_infoState_1392_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1387_);
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v___y_1384_);
lean_inc_ref(v___y_1383_);
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
v___x_1394_ = lean_apply_10(v_mkInfoTree_1380_, v_trees_1393_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1379_, lean_box(0));
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1434_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1434_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1434_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v_infoState_1400_; lean_object* v_env_1401_; lean_object* v_nextMacroScope_1402_; lean_object* v_ngen_1403_; lean_object* v_auxDeclNGen_1404_; lean_object* v_traceState_1405_; lean_object* v_cache_1406_; lean_object* v_recordedDeps_1407_; lean_object* v_messages_1408_; lean_object* v_snapshotTasks_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1433_; 
v___x_1399_ = lean_st_ref_take(v___y_1379_);
v_infoState_1400_ = lean_ctor_get(v___x_1399_, 8);
v_env_1401_ = lean_ctor_get(v___x_1399_, 0);
v_nextMacroScope_1402_ = lean_ctor_get(v___x_1399_, 1);
v_ngen_1403_ = lean_ctor_get(v___x_1399_, 2);
v_auxDeclNGen_1404_ = lean_ctor_get(v___x_1399_, 3);
v_traceState_1405_ = lean_ctor_get(v___x_1399_, 4);
v_cache_1406_ = lean_ctor_get(v___x_1399_, 5);
v_recordedDeps_1407_ = lean_ctor_get(v___x_1399_, 6);
v_messages_1408_ = lean_ctor_get(v___x_1399_, 7);
v_snapshotTasks_1409_ = lean_ctor_get(v___x_1399_, 9);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1411_ = v___x_1399_;
v_isShared_1412_ = v_isSharedCheck_1433_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_snapshotTasks_1409_);
lean_inc(v_infoState_1400_);
lean_inc(v_messages_1408_);
lean_inc(v_recordedDeps_1407_);
lean_inc(v_cache_1406_);
lean_inc(v_traceState_1405_);
lean_inc(v_auxDeclNGen_1404_);
lean_inc(v_ngen_1403_);
lean_inc(v_nextMacroScope_1402_);
lean_inc(v_env_1401_);
lean_dec(v___x_1399_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1433_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
uint8_t v_enabled_1413_; lean_object* v_assignment_1414_; lean_object* v_lazyAssignment_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1431_; 
v_enabled_1413_ = lean_ctor_get_uint8(v_infoState_1400_, sizeof(void*)*3);
v_assignment_1414_ = lean_ctor_get(v_infoState_1400_, 0);
v_lazyAssignment_1415_ = lean_ctor_get(v_infoState_1400_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_infoState_1400_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v_infoState_1400_, 2);
lean_dec(v_unused_1432_);
v___x_1417_ = v_infoState_1400_;
v_isShared_1418_ = v_isSharedCheck_1431_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_lazyAssignment_1415_);
lean_inc(v_assignment_1414_);
lean_dec(v_infoState_1400_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1431_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Lean_PersistentArray_push___redArg(v_a_1388_, v_a_1395_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 2, v___x_1420_);
v___x_1422_ = v___x_1417_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_assignment_1414_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_lazyAssignment_1415_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v___x_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1430_, sizeof(void*)*3, v_enabled_1413_);
v___x_1422_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 8, v___x_1422_);
v___x_1424_ = v___x_1411_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_env_1401_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_nextMacroScope_1402_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_ngen_1403_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_auxDeclNGen_1404_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_traceState_1405_);
lean_ctor_set(v_reuseFailAlloc_1429_, 5, v_cache_1406_);
lean_ctor_set(v_reuseFailAlloc_1429_, 6, v_recordedDeps_1407_);
lean_ctor_set(v_reuseFailAlloc_1429_, 7, v_messages_1408_);
lean_ctor_set(v_reuseFailAlloc_1429_, 8, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1429_, 9, v_snapshotTasks_1409_);
v___x_1424_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_st_ref_put(v___y_1379_, v___x_1424_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1419_);
v___x_1427_ = v___x_1397_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1419_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v_a_1388_);
v_a_1435_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1394_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1394_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1443_, lean_object* v_mkInfoTree_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v_a_1452_, lean_object* v_a_x3f_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1443_, v_mkInfoTree_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v_a_1452_, v_a_x3f_1453_);
lean_dec(v_a_x3f_1453_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1443_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1456_, lean_object* v_mkInfoTree_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v_infoState_1468_; uint8_t v_enabled_1469_; 
v___x_1467_ = lean_st_ref_get(v___y_1465_);
v_infoState_1468_ = lean_ctor_get(v___x_1467_, 8);
lean_inc_ref(v_infoState_1468_);
lean_dec(v___x_1467_);
v_enabled_1469_ = lean_ctor_get_uint8(v_infoState_1468_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1468_);
if (v_enabled_1469_ == 0)
{
lean_object* v___x_1470_; 
lean_dec_ref(v_mkInfoTree_1457_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
v___x_1470_ = lean_apply_9(v_x_1456_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, lean_box(0));
return v___x_1470_;
}
else
{
lean_object* v___x_1471_; lean_object* v_a_1472_; lean_object* v_r_1473_; 
v___x_1471_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1465_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
v_r_1473_ = lean_apply_9(v_x_1456_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, lean_box(0));
if (lean_obj_tag(v_r_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1498_; 
v_a_1474_ = lean_ctor_get(v_r_1473_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_r_1473_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1476_ = v_r_1473_;
v_isShared_1477_ = v_isSharedCheck_1498_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v_r_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1498_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
lean_inc(v_a_1474_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set_tag(v___x_1476_, 1);
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1465_, v_mkInfoTree_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v_a_1472_, v___x_1479_);
lean_dec_ref(v___x_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v___x_1480_, 0);
lean_dec(v_unused_1488_);
v___x_1482_ = v___x_1480_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_dec(v___x_1480_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v_a_1474_);
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1474_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_a_1474_);
v_a_1489_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1480_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1480_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_a_1499_ = lean_ctor_get(v_r_1473_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v_r_1473_, 1);
v___x_1500_ = lean_box(0);
v___x_1501_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1465_, v_mkInfoTree_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v_a_1472_, v___x_1500_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v___x_1501_, 0);
lean_dec(v_unused_1509_);
v___x_1503_ = v___x_1501_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v___x_1501_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 1);
lean_ctor_set(v___x_1503_, 0, v_a_1499_);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1499_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_a_1499_);
v_a_1510_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1501_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1501_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1518_, lean_object* v_mkInfoTree_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1518_, v_mkInfoTree_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_ref_1536_; lean_object* v___x_1537_; lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1546_; 
v_ref_1536_ = lean_ctor_get(v___y_1533_, 2);
v___x_1537_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1546_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_inc(v_ref_1536_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_ref_1536_);
lean_ctor_set(v___x_1542_, 1, v_a_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v___x_1542_);
v___x_1544_ = v___x_1540_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1553_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(lean_object* v_a_1554_, lean_object* v_x_1555_){
_start:
{
if (lean_obj_tag(v_x_1555_) == 0)
{
uint8_t v___x_1556_; 
v___x_1556_ = 0;
return v___x_1556_;
}
else
{
lean_object* v_key_1557_; lean_object* v_tail_1558_; uint8_t v___x_1559_; 
v_key_1557_ = lean_ctor_get(v_x_1555_, 0);
v_tail_1558_ = lean_ctor_get(v_x_1555_, 2);
v___x_1559_ = lean_expr_eqv(v_key_1557_, v_a_1554_);
if (v___x_1559_ == 0)
{
v_x_1555_ = v_tail_1558_;
goto _start;
}
else
{
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_a_1561_, lean_object* v_x_1562_){
_start:
{
uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_res_1563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1561_, v_x_1562_);
lean_dec(v_x_1562_);
lean_dec_ref(v_a_1561_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(lean_object* v_x_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1566_) == 0)
{
return v_x_1565_;
}
else
{
lean_object* v_key_1567_; lean_object* v_value_1568_; lean_object* v_tail_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1592_; 
v_key_1567_ = lean_ctor_get(v_x_1566_, 0);
v_value_1568_ = lean_ctor_get(v_x_1566_, 1);
v_tail_1569_ = lean_ctor_get(v_x_1566_, 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1571_ = v_x_1566_;
v_isShared_1572_ = v_isSharedCheck_1592_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_tail_1569_);
lean_inc(v_value_1568_);
lean_inc(v_key_1567_);
lean_dec(v_x_1566_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1592_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; uint64_t v___x_1574_; uint64_t v___x_1575_; uint64_t v___x_1576_; uint64_t v_fold_1577_; uint64_t v___x_1578_; uint64_t v___x_1579_; uint64_t v___x_1580_; size_t v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1573_ = lean_array_get_size(v_x_1565_);
v___x_1574_ = l_Lean_Expr_hash(v_key_1567_);
v___x_1575_ = 32ULL;
v___x_1576_ = lean_uint64_shift_right(v___x_1574_, v___x_1575_);
v_fold_1577_ = lean_uint64_xor(v___x_1574_, v___x_1576_);
v___x_1578_ = 16ULL;
v___x_1579_ = lean_uint64_shift_right(v_fold_1577_, v___x_1578_);
v___x_1580_ = lean_uint64_xor(v_fold_1577_, v___x_1579_);
v___x_1581_ = lean_uint64_to_usize(v___x_1580_);
v___x_1582_ = lean_usize_of_nat(v___x_1573_);
v___x_1583_ = ((size_t)1ULL);
v___x_1584_ = lean_usize_sub(v___x_1582_, v___x_1583_);
v___x_1585_ = lean_usize_land(v___x_1581_, v___x_1584_);
v___x_1586_ = lean_array_uget_borrowed(v_x_1565_, v___x_1585_);
lean_inc(v___x_1586_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 2, v___x_1586_);
v___x_1588_ = v___x_1571_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_key_1567_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_value_1568_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_array_uset(v_x_1565_, v___x_1585_, v___x_1588_);
v_x_1565_ = v___x_1589_;
v_x_1566_ = v_tail_1569_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(lean_object* v_i_1593_, lean_object* v_source_1594_, lean_object* v_target_1595_){
_start:
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_array_get_size(v_source_1594_);
v___x_1597_ = lean_nat_dec_lt(v_i_1593_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v_source_1594_);
lean_dec(v_i_1593_);
return v_target_1595_;
}
else
{
lean_object* v_es_1598_; lean_object* v___x_1599_; lean_object* v_source_1600_; lean_object* v_target_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_es_1598_ = lean_array_fget(v_source_1594_, v_i_1593_);
v___x_1599_ = lean_box(0);
v_source_1600_ = lean_array_fset(v_source_1594_, v_i_1593_, v___x_1599_);
v_target_1601_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_target_1595_, v_es_1598_);
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_add(v_i_1593_, v___x_1602_);
lean_dec(v_i_1593_);
v_i_1593_ = v___x_1603_;
v_source_1594_ = v_source_1600_;
v_target_1595_ = v_target_1601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(lean_object* v_data_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_nbuckets_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1606_ = lean_array_get_size(v_data_1605_);
v___x_1607_ = lean_unsigned_to_nat(2u);
v_nbuckets_1608_ = lean_nat_mul(v___x_1606_, v___x_1607_);
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_mk_array(v_nbuckets_1608_, v___x_1610_);
v___x_1612_ = lean_array_propagate_mark(v_data_1605_, v___x_1611_);
v___x_1613_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v___x_1609_, v_data_1605_, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(lean_object* v_m_1614_, lean_object* v_a_1615_, lean_object* v_b_1616_){
_start:
{
lean_object* v_size_1617_; lean_object* v_buckets_1618_; lean_object* v___x_1619_; uint64_t v___x_1620_; uint64_t v___x_1621_; uint64_t v___x_1622_; uint64_t v_fold_1623_; uint64_t v___x_1624_; uint64_t v___x_1625_; uint64_t v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; lean_object* v_bkt_1632_; uint8_t v___x_1633_; 
v_size_1617_ = lean_ctor_get(v_m_1614_, 0);
v_buckets_1618_ = lean_ctor_get(v_m_1614_, 1);
v___x_1619_ = lean_array_get_size(v_buckets_1618_);
v___x_1620_ = l_Lean_Expr_hash(v_a_1615_);
v___x_1621_ = 32ULL;
v___x_1622_ = lean_uint64_shift_right(v___x_1620_, v___x_1621_);
v_fold_1623_ = lean_uint64_xor(v___x_1620_, v___x_1622_);
v___x_1624_ = 16ULL;
v___x_1625_ = lean_uint64_shift_right(v_fold_1623_, v___x_1624_);
v___x_1626_ = lean_uint64_xor(v_fold_1623_, v___x_1625_);
v___x_1627_ = lean_uint64_to_usize(v___x_1626_);
v___x_1628_ = lean_usize_of_nat(v___x_1619_);
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_sub(v___x_1628_, v___x_1629_);
v___x_1631_ = lean_usize_land(v___x_1627_, v___x_1630_);
v_bkt_1632_ = lean_array_uget_borrowed(v_buckets_1618_, v___x_1631_);
v___x_1633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1615_, v_bkt_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1654_; 
lean_inc_ref(v_buckets_1618_);
lean_inc(v_size_1617_);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_m_1614_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; lean_object* v_unused_1656_; 
v_unused_1655_ = lean_ctor_get(v_m_1614_, 1);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_m_1614_, 0);
lean_dec(v_unused_1656_);
v___x_1635_ = v_m_1614_;
v_isShared_1636_ = v_isSharedCheck_1654_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v_m_1614_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1654_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v_size_x27_1638_; lean_object* v___x_1639_; lean_object* v_buckets_x27_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1637_ = lean_unsigned_to_nat(1u);
v_size_x27_1638_ = lean_nat_add(v_size_1617_, v___x_1637_);
lean_dec(v_size_1617_);
lean_inc(v_bkt_1632_);
v___x_1639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1639_, 0, v_a_1615_);
lean_ctor_set(v___x_1639_, 1, v_b_1616_);
lean_ctor_set(v___x_1639_, 2, v_bkt_1632_);
v_buckets_x27_1640_ = lean_array_uset(v_buckets_1618_, v___x_1631_, v___x_1639_);
v___x_1641_ = lean_unsigned_to_nat(4u);
v___x_1642_ = lean_nat_mul(v_size_x27_1638_, v___x_1641_);
v___x_1643_ = lean_unsigned_to_nat(3u);
v___x_1644_ = lean_nat_div(v___x_1642_, v___x_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_array_get_size(v_buckets_x27_1640_);
v___x_1646_ = lean_nat_dec_le(v___x_1644_, v___x_1645_);
lean_dec(v___x_1644_);
if (v___x_1646_ == 0)
{
lean_object* v_val_1647_; lean_object* v___x_1649_; 
v_val_1647_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_buckets_x27_1640_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v_val_1647_);
lean_ctor_set(v___x_1635_, 0, v_size_x27_1638_);
v___x_1649_ = v___x_1635_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_size_x27_1638_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_val_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
else
{
lean_object* v___x_1652_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v_buckets_x27_1640_);
lean_ctor_set(v___x_1635_, 0, v_size_x27_1638_);
v___x_1652_ = v___x_1635_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_size_x27_1638_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_buckets_x27_1640_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_dec(v_b_1616_);
lean_dec_ref(v_a_1615_);
return v_m_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(lean_object* v_mvarId_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v_mctx_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1661_ = lean_st_ref_get(v___y_1659_);
v_mctx_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc_ref(v_mctx_1662_);
lean_dec(v___x_1661_);
v___x_1663_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1662_, v_mvarId_1657_);
lean_dec_ref(v_mctx_1662_);
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v___y_1658_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_mvarId_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec(v_mvarId_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(lean_object* v_mvarId_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v___x_1676_; lean_object* v_mctx_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1676_ = lean_st_ref_get(v___y_1674_);
v_mctx_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc_ref(v_mctx_1677_);
lean_dec(v___x_1676_);
v___x_1678_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1677_, v_mvarId_1672_);
lean_dec_ref(v_mctx_1677_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___y_1673_);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg___boxed(lean_object* v_mvarId_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec(v_mvarId_1682_);
return v_res_1686_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(lean_object* v_m_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_buckets_1689_; lean_object* v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; uint64_t v_fold_1694_; uint64_t v___x_1695_; uint64_t v___x_1696_; uint64_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v_buckets_1689_ = lean_ctor_get(v_m_1687_, 1);
v___x_1690_ = lean_array_get_size(v_buckets_1689_);
v___x_1691_ = l_Lean_Expr_hash(v_a_1688_);
v___x_1692_ = 32ULL;
v___x_1693_ = lean_uint64_shift_right(v___x_1691_, v___x_1692_);
v_fold_1694_ = lean_uint64_xor(v___x_1691_, v___x_1693_);
v___x_1695_ = 16ULL;
v___x_1696_ = lean_uint64_shift_right(v_fold_1694_, v___x_1695_);
v___x_1697_ = lean_uint64_xor(v_fold_1694_, v___x_1696_);
v___x_1698_ = lean_uint64_to_usize(v___x_1697_);
v___x_1699_ = lean_usize_of_nat(v___x_1690_);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_sub(v___x_1699_, v___x_1700_);
v___x_1702_ = lean_usize_land(v___x_1698_, v___x_1701_);
v___x_1703_ = lean_array_uget_borrowed(v_buckets_1689_, v___x_1702_);
v___x_1704_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1688_, v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_m_1705_, lean_object* v_a_1706_){
_start:
{
uint8_t v_res_1707_; lean_object* v_r_1708_; 
v_res_1707_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_1705_, v_a_1706_);
lean_dec_ref(v_a_1706_);
lean_dec_ref(v_m_1705_);
v_r_1708_ = lean_box(v_res_1707_);
return v_r_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(lean_object* v_mvarId_1713_, lean_object* v_e_1714_, lean_object* v_a_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_d_1726_; lean_object* v_b_1727_; lean_object* v___y_1728_; uint8_t v___x_1734_; 
v___x_1734_ = l_Lean_Expr_hasExprMVar(v_e_1714_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec_ref(v_e_1714_);
v___x_1735_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v_a_1715_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
else
{
uint8_t v___x_1738_; 
v___x_1738_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_a_1715_, v_e_1714_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_box(0);
lean_inc_ref(v_e_1714_);
v___x_1740_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_a_1715_, v_e_1714_, v___x_1739_);
switch(lean_obj_tag(v_e_1714_))
{
case 11:
{
lean_object* v_struct_1741_; 
v_struct_1741_ = lean_ctor_get(v_e_1714_, 2);
lean_inc_ref(v_struct_1741_);
lean_dec_ref_known(v_e_1714_, 3);
v_e_1714_ = v_struct_1741_;
v_a_1715_ = v___x_1740_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1743_; lean_object* v_body_1744_; 
v_binderType_1743_ = lean_ctor_get(v_e_1714_, 1);
lean_inc_ref(v_binderType_1743_);
v_body_1744_ = lean_ctor_get(v_e_1714_, 2);
lean_inc_ref(v_body_1744_);
lean_dec_ref_known(v_e_1714_, 3);
v_d_1726_ = v_binderType_1743_;
v_b_1727_ = v_body_1744_;
v___y_1728_ = v___x_1740_;
goto v___jp_1725_;
}
case 6:
{
lean_object* v_binderType_1745_; lean_object* v_body_1746_; 
v_binderType_1745_ = lean_ctor_get(v_e_1714_, 1);
lean_inc_ref(v_binderType_1745_);
v_body_1746_ = lean_ctor_get(v_e_1714_, 2);
lean_inc_ref(v_body_1746_);
lean_dec_ref_known(v_e_1714_, 3);
v_d_1726_ = v_binderType_1745_;
v_b_1727_ = v_body_1746_;
v___y_1728_ = v___x_1740_;
goto v___jp_1725_;
}
case 8:
{
lean_object* v_type_1747_; lean_object* v_value_1748_; lean_object* v_body_1749_; lean_object* v___x_1750_; 
v_type_1747_ = lean_ctor_get(v_e_1714_, 1);
lean_inc_ref(v_type_1747_);
v_value_1748_ = lean_ctor_get(v_e_1714_, 2);
lean_inc_ref(v_value_1748_);
v_body_1749_ = lean_ctor_get(v_e_1714_, 3);
lean_inc_ref(v_body_1749_);
lean_dec_ref_known(v_e_1714_, 4);
v___x_1750_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1713_, v_type_1747_, v___x_1740_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v_fst_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_fst_1752_ = lean_ctor_get(v_a_1751_, 0);
if (lean_obj_tag(v_fst_1752_) == 0)
{
lean_dec_ref(v_body_1749_);
lean_dec_ref(v_value_1748_);
return v___x_1750_;
}
else
{
lean_object* v_snd_1753_; lean_object* v___x_1754_; 
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v_snd_1753_ = lean_ctor_get(v_a_1751_, 1);
lean_inc(v_snd_1753_);
lean_dec(v_a_1751_);
v___x_1754_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1713_, v_value_1748_, v_snd_1753_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_fst_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_fst_1756_ = lean_ctor_get(v_a_1755_, 0);
if (lean_obj_tag(v_fst_1756_) == 0)
{
lean_dec_ref(v_body_1749_);
return v___x_1754_;
}
else
{
lean_object* v_snd_1757_; 
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v_snd_1757_ = lean_ctor_get(v_a_1755_, 1);
lean_inc(v_snd_1757_);
lean_dec(v_a_1755_);
v_e_1714_ = v_body_1749_;
v_a_1715_ = v_snd_1757_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1749_);
return v___x_1754_;
}
}
}
else
{
lean_dec_ref(v_body_1749_);
lean_dec_ref(v_value_1748_);
return v___x_1750_;
}
}
case 10:
{
lean_object* v_expr_1759_; 
v_expr_1759_ = lean_ctor_get(v_e_1714_, 1);
lean_inc_ref(v_expr_1759_);
lean_dec_ref_known(v_e_1714_, 2);
v_e_1714_ = v_expr_1759_;
v_a_1715_ = v___x_1740_;
goto _start;
}
case 5:
{
lean_object* v_fn_1761_; lean_object* v_arg_1762_; lean_object* v___x_1763_; 
v_fn_1761_ = lean_ctor_get(v_e_1714_, 0);
lean_inc_ref(v_fn_1761_);
v_arg_1762_ = lean_ctor_get(v_e_1714_, 1);
lean_inc_ref(v_arg_1762_);
lean_dec_ref_known(v_e_1714_, 2);
v___x_1763_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1713_, v_fn_1761_, v___x_1740_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v_fst_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_fst_1765_ = lean_ctor_get(v_a_1764_, 0);
if (lean_obj_tag(v_fst_1765_) == 0)
{
lean_dec_ref(v_arg_1762_);
return v___x_1763_;
}
else
{
lean_object* v_snd_1766_; 
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v_snd_1766_ = lean_ctor_get(v_a_1764_, 1);
lean_inc(v_snd_1766_);
lean_dec(v_a_1764_);
v_e_1714_ = v_arg_1762_;
v_a_1715_ = v_snd_1766_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1762_);
return v___x_1763_;
}
}
case 2:
{
lean_object* v_mvarId_1768_; lean_object* v___x_1769_; 
v_mvarId_1768_ = lean_ctor_get(v_e_1714_, 0);
lean_inc(v_mvarId_1768_);
lean_dec_ref_known(v_e_1714_, 1);
v___x_1769_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1713_, v_mvarId_1768_, v___x_1740_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
return v___x_1769_;
}
default: 
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v_e_1714_);
v___x_1770_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v___x_1740_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec_ref(v_e_1714_);
v___x_1773_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v_a_1715_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
v___jp_1725_:
{
lean_object* v___x_1729_; 
v___x_1729_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1713_, v_d_1726_, v___y_1728_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v_fst_1731_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_fst_1731_ = lean_ctor_get(v_a_1730_, 0);
if (lean_obj_tag(v_fst_1731_) == 0)
{
lean_dec_ref(v_b_1727_);
return v___x_1729_;
}
else
{
lean_object* v_snd_1732_; 
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v_snd_1732_ = lean_ctor_get(v_a_1730_, 1);
lean_inc(v_snd_1732_);
lean_dec(v_a_1730_);
v_e_1714_ = v_b_1727_;
v_a_1715_ = v_snd_1732_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1727_);
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(lean_object* v_mvarId_1776_, lean_object* v_mvarId_x27_1777_, lean_object* v_a_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = l_Lean_instBEqMVarId_beq(v_mvarId_1776_, v_mvarId_x27_1777_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_x27_1777_, v_a_1778_, v___y_1784_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1873_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1873_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1873_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_fst_1794_; 
v_fst_1794_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_fst_1794_);
if (lean_obj_tag(v_fst_1794_) == 0)
{
lean_object* v_snd_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_mvarId_x27_1777_);
v_snd_1795_ = lean_ctor_get(v_a_1790_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_a_1790_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v_a_1790_, 0);
lean_dec(v_unused_1814_);
v___x_1797_ = v_a_1790_;
v_isShared_1798_ = v_isSharedCheck_1813_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_snd_1795_);
lean_dec(v_a_1790_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1813_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1812_; 
v_a_1799_ = lean_ctor_get(v_fst_1794_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_fst_1794_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1801_ = v_fst_1794_;
v_isShared_1802_ = v_isSharedCheck_1812_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v_fst_1794_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1812_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1806_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1804_);
v___x_1806_ = v___x_1797_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_snd_1795_);
v___x_1806_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1806_);
v___x_1808_ = v___x_1792_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
}
else
{
lean_object* v_a_1815_; 
lean_del_object(v___x_1792_);
v_a_1815_ = lean_ctor_get(v_fst_1794_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v_fst_1794_, 1);
if (lean_obj_tag(v_a_1815_) == 0)
{
lean_object* v_snd_1816_; lean_object* v___x_1817_; 
v_snd_1816_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_snd_1816_);
lean_dec(v_a_1790_);
v___x_1817_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_x27_1777_, v_snd_1816_, v___y_1784_);
lean_dec(v_mvarId_x27_1777_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1861_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1861_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1861_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_fst_1822_; 
v_fst_1822_ = lean_ctor_get(v_a_1818_, 0);
lean_inc(v_fst_1822_);
if (lean_obj_tag(v_fst_1822_) == 0)
{
lean_object* v_snd_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1841_; 
v_snd_1823_ = lean_ctor_get(v_a_1818_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_a_1818_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v_a_1818_, 0);
lean_dec(v_unused_1842_);
v___x_1825_ = v_a_1818_;
v_isShared_1826_ = v_isSharedCheck_1841_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_snd_1823_);
lean_dec(v_a_1818_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1841_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1840_; 
v_a_1827_ = lean_ctor_get(v_fst_1822_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_fst_1822_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1829_ = v_fst_1822_;
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v_fst_1822_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1840_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1832_);
v___x_1834_ = v___x_1825_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_snd_1823_);
v___x_1834_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1836_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1834_);
v___x_1836_ = v___x_1820_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
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
}
}
else
{
lean_object* v_a_1843_; 
v_a_1843_ = lean_ctor_get(v_fst_1822_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v_fst_1822_, 1);
if (lean_obj_tag(v_a_1843_) == 0)
{
lean_object* v_snd_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1855_; 
v_snd_1844_ = lean_ctor_get(v_a_1818_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_a_1818_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v_a_1818_, 0);
lean_dec(v_unused_1856_);
v___x_1846_ = v_a_1818_;
v_isShared_1847_ = v_isSharedCheck_1855_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_snd_1844_);
lean_dec(v_a_1818_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1855_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_snd_1844_);
v___x_1850_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1850_);
v___x_1852_ = v___x_1820_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
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
else
{
lean_object* v_val_1857_; lean_object* v_snd_1858_; lean_object* v_mvarIdPending_1859_; 
lean_del_object(v___x_1820_);
v_val_1857_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_val_1857_);
lean_dec_ref_known(v_a_1843_, 1);
v_snd_1858_ = lean_ctor_get(v_a_1818_, 1);
lean_inc(v_snd_1858_);
lean_dec(v_a_1818_);
v_mvarIdPending_1859_ = lean_ctor_get(v_val_1857_, 1);
lean_inc(v_mvarIdPending_1859_);
lean_dec(v_val_1857_);
v_mvarId_x27_1777_ = v_mvarIdPending_1859_;
v_a_1778_ = v_snd_1858_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1817_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1817_);
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
lean_object* v_snd_1870_; lean_object* v_val_1871_; lean_object* v___x_1872_; 
lean_dec(v_mvarId_x27_1777_);
v_snd_1870_ = lean_ctor_get(v_a_1790_, 1);
lean_inc(v_snd_1870_);
lean_dec(v_a_1790_);
v_val_1871_ = lean_ctor_get(v_a_1815_, 0);
lean_inc(v_val_1871_);
lean_dec_ref_known(v_a_1815_, 1);
v___x_1872_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1776_, v_val_1871_, v_snd_1870_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_mvarId_x27_1777_);
v_a_1874_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1789_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1789_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_dec(v_mvarId_x27_1777_);
v___x_1882_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1));
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_a_1778_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___boxed(lean_object* v_mvarId_1885_, lean_object* v_mvarId_x27_1886_, lean_object* v_a_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1885_, v_mvarId_x27_1886_, v_a_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v_mvarId_1885_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6___boxed(lean_object* v_mvarId_1898_, lean_object* v_e_1899_, lean_object* v_a_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1898_, v_e_1899_, v_a_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v_mvarId_1898_);
return v_res_1910_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_unsigned_to_nat(16u);
v___x_1913_ = lean_mk_array(v___x_1912_, v___x_1911_);
return v___x_1913_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0);
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_mvarId_1917_, lean_object* v_e_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Expr_hasExprMVar(v_e_1918_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_dec_ref(v_e_1918_);
v___x_1929_ = 1;
v___x_1930_ = lean_box(v___x_1929_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
else
{
uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = 0;
v___x_1933_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
v___x_1934_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1917_, v_e_1918_, v___x_1933_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1948_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1948_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1948_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_fst_1939_; 
v_fst_1939_ = lean_ctor_get(v_a_1935_, 0);
lean_inc(v_fst_1939_);
lean_dec(v_a_1935_);
if (lean_obj_tag(v_fst_1939_) == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
lean_dec_ref_known(v_fst_1939_, 1);
v___x_1940_ = lean_box(v___x_1932_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1940_);
v___x_1942_ = v___x_1937_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_dec_ref_known(v_fst_1939_, 1);
v___x_1944_ = lean_box(v___x_1928_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1944_);
v___x_1946_ = v___x_1937_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1934_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1934_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_mvarId_1957_, lean_object* v_e_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_mvarId_1957_, v_e_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v_mvarId_1957_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_, lean_object* v_x_1972_){
_start:
{
lean_object* v_ks_1973_; lean_object* v_vs_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1998_; 
v_ks_1973_ = lean_ctor_get(v_x_1969_, 0);
v_vs_1974_ = lean_ctor_get(v_x_1969_, 1);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_x_1969_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1976_ = v_x_1969_;
v_isShared_1977_ = v_isSharedCheck_1998_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_vs_1974_);
lean_inc(v_ks_1973_);
lean_dec(v_x_1969_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1998_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = lean_array_get_size(v_ks_1973_);
v___x_1979_ = lean_nat_dec_lt(v_x_1970_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
lean_dec(v_x_1970_);
v___x_1980_ = lean_array_push(v_ks_1973_, v_x_1971_);
v___x_1981_ = lean_array_push(v_vs_1974_, v_x_1972_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___x_1981_);
lean_ctor_set(v___x_1976_, 0, v___x_1980_);
v___x_1983_ = v___x_1976_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
else
{
lean_object* v_k_x27_1985_; uint8_t v___x_1986_; 
v_k_x27_1985_ = lean_array_fget_borrowed(v_ks_1973_, v_x_1970_);
v___x_1986_ = l_Lean_instBEqMVarId_beq(v_x_1971_, v_k_x27_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1988_; 
if (v_isShared_1977_ == 0)
{
v___x_1988_ = v___x_1976_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_ks_1973_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_vs_1974_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_nat_add(v_x_1970_, v___x_1989_);
lean_dec(v_x_1970_);
v_x_1969_ = v___x_1988_;
v_x_1970_ = v___x_1990_;
goto _start;
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1993_ = lean_array_fset(v_ks_1973_, v_x_1970_, v_x_1971_);
v___x_1994_ = lean_array_fset(v_vs_1974_, v_x_1970_, v_x_1972_);
lean_dec(v_x_1970_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___x_1994_);
lean_ctor_set(v___x_1976_, 0, v___x_1993_);
v___x_1996_ = v___x_1976_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_n_1999_, lean_object* v_k_2000_, lean_object* v_v_2001_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_n_1999_, v___x_2002_, v_k_2000_, v_v_2001_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_x_2005_, size_t v_x_2006_, size_t v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 0)
{
lean_object* v_es_2010_; size_t v___x_2011_; size_t v___x_2012_; lean_object* v_j_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_es_2010_ = lean_ctor_get(v_x_2005_, 0);
v___x_2011_ = ((size_t)31ULL);
v___x_2012_ = lean_usize_land(v_x_2006_, v___x_2011_);
v_j_2013_ = lean_usize_to_nat(v___x_2012_);
v___x_2014_ = lean_array_get_size(v_es_2010_);
v___x_2015_ = lean_nat_dec_lt(v_j_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_dec(v_j_2013_);
lean_dec(v_x_2009_);
lean_dec(v_x_2008_);
return v_x_2005_;
}
else
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2054_; 
lean_inc_ref(v_es_2010_);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_x_2005_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v_x_2005_, 0);
lean_dec(v_unused_2055_);
v___x_2017_ = v_x_2005_;
v_isShared_2018_ = v_isSharedCheck_2054_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_x_2005_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2054_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_v_2019_; lean_object* v___x_2020_; lean_object* v_xs_x27_2021_; lean_object* v___y_2023_; 
v_v_2019_ = lean_array_fget(v_es_2010_, v_j_2013_);
v___x_2020_ = lean_box(0);
v_xs_x27_2021_ = lean_array_fset(v_es_2010_, v_j_2013_, v___x_2020_);
switch(lean_obj_tag(v_v_2019_))
{
case 0:
{
lean_object* v_key_2028_; lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_key_2028_ = lean_ctor_get(v_v_2019_, 0);
v_val_2029_ = lean_ctor_get(v_v_2019_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_v_2019_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v_v_2019_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_inc(v_key_2028_);
lean_dec(v_v_2019_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Lean_instBEqMVarId_beq(v_x_2008_, v_key_2028_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_del_object(v___x_2031_);
v___x_2034_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2028_, v_val_2029_, v_x_2008_, v_x_2009_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
v___y_2023_ = v___x_2035_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2037_; 
lean_dec(v_val_2029_);
lean_dec(v_key_2028_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v_x_2009_);
lean_ctor_set(v___x_2031_, 0, v_x_2008_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_x_2008_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_x_2009_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v___y_2023_ = v___x_2037_;
goto v___jp_2022_;
}
}
}
}
case 1:
{
lean_object* v_node_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2052_; 
v_node_2040_ = lean_ctor_get(v_v_2019_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_v_2019_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2042_ = v_v_2019_;
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_node_2040_);
lean_dec(v_v_2019_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2052_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
size_t v___x_2044_; size_t v___x_2045_; size_t v___x_2046_; size_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2044_ = ((size_t)5ULL);
v___x_2045_ = lean_usize_shift_right(v_x_2006_, v___x_2044_);
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_add(v_x_2007_, v___x_2046_);
v___x_2048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_node_2040_, v___x_2045_, v___x_2047_, v_x_2008_, v_x_2009_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2048_);
v___x_2050_ = v___x_2042_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v___y_2023_ = v___x_2050_;
goto v___jp_2022_;
}
}
}
default: 
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v_x_2008_);
lean_ctor_set(v___x_2053_, 1, v_x_2009_);
v___y_2023_ = v___x_2053_;
goto v___jp_2022_;
}
}
v___jp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_array_fset(v_xs_x27_2021_, v_j_2013_, v___y_2023_);
lean_dec(v_j_2013_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2024_);
v___x_2026_ = v___x_2017_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
else
{
lean_object* v_ks_2056_; lean_object* v_vs_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2075_; 
v_ks_2056_ = lean_ctor_get(v_x_2005_, 0);
v_vs_2057_ = lean_ctor_get(v_x_2005_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_x_2005_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2059_ = v_x_2005_;
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_vs_2057_);
lean_inc(v_ks_2056_);
lean_dec(v_x_2005_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_ks_2056_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_vs_2057_);
v___x_2062_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v_newNode_2063_; size_t v___x_2064_; uint8_t v___x_2065_; 
v_newNode_2063_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v___x_2062_, v_x_2008_, v_x_2009_);
v___x_2064_ = ((size_t)7ULL);
v___x_2065_ = lean_usize_dec_le(v___x_2064_, v_x_2007_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2066_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2063_);
v___x_2067_ = lean_unsigned_to_nat(4u);
v___x_2068_ = lean_nat_dec_lt(v___x_2066_, v___x_2067_);
lean_dec(v___x_2066_);
if (v___x_2068_ == 0)
{
lean_object* v_ks_2069_; lean_object* v_vs_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_ks_2069_ = lean_ctor_get(v_newNode_2063_, 0);
lean_inc_ref(v_ks_2069_);
v_vs_2070_ = lean_ctor_get(v_newNode_2063_, 1);
lean_inc_ref(v_vs_2070_);
lean_dec_ref(v_newNode_2063_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0);
v___x_2073_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_x_2007_, v_ks_2069_, v_vs_2070_, v___x_2071_, v___x_2072_);
lean_dec_ref(v_vs_2070_);
lean_dec_ref(v_ks_2069_);
return v___x_2073_;
}
else
{
return v_newNode_2063_;
}
}
else
{
return v_newNode_2063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(size_t v_depth_2076_, lean_object* v_keys_2077_, lean_object* v_vals_2078_, lean_object* v_i_2079_, lean_object* v_entries_2080_){
_start:
{
lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = lean_array_get_size(v_keys_2077_);
v___x_2082_ = lean_nat_dec_lt(v_i_2079_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_dec(v_i_2079_);
return v_entries_2080_;
}
else
{
lean_object* v_k_2083_; lean_object* v_v_2084_; uint64_t v___x_2085_; size_t v_h_2086_; size_t v___x_2087_; lean_object* v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v_h_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_k_2083_ = lean_array_fget_borrowed(v_keys_2077_, v_i_2079_);
v_v_2084_ = lean_array_fget_borrowed(v_vals_2078_, v_i_2079_);
v___x_2085_ = l_Lean_instHashableMVarId_hash(v_k_2083_);
v_h_2086_ = lean_uint64_to_usize(v___x_2085_);
v___x_2087_ = ((size_t)5ULL);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_sub(v_depth_2076_, v___x_2089_);
v___x_2091_ = lean_usize_mul(v___x_2087_, v___x_2090_);
v_h_2092_ = lean_usize_shift_right(v_h_2086_, v___x_2091_);
v___x_2093_ = lean_nat_add(v_i_2079_, v___x_2088_);
lean_dec(v_i_2079_);
lean_inc(v_v_2084_);
lean_inc(v_k_2083_);
v___x_2094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_entries_2080_, v_h_2092_, v_depth_2076_, v_k_2083_, v_v_2084_);
v_i_2079_ = v___x_2093_;
v_entries_2080_ = v___x_2094_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_depth_2096_, lean_object* v_keys_2097_, lean_object* v_vals_2098_, lean_object* v_i_2099_, lean_object* v_entries_2100_){
_start:
{
size_t v_depth_boxed_2101_; lean_object* v_res_2102_; 
v_depth_boxed_2101_ = lean_unbox_usize(v_depth_2096_);
lean_dec(v_depth_2096_);
v_res_2102_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_boxed_2101_, v_keys_2097_, v_vals_2098_, v_i_2099_, v_entries_2100_);
lean_dec_ref(v_vals_2098_);
lean_dec_ref(v_keys_2097_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
size_t v_x_96037__boxed_2108_; size_t v_x_96038__boxed_2109_; lean_object* v_res_2110_; 
v_x_96037__boxed_2108_ = lean_unbox_usize(v_x_2104_);
lean_dec(v_x_2104_);
v_x_96038__boxed_2109_ = lean_unbox_usize(v_x_2105_);
lean_dec(v_x_2105_);
v_res_2110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2103_, v_x_96037__boxed_2108_, v_x_96038__boxed_2109_, v_x_2106_, v_x_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(lean_object* v_x_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_){
_start:
{
uint64_t v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = l_Lean_instHashableMVarId_hash(v_x_2112_);
v___x_2115_ = lean_uint64_to_usize(v___x_2114_);
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2111_, v___x_2115_, v___x_2116_, v_x_2112_, v_x_2113_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(lean_object* v_mvarId_2118_, lean_object* v_val_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v_mctx_2123_; lean_object* v_cache_2124_; lean_object* v_zetaDeltaFVarIds_2125_; lean_object* v_postponed_2126_; lean_object* v_diag_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2157_; 
v___x_2122_ = lean_st_ref_take(v___y_2120_);
v_mctx_2123_ = lean_ctor_get(v___x_2122_, 0);
v_cache_2124_ = lean_ctor_get(v___x_2122_, 1);
v_zetaDeltaFVarIds_2125_ = lean_ctor_get(v___x_2122_, 2);
v_postponed_2126_ = lean_ctor_get(v___x_2122_, 3);
v_diag_2127_ = lean_ctor_get(v___x_2122_, 4);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2129_ = v___x_2122_;
v_isShared_2130_ = v_isSharedCheck_2157_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_diag_2127_);
lean_inc(v_postponed_2126_);
lean_inc(v_zetaDeltaFVarIds_2125_);
lean_inc(v_cache_2124_);
lean_inc(v_mctx_2123_);
lean_dec(v___x_2122_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2157_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_depth_2131_; lean_object* v_levelAssignDepth_2132_; lean_object* v_lmvarCounter_2133_; lean_object* v_mvarCounter_2134_; lean_object* v_lDecls_2135_; lean_object* v_decls_2136_; lean_object* v_userNames_2137_; lean_object* v_lAssignment_2138_; lean_object* v_eAssignment_2139_; lean_object* v_dAssignment_2140_; lean_object* v_instanceTypedMVars_2141_; lean_object* v_synthNormMemo_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2156_; 
v_depth_2131_ = lean_ctor_get(v_mctx_2123_, 0);
v_levelAssignDepth_2132_ = lean_ctor_get(v_mctx_2123_, 1);
v_lmvarCounter_2133_ = lean_ctor_get(v_mctx_2123_, 2);
v_mvarCounter_2134_ = lean_ctor_get(v_mctx_2123_, 3);
v_lDecls_2135_ = lean_ctor_get(v_mctx_2123_, 4);
v_decls_2136_ = lean_ctor_get(v_mctx_2123_, 5);
v_userNames_2137_ = lean_ctor_get(v_mctx_2123_, 6);
v_lAssignment_2138_ = lean_ctor_get(v_mctx_2123_, 7);
v_eAssignment_2139_ = lean_ctor_get(v_mctx_2123_, 8);
v_dAssignment_2140_ = lean_ctor_get(v_mctx_2123_, 9);
v_instanceTypedMVars_2141_ = lean_ctor_get(v_mctx_2123_, 10);
v_synthNormMemo_2142_ = lean_ctor_get(v_mctx_2123_, 11);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_mctx_2123_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2144_ = v_mctx_2123_;
v_isShared_2145_ = v_isSharedCheck_2156_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_synthNormMemo_2142_);
lean_inc(v_instanceTypedMVars_2141_);
lean_inc(v_dAssignment_2140_);
lean_inc(v_eAssignment_2139_);
lean_inc(v_lAssignment_2138_);
lean_inc(v_userNames_2137_);
lean_inc(v_decls_2136_);
lean_inc(v_lDecls_2135_);
lean_inc(v_mvarCounter_2134_);
lean_inc(v_lmvarCounter_2133_);
lean_inc(v_levelAssignDepth_2132_);
lean_inc(v_depth_2131_);
lean_dec(v_mctx_2123_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2156_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2146_ = lean_box(0);
v___x_2147_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_eAssignment_2139_, v_mvarId_2118_, v_val_2119_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 8, v___x_2147_);
v___x_2149_ = v___x_2144_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_depth_2131_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_levelAssignDepth_2132_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_lmvarCounter_2133_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_mvarCounter_2134_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_lDecls_2135_);
lean_ctor_set(v_reuseFailAlloc_2155_, 5, v_decls_2136_);
lean_ctor_set(v_reuseFailAlloc_2155_, 6, v_userNames_2137_);
lean_ctor_set(v_reuseFailAlloc_2155_, 7, v_lAssignment_2138_);
lean_ctor_set(v_reuseFailAlloc_2155_, 8, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2155_, 9, v_dAssignment_2140_);
lean_ctor_set(v_reuseFailAlloc_2155_, 10, v_instanceTypedMVars_2141_);
lean_ctor_set(v_reuseFailAlloc_2155_, 11, v_synthNormMemo_2142_);
v___x_2149_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2149_);
v___x_2151_ = v___x_2129_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_cache_2124_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_zetaDeltaFVarIds_2125_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_postponed_2126_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_diag_2127_);
v___x_2151_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_st_ref_put(v___y_2120_, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2146_);
return v___x_2153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg___boxed(lean_object* v_mvarId_2158_, lean_object* v_val_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_2158_, v_val_2159_, v___y_2160_);
lean_dec(v___y_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_o_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_env_2168_; lean_object* v___x_2169_; lean_object* v_toEnvExtension_2170_; lean_object* v_asyncMode_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v_merged_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2183_; 
v___x_2166_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2167_ = lean_st_ref_get(v___y_2164_);
v_env_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_ref(v_env_2168_);
lean_dec(v___x_2167_);
v___x_2169_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2170_ = lean_ctor_get(v___x_2169_, 0);
v_asyncMode_2171_ = lean_ctor_get(v_toEnvExtension_2170_, 2);
v___x_2172_ = lean_box(0);
v___x_2173_ = 0;
v___x_2174_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2166_, v___x_2169_, v_env_2168_, v_asyncMode_2171_, v___x_2172_, v___x_2173_);
v_merged_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v___x_2174_, 1);
lean_dec(v_unused_2184_);
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_merged_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_merged_2175_);
lean_ctor_set(v___x_2177_, 0, v_o_2163_);
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_o_2163_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_merged_2175_);
v___x_2180_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg___boxed(lean_object* v_o_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_2185_, v___y_2186_);
lean_dec(v___y_2186_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2195_);
v___x_2199_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v___x_2198_, v___y_2196_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2209_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2225_, lean_object* v_snd_2226_, uint8_t v___x_2227_, lean_object* v___x_2228_, uint8_t v___x_2229_, uint8_t v_useReducible_2230_, uint8_t v___x_2231_, lean_object* v___x_2232_, lean_object* v___x_2233_, lean_object* v_simprocs_2234_, lean_object* v_discharge_x3f_2235_, lean_object* v_snd_2236_, lean_object* v___f_2237_, lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v___f_2242_, lean_object* v_a_2243_, lean_object* v___x_2244_, lean_object* v___f_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; 
if (lean_obj_tag(v_usingArg_2225_) == 1)
{
lean_object* v_val_2468_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___x_2520_; lean_object* v_infoState_2521_; uint8_t v_enabled_2522_; 
v_val_2468_ = lean_ctor_get(v_usingArg_2225_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v_usingArg_2225_, 1);
v___x_2520_ = lean_st_ref_get(v___y_2253_);
v_infoState_2521_ = lean_ctor_get(v___x_2520_, 8);
lean_inc_ref(v_infoState_2521_);
lean_dec(v___x_2520_);
v_enabled_2522_ = lean_ctor_get_uint8(v_infoState_2521_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2521_);
if (v_enabled_2522_ == 0)
{
lean_dec_ref(v___f_2245_);
v___y_2470_ = v___y_2246_;
v___y_2471_ = v___y_2247_;
v___y_2472_ = v___y_2248_;
v___y_2473_ = v___y_2249_;
v___y_2474_ = v___y_2250_;
v___y_2475_ = v___y_2251_;
v___y_2476_ = v___y_2252_;
v___y_2477_ = v___y_2253_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2523_; lean_object* v_a_2524_; lean_object* v___f_2525_; lean_object* v___x_2526_; 
v___x_2523_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2253_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2523_);
v___f_2525_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2525_, 0, v_a_2524_);
v___x_2526_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2525_, v___f_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_dec_ref_known(v___x_2526_, 1);
v___y_2470_ = v___y_2246_;
v___y_2471_ = v___y_2247_;
v___y_2472_ = v___y_2248_;
v___y_2473_ = v___y_2249_;
v___y_2474_ = v___y_2250_;
v___y_2475_ = v___y_2251_;
v___y_2476_ = v___y_2252_;
v___y_2477_ = v___y_2253_;
goto v___jp_2469_;
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_val_2468_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
v___jp_2469_:
{
lean_object* v___x_2478_; lean_object* v_mctx_2479_; lean_object* v_mvarCounter_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2478_ = lean_st_ref_get(v___y_2475_);
v_mctx_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc_ref(v_mctx_2479_);
lean_dec(v___x_2478_);
v_mvarCounter_2480_ = lean_ctor_get(v_mctx_2479_, 3);
lean_inc(v_mvarCounter_2480_);
lean_dec_ref(v_mctx_2479_);
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Lean_Elab_Tactic_elabTerm(v_val_2468_, v___x_2481_, v___x_2227_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc_n(v_a_2483_, 2);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_snd_2226_, v_a_2483_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; uint8_t v___x_2486_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2484_, 1);
v___x_2486_ = lean_unbox(v_a_2485_);
lean_dec(v_a_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_mvarCounter_2480_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
v___x_2487_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2488_ = l_Lean_indentExpr(v_a_2483_);
v___x_2489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2489_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = l_Lean_Expr_mvar___override(v_snd_2226_);
v___x_2493_ = l_Lean_MessageData_ofExpr(v___x_2492_);
v___x_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2491_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2494_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
else
{
v___y_2320_ = v___x_2481_;
v___y_2321_ = v_a_2483_;
v___y_2322_ = v_mvarCounter_2480_;
v___y_2323_ = v___x_2481_;
v___y_2324_ = v___y_2470_;
v___y_2325_ = v___y_2471_;
v___y_2326_ = v___y_2472_;
v___y_2327_ = v___y_2473_;
v___y_2328_ = v___y_2474_;
v___y_2329_ = v___y_2475_;
v___y_2330_ = v___y_2476_;
v___y_2331_ = v___y_2477_;
goto v___jp_2319_;
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v_a_2483_);
lean_dec(v_mvarCounter_2480_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2504_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2484_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2484_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v_mvarCounter_2480_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2512_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2482_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2482_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
else
{
lean_object* v_lctx_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec_ref(v___f_2245_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v___x_2228_);
lean_dec(v_usingArg_2225_);
v_lctx_2535_ = lean_ctor_get(v___y_2250_, 2);
v___x_2536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10));
v___x_2537_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2535_, v___x_2536_);
if (lean_obj_tag(v___x_2537_) == 1)
{
lean_object* v_val_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_val_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v___x_2537_, 1);
v___x_2539_ = l_Lean_LocalDecl_fvarId(v_val_2538_);
lean_dec(v_val_2538_);
v___x_2540_ = lean_mk_empty_array_with_capacity(v___x_2232_);
v___x_2541_ = lean_array_push(v___x_2540_, v___x_2539_);
lean_inc_ref(v_snd_2236_);
v___x_2542_ = l_Lean_Meta_simpGoal(v_snd_2226_, v___x_2233_, v_simprocs_2234_, v_discharge_x3f_2235_, v___x_2229_, v___x_2541_, v_snd_2236_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2571_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2571_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2571_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_fst_2547_; 
v_fst_2547_ = lean_ctor_get(v_a_2543_, 0);
if (lean_obj_tag(v_fst_2547_) == 1)
{
lean_object* v_val_2548_; lean_object* v_snd_2549_; lean_object* v_snd_2550_; lean_object* v___x_2551_; 
lean_del_object(v___x_2545_);
lean_dec_ref(v_snd_2236_);
v_val_2548_ = lean_ctor_get(v_fst_2547_, 0);
lean_inc(v_val_2548_);
v_snd_2549_ = lean_ctor_get(v_a_2543_, 1);
lean_inc(v_snd_2549_);
lean_dec(v_a_2543_);
v_snd_2550_ = lean_ctor_get(v_val_2548_, 1);
lean_inc(v_snd_2550_);
lean_dec(v_val_2548_);
v___x_2551_ = l_Lean_MVarId_assumption(v_snd_2550_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v___x_2551_, 0);
lean_dec(v_unused_2559_);
v___x_2553_ = v___x_2551_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_dec(v___x_2551_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v_snd_2549_);
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_snd_2549_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_snd_2549_);
v_a_2560_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2551_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2551_);
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
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v___x_2569_; 
lean_dec(v_a_2543_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v_snd_2236_);
v___x_2569_ = v___x_2545_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_snd_2236_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v_snd_2236_);
v_a_2572_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2542_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2542_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v___x_2580_; 
lean_dec(v___x_2537_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
v___x_2580_ = l_Lean_MVarId_assumption(v_snd_2226_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v___x_2580_, 0);
lean_dec(v_unused_2588_);
v___x_2582_ = v___x_2580_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_dec(v___x_2580_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v_snd_2236_);
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_snd_2236_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v_snd_2236_);
v_a_2589_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2580_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2580_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v___x_2259_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_snd_2226_, v___y_2257_, v___y_2258_);
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
lean_ctor_set(v___x_2261_, 0, v___y_2256_);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___y_2256_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
v___jp_2268_:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Core_mkFreshUserName(v___y_2276_, v___y_2277_, v___y_2274_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc_n(v_a_2286_, 2);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = l_Lean_MVarId_rename(v___y_2280_, v___y_2284_, v_a_2286_, v___y_2275_, v___y_2279_, v___y_2277_, v___y_2274_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc_n(v_a_2288_, 2);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = lean_box(v___x_2227_);
v___x_2290_ = lean_box(v___x_2229_);
v___x_2291_ = lean_box(v_useReducible_2230_);
v___x_2292_ = lean_box(v___x_2231_);
v___f_2293_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2293_, 0, v_a_2288_);
lean_closure_set(v___f_2293_, 1, v_a_2286_);
lean_closure_set(v___f_2293_, 2, v___x_2289_);
lean_closure_set(v___f_2293_, 3, v___y_2270_);
lean_closure_set(v___f_2293_, 4, v___y_2271_);
lean_closure_set(v___f_2293_, 5, v___x_2228_);
lean_closure_set(v___f_2293_, 6, v___x_2290_);
lean_closure_set(v___f_2293_, 7, v___y_2269_);
lean_closure_set(v___f_2293_, 8, v___x_2291_);
lean_closure_set(v___f_2293_, 9, v___x_2292_);
v___x_2294_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_a_2288_, v___f_2293_, v___y_2282_, v___y_2278_, v___y_2283_, v___y_2281_, v___y_2275_, v___y_2279_, v___y_2277_, v___y_2274_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref_known(v___x_2294_, 1);
v___y_2256_ = v___y_2272_;
v___y_2257_ = v___y_2273_;
v___y_2258_ = v___y_2279_;
goto v___jp_2255_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v_snd_2226_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v_a_2286_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2303_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2287_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2287_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec(v___y_2284_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2311_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2285_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2285_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
v___jp_2319_:
{
lean_object* v___x_2332_; 
lean_inc(v_snd_2226_);
v___x_2332_ = l_Lean_MVarId_getType(v_snd_2226_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
lean_inc(v_snd_2226_);
v___x_2334_ = l_Lean_MVarId_getTag(v_snd_2226_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2333_, v_a_2335_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = l_Lean_Expr_mvarId_x21(v_a_2337_);
v___x_2339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1));
lean_inc_ref(v___y_2321_);
v___x_2340_ = l_Lean_MVarId_note(v___x_2338_, v___x_2339_, v___y_2321_, v___y_2323_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v_fst_2342_; lean_object* v_snd_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v_fst_2342_ = lean_ctor_get(v_a_2341_, 0);
lean_inc_n(v_fst_2342_, 2);
v_snd_2343_ = lean_ctor_get(v_a_2341_, 1);
lean_inc(v_snd_2343_);
lean_dec(v_a_2341_);
v___x_2344_ = lean_mk_empty_array_with_capacity(v___x_2232_);
v___x_2345_ = lean_array_push(v___x_2344_, v_fst_2342_);
v___x_2346_ = l_Lean_Meta_simpGoal(v_snd_2343_, v___x_2233_, v_simprocs_2234_, v_discharge_x3f_2235_, v___x_2229_, v___x_2345_, v_snd_2236_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v_fst_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v_fst_2348_ = lean_ctor_get(v_a_2347_, 0);
if (lean_obj_tag(v_fst_2348_) == 0)
{
lean_object* v_snd_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_fst_2342_);
lean_dec(v___y_2322_);
lean_dec(v___y_2320_);
lean_dec_ref(v___x_2228_);
v_snd_2349_ = lean_ctor_get(v_a_2347_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_a_2347_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v_a_2347_, 0);
lean_dec(v_unused_2420_);
v___x_2351_ = v_a_2347_;
v_isShared_2352_ = v_isSharedCheck_2419_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snd_2349_);
lean_dec(v_a_2347_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2419_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v_a_2354_; uint8_t v___x_2355_; 
v___x_2353_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2354_);
lean_dec(v_a_2354_);
if (v___x_2355_ == 0)
{
lean_del_object(v___x_2351_);
lean_dec_ref(v___y_2321_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
v___y_2256_ = v_snd_2349_;
v___y_2257_ = v_a_2337_;
v___y_2258_ = v___y_2329_;
goto v___jp_2255_;
}
else
{
if (lean_obj_tag(v___y_2321_) == 1)
{
lean_object* v_fvarId_2356_; lean_object* v_lctx_2357_; lean_object* v___x_2358_; 
v_fvarId_2356_ = lean_ctor_get(v___y_2321_, 0);
lean_inc(v_fvarId_2356_);
lean_dec_ref_known(v___y_2321_, 1);
v_lctx_2357_ = lean_ctor_get(v___y_2328_, 2);
lean_inc_ref(v_lctx_2357_);
v___x_2358_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2357_, v_fvarId_2356_);
if (lean_obj_tag(v___x_2358_) == 1)
{
lean_object* v_val_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2418_; 
v_val_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2418_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_val_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2418_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = l_Lean_mkIdent(v_val_2359_);
lean_inc_ref(v___f_2237_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
lean_inc(v___y_2325_);
lean_inc_ref(v___y_2324_);
v___x_2364_ = lean_apply_9(v___f_2237_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, lean_box(0));
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc_n(v_a_2365_, 2);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2240_);
lean_inc_ref(v___x_2239_);
lean_inc_ref(v___x_2238_);
v___x_2367_ = l_Lean_Name_mkStr4(v___x_2238_, v___x_2239_, v___x_2240_, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node1(v_a_2365_, v___x_2241_, v___x_2363_);
v___x_2369_ = l_Lean_Syntax_node1(v_a_2365_, v___x_2367_, v___x_2368_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
lean_inc(v___y_2325_);
lean_inc_ref(v___y_2324_);
v___x_2370_ = lean_apply_9(v___f_2237_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, lean_box(0));
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v_ref_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc_n(v_a_2371_, 2);
lean_dec_ref_known(v___x_2370_, 1);
v_ref_2372_ = lean_ctor_get(v___y_2330_, 2);
v___x_2373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 2);
lean_ctor_set(v___x_2351_, 1, v___x_2373_);
lean_ctor_set(v___x_2351_, 0, v_a_2371_);
v___x_2375_ = v___x_2351_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2371_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2377_ = l_Lean_Name_mkStr4(v___x_2238_, v___x_2239_, v___x_2240_, v___x_2376_);
v___x_2378_ = l_Lean_Syntax_node2(v_a_2371_, v___x_2377_, v___x_2375_, v___x_2369_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2378_);
v___x_2380_ = v___x_2361_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; 
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
lean_inc(v___y_2325_);
lean_inc_ref(v___y_2324_);
v___x_2381_ = lean_apply_10(v___f_2242_, v___x_2380_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, lean_box(0));
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
lean_inc(v_ref_2372_);
v___x_2383_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2243_, v_ref_2372_, v_a_2382_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_dec_ref_known(v___x_2383_, 1);
v___y_2256_ = v_snd_2349_;
v___y_2257_ = v_a_2337_;
v___y_2258_ = v___y_2329_;
goto v___jp_2255_;
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_snd_2349_);
lean_dec(v_a_2337_);
lean_dec(v_snd_2226_);
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_snd_2349_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2243_);
lean_dec(v_snd_2226_);
v_a_2392_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2381_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2381_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v___x_2369_);
lean_del_object(v___x_2361_);
lean_del_object(v___x_2351_);
lean_dec(v_snd_2349_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec(v_snd_2226_);
v_a_2402_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2370_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2370_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v___x_2363_);
lean_del_object(v___x_2361_);
lean_del_object(v___x_2351_);
lean_dec(v_snd_2349_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec(v_snd_2226_);
v_a_2410_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2364_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2364_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
else
{
lean_dec(v___x_2358_);
lean_del_object(v___x_2351_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
v___y_2256_ = v_snd_2349_;
v___y_2257_ = v_a_2337_;
v___y_2258_ = v___y_2329_;
goto v___jp_2255_;
}
}
else
{
lean_del_object(v___x_2351_);
lean_dec_ref(v___y_2321_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
v___y_2256_ = v_snd_2349_;
v___y_2257_ = v_a_2337_;
v___y_2258_ = v___y_2329_;
goto v___jp_2255_;
}
}
}
}
else
{
lean_object* v_val_2421_; lean_object* v_snd_2422_; lean_object* v_fst_2423_; lean_object* v_snd_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
v_val_2421_ = lean_ctor_get(v_fst_2348_, 0);
lean_inc(v_val_2421_);
v_snd_2422_ = lean_ctor_get(v_a_2347_, 1);
lean_inc(v_snd_2422_);
lean_dec(v_a_2347_);
v_fst_2423_ = lean_ctor_get(v_val_2421_, 0);
lean_inc(v_fst_2423_);
v_snd_2424_ = lean_ctor_get(v_val_2421_, 1);
lean_inc(v_snd_2424_);
lean_dec(v_val_2421_);
v___x_2425_ = lean_array_get_size(v_fst_2423_);
v___x_2426_ = lean_nat_dec_lt(v___x_2244_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_dec(v_fst_2423_);
v___y_2269_ = v___y_2320_;
v___y_2270_ = v___y_2321_;
v___y_2271_ = v___y_2322_;
v___y_2272_ = v_snd_2422_;
v___y_2273_ = v_a_2337_;
v___y_2274_ = v___y_2331_;
v___y_2275_ = v___y_2328_;
v___y_2276_ = v___x_2339_;
v___y_2277_ = v___y_2330_;
v___y_2278_ = v___y_2325_;
v___y_2279_ = v___y_2329_;
v___y_2280_ = v_snd_2424_;
v___y_2281_ = v___y_2327_;
v___y_2282_ = v___y_2324_;
v___y_2283_ = v___y_2326_;
v___y_2284_ = v_fst_2342_;
goto v___jp_2268_;
}
else
{
lean_object* v___x_2427_; 
lean_dec(v_fst_2342_);
v___x_2427_ = lean_array_fget(v_fst_2423_, v___x_2244_);
lean_dec(v_fst_2423_);
v___y_2269_ = v___y_2320_;
v___y_2270_ = v___y_2321_;
v___y_2271_ = v___y_2322_;
v___y_2272_ = v_snd_2422_;
v___y_2273_ = v_a_2337_;
v___y_2274_ = v___y_2331_;
v___y_2275_ = v___y_2328_;
v___y_2276_ = v___x_2339_;
v___y_2277_ = v___y_2330_;
v___y_2278_ = v___y_2325_;
v___y_2279_ = v___y_2329_;
v___y_2280_ = v_snd_2424_;
v___y_2281_ = v___y_2327_;
v___y_2282_ = v___y_2324_;
v___y_2283_ = v___y_2326_;
v___y_2284_ = v___x_2427_;
goto v___jp_2268_;
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_fst_2342_);
lean_dec(v_a_2337_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2428_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2346_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2346_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2337_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2436_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2340_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2340_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2444_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2336_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2336_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_a_2333_);
lean_dec(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2452_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2334_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2334_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v_a_2243_);
lean_dec_ref(v___f_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec_ref(v___x_2239_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v___f_2237_);
lean_dec_ref(v_snd_2236_);
lean_dec(v_discharge_x3f_2235_);
lean_dec_ref(v_simprocs_2234_);
lean_dec_ref(v___x_2233_);
lean_dec_ref(v___x_2228_);
lean_dec(v_snd_2226_);
v_a_2460_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2332_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2332_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v_usingArg_2597_ = _args[0];
lean_object* v_snd_2598_ = _args[1];
lean_object* v___x_2599_ = _args[2];
lean_object* v___x_2600_ = _args[3];
lean_object* v___x_2601_ = _args[4];
lean_object* v_useReducible_2602_ = _args[5];
lean_object* v___x_2603_ = _args[6];
lean_object* v___x_2604_ = _args[7];
lean_object* v___x_2605_ = _args[8];
lean_object* v_simprocs_2606_ = _args[9];
lean_object* v_discharge_x3f_2607_ = _args[10];
lean_object* v_snd_2608_ = _args[11];
lean_object* v___f_2609_ = _args[12];
lean_object* v___x_2610_ = _args[13];
lean_object* v___x_2611_ = _args[14];
lean_object* v___x_2612_ = _args[15];
lean_object* v___x_2613_ = _args[16];
lean_object* v___f_2614_ = _args[17];
lean_object* v_a_2615_ = _args[18];
lean_object* v___x_2616_ = _args[19];
lean_object* v___f_2617_ = _args[20];
lean_object* v___y_2618_ = _args[21];
lean_object* v___y_2619_ = _args[22];
lean_object* v___y_2620_ = _args[23];
lean_object* v___y_2621_ = _args[24];
lean_object* v___y_2622_ = _args[25];
lean_object* v___y_2623_ = _args[26];
lean_object* v___y_2624_ = _args[27];
lean_object* v___y_2625_ = _args[28];
lean_object* v___y_2626_ = _args[29];
_start:
{
uint8_t v___x_96350__boxed_2627_; uint8_t v___x_96352__boxed_2628_; uint8_t v_useReducible_boxed_2629_; uint8_t v___x_96353__boxed_2630_; lean_object* v_res_2631_; 
v___x_96350__boxed_2627_ = lean_unbox(v___x_2599_);
v___x_96352__boxed_2628_ = lean_unbox(v___x_2601_);
v_useReducible_boxed_2629_ = lean_unbox(v_useReducible_2602_);
v___x_96353__boxed_2630_ = lean_unbox(v___x_2603_);
v_res_2631_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2597_, v_snd_2598_, v___x_96350__boxed_2627_, v___x_2600_, v___x_96352__boxed_2628_, v_useReducible_boxed_2629_, v___x_96353__boxed_2630_, v___x_2604_, v___x_2605_, v_simprocs_2606_, v_discharge_x3f_2607_, v_snd_2608_, v___f_2609_, v___x_2610_, v___x_2611_, v___x_2612_, v___x_2613_, v___f_2614_, v_a_2615_, v___x_2616_, v___f_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___x_2616_);
lean_dec(v___x_2604_);
return v_res_2631_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0(void){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2632_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
return v___x_2634_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_unsigned_to_nat(32u);
v___x_2636_ = lean_mk_empty_array_with_capacity(v___x_2635_);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2638_, lean_object* v_tk_2639_, lean_object* v___x_2640_, lean_object* v___x_2641_, lean_object* v___x_2642_, lean_object* v_simprocs_2643_, uint8_t v___x_2644_, lean_object* v_usingArg_2645_, lean_object* v___x_2646_, uint8_t v___x_2647_, uint8_t v_useReducible_2648_, uint8_t v___x_2649_, lean_object* v___x_2650_, lean_object* v___f_2651_, lean_object* v___x_2652_, lean_object* v___x_2653_, lean_object* v___x_2654_, lean_object* v___f_2655_, lean_object* v_a_2656_, lean_object* v_usingTk_x3f_2657_, lean_object* v_discharge_x3f_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___y_2669_; 
if (lean_obj_tag(v_usingTk_x3f_2657_) == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_box(0);
v___y_2669_ = v___x_2783_;
goto v___jp_2668_;
}
else
{
lean_object* v_val_2784_; 
v_val_2784_ = lean_ctor_get(v_usingTk_x3f_2657_, 0);
lean_inc(v_val_2784_);
lean_dec_ref_known(v_usingTk_x3f_2657_, 1);
v___y_2669_ = v_val_2784_;
goto v___jp_2668_;
}
v___jp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2670_ = lean_mk_empty_array_with_capacity(v___x_2638_);
v___x_2671_ = lean_array_push(v___x_2670_, v_tk_2639_);
v___x_2672_ = lean_array_push(v___x_2671_, v___y_2669_);
v___x_2673_ = lean_box(2);
lean_inc(v___x_2640_);
v___x_2674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
lean_ctor_set(v___x_2674_, 1, v___x_2640_);
lean_ctor_set(v___x_2674_, 2, v___x_2672_);
v___x_2675_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2674_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___f_2677_; lean_object* v___x_2678_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___f_2677_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2677_, 0, v_a_2676_);
v___x_2678_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2660_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; size_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = lean_mk_empty_array_with_capacity(v___x_2641_);
v___x_2681_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2641_, 3);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v___x_2641_);
v___x_2683_ = lean_unsigned_to_nat(32u);
v___x_2684_ = lean_mk_empty_array_with_capacity(v___x_2683_);
v___x_2685_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2686_ = ((size_t)5ULL);
v___x_2687_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2684_);
lean_ctor_set(v___x_2687_, 2, v___x_2641_);
lean_ctor_set(v___x_2687_, 3, v___x_2641_);
lean_ctor_set_usize(v___x_2687_, 4, v___x_2686_);
v___x_2688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2681_);
lean_ctor_set(v___x_2688_, 1, v___x_2681_);
lean_ctor_set(v___x_2688_, 2, v___x_2681_);
lean_ctor_set(v___x_2688_, 3, v___x_2687_);
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2682_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
lean_inc_ref(v___x_2689_);
lean_inc(v_discharge_x3f_2658_);
lean_inc_ref(v_simprocs_2643_);
lean_inc_ref(v___x_2642_);
v___x_2690_ = l_Lean_Meta_simpGoal(v_a_2679_, v___x_2642_, v_simprocs_2643_, v_discharge_x3f_2658_, v___x_2644_, v___x_2680_, v___x_2689_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v_fst_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v_fst_2692_ = lean_ctor_get(v_a_2691_, 0);
if (lean_obj_tag(v_fst_2692_) == 1)
{
lean_object* v_val_2693_; lean_object* v_snd_2694_; lean_object* v_snd_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref_known(v___x_2689_, 2);
v_val_2693_ = lean_ctor_get(v_fst_2692_, 0);
lean_inc(v_val_2693_);
v_snd_2694_ = lean_ctor_get(v_a_2691_, 1);
lean_inc(v_snd_2694_);
lean_dec(v_a_2691_);
v_snd_2695_ = lean_ctor_get(v_val_2693_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_val_2693_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; 
v_unused_2719_ = lean_ctor_get(v_val_2693_, 0);
lean_dec(v_unused_2719_);
v___x_2697_ = v_val_2693_;
v_isShared_2698_ = v_isSharedCheck_2718_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_snd_2695_);
lean_dec(v_val_2693_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2718_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___y_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2699_ = lean_box(v___x_2644_);
v___x_2700_ = lean_box(v___x_2647_);
v___x_2701_ = lean_box(v_useReducible_2648_);
v___x_2702_ = lean_box(v___x_2649_);
lean_inc_n(v_snd_2695_, 2);
v___y_2703_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2703_, 0, v_usingArg_2645_);
lean_closure_set(v___y_2703_, 1, v_snd_2695_);
lean_closure_set(v___y_2703_, 2, v___x_2699_);
lean_closure_set(v___y_2703_, 3, v___x_2646_);
lean_closure_set(v___y_2703_, 4, v___x_2700_);
lean_closure_set(v___y_2703_, 5, v___x_2701_);
lean_closure_set(v___y_2703_, 6, v___x_2702_);
lean_closure_set(v___y_2703_, 7, v___x_2650_);
lean_closure_set(v___y_2703_, 8, v___x_2642_);
lean_closure_set(v___y_2703_, 9, v_simprocs_2643_);
lean_closure_set(v___y_2703_, 10, v_discharge_x3f_2658_);
lean_closure_set(v___y_2703_, 11, v_snd_2694_);
lean_closure_set(v___y_2703_, 12, v___f_2651_);
lean_closure_set(v___y_2703_, 13, v___x_2652_);
lean_closure_set(v___y_2703_, 14, v___x_2653_);
lean_closure_set(v___y_2703_, 15, v___x_2654_);
lean_closure_set(v___y_2703_, 16, v___x_2640_);
lean_closure_set(v___y_2703_, 17, v___f_2655_);
lean_closure_set(v___y_2703_, 18, v_a_2656_);
lean_closure_set(v___y_2703_, 19, v___x_2641_);
lean_closure_set(v___y_2703_, 20, v___f_2677_);
v___x_2704_ = lean_box(0);
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 1);
lean_ctor_set(v___x_2697_, 1, v___x_2704_);
lean_ctor_set(v___x_2697_, 0, v_snd_2695_);
v___x_2706_ = v___x_2697_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_snd_2695_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2706_, v___y_2660_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v___x_2708_; 
lean_dec_ref_known(v___x_2707_, 1);
v___x_2708_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_snd_2695_, v___y_2703_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2708_;
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v___y_2703_);
lean_dec(v_snd_2695_);
v_a_2709_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2707_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2707_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
}
else
{
lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2691_);
lean_dec_ref(v___f_2677_);
lean_dec(v_discharge_x3f_2658_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___x_2652_);
lean_dec_ref(v___f_2651_);
lean_dec(v___x_2650_);
lean_dec_ref(v___x_2646_);
lean_dec(v_usingArg_2645_);
lean_dec_ref(v_simprocs_2643_);
lean_dec_ref(v___x_2642_);
lean_dec(v___x_2641_);
lean_dec(v___x_2640_);
v___x_2720_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2758_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2758_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
uint8_t v___x_2725_; 
v___x_2725_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2721_);
lean_dec(v_a_2721_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2727_; 
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2655_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2689_);
v___x_2727_ = v___x_2723_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2689_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
else
{
lean_object* v_ref_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_del_object(v___x_2723_);
v_ref_2729_ = lean_ctor_get(v___y_2665_, 2);
v___x_2730_ = lean_box(0);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
lean_inc(v___y_2662_);
lean_inc_ref(v___y_2661_);
lean_inc(v___y_2660_);
lean_inc_ref(v___y_2659_);
v___x_2731_ = lean_apply_10(v___f_2655_, v___x_2730_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, lean_box(0));
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
lean_inc(v_ref_2729_);
v___x_2733_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2656_, v_ref_2729_, v_a_2732_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; 
v_unused_2741_ = lean_ctor_get(v___x_2733_, 0);
lean_dec(v_unused_2741_);
v___x_2735_ = v___x_2733_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_dec(v___x_2733_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2689_);
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2689_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref_known(v___x_2689_, 2);
v_a_2742_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2733_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2733_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec_ref_known(v___x_2689_, 2);
lean_dec_ref(v_a_2656_);
v_a_2750_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2731_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2731_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec_ref_known(v___x_2689_, 2);
lean_dec_ref(v___f_2677_);
lean_dec(v_discharge_x3f_2658_);
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___x_2652_);
lean_dec_ref(v___f_2651_);
lean_dec(v___x_2650_);
lean_dec_ref(v___x_2646_);
lean_dec(v_usingArg_2645_);
lean_dec_ref(v_simprocs_2643_);
lean_dec_ref(v___x_2642_);
lean_dec(v___x_2641_);
lean_dec(v___x_2640_);
v_a_2759_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2690_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2690_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref(v___f_2677_);
lean_dec(v_discharge_x3f_2658_);
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___x_2652_);
lean_dec_ref(v___f_2651_);
lean_dec(v___x_2650_);
lean_dec_ref(v___x_2646_);
lean_dec(v_usingArg_2645_);
lean_dec_ref(v_simprocs_2643_);
lean_dec_ref(v___x_2642_);
lean_dec(v___x_2641_);
lean_dec(v___x_2640_);
v_a_2767_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2678_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2678_);
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
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_discharge_x3f_2658_);
lean_dec_ref(v_a_2656_);
lean_dec_ref(v___f_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___x_2653_);
lean_dec_ref(v___x_2652_);
lean_dec_ref(v___f_2651_);
lean_dec(v___x_2650_);
lean_dec_ref(v___x_2646_);
lean_dec(v_usingArg_2645_);
lean_dec_ref(v_simprocs_2643_);
lean_dec_ref(v___x_2642_);
lean_dec(v___x_2641_);
lean_dec(v___x_2640_);
v_a_2775_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2675_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2675_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v___x_2785_ = _args[0];
lean_object* v_tk_2786_ = _args[1];
lean_object* v___x_2787_ = _args[2];
lean_object* v___x_2788_ = _args[3];
lean_object* v___x_2789_ = _args[4];
lean_object* v_simprocs_2790_ = _args[5];
lean_object* v___x_2791_ = _args[6];
lean_object* v_usingArg_2792_ = _args[7];
lean_object* v___x_2793_ = _args[8];
lean_object* v___x_2794_ = _args[9];
lean_object* v_useReducible_2795_ = _args[10];
lean_object* v___x_2796_ = _args[11];
lean_object* v___x_2797_ = _args[12];
lean_object* v___f_2798_ = _args[13];
lean_object* v___x_2799_ = _args[14];
lean_object* v___x_2800_ = _args[15];
lean_object* v___x_2801_ = _args[16];
lean_object* v___f_2802_ = _args[17];
lean_object* v_a_2803_ = _args[18];
lean_object* v_usingTk_x3f_2804_ = _args[19];
lean_object* v_discharge_x3f_2805_ = _args[20];
lean_object* v___y_2806_ = _args[21];
lean_object* v___y_2807_ = _args[22];
lean_object* v___y_2808_ = _args[23];
lean_object* v___y_2809_ = _args[24];
lean_object* v___y_2810_ = _args[25];
lean_object* v___y_2811_ = _args[26];
lean_object* v___y_2812_ = _args[27];
lean_object* v___y_2813_ = _args[28];
lean_object* v___y_2814_ = _args[29];
_start:
{
uint8_t v___x_97143__boxed_2815_; uint8_t v___x_97145__boxed_2816_; uint8_t v_useReducible_boxed_2817_; uint8_t v___x_97146__boxed_2818_; lean_object* v_res_2819_; 
v___x_97143__boxed_2815_ = lean_unbox(v___x_2791_);
v___x_97145__boxed_2816_ = lean_unbox(v___x_2794_);
v_useReducible_boxed_2817_ = lean_unbox(v_useReducible_2795_);
v___x_97146__boxed_2818_ = lean_unbox(v___x_2796_);
v_res_2819_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2785_, v_tk_2786_, v___x_2787_, v___x_2788_, v___x_2789_, v_simprocs_2790_, v___x_97143__boxed_2815_, v_usingArg_2792_, v___x_2793_, v___x_97145__boxed_2816_, v_useReducible_boxed_2817_, v___x_97146__boxed_2818_, v___x_2797_, v___f_2798_, v___x_2799_, v___x_2800_, v___x_2801_, v___f_2802_, v_a_2803_, v_usingTk_x3f_2804_, v_discharge_x3f_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___x_2785_);
return v_res_2819_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2825_ = lean_unsigned_to_nat(38u);
v___x_2826_ = lean_unsigned_to_nat(159u);
v___x_2827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2829_ = l_mkPanicMessageWithDecl(v___x_2828_, v___x_2827_, v___x_2826_, v___x_2825_, v___x_2824_);
return v___x_2829_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2837_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2838_ = lean_unsigned_to_nat(15u);
v___x_2839_ = lean_unsigned_to_nat(160u);
v___x_2840_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2842_ = l_mkPanicMessageWithDecl(v___x_2841_, v___x_2840_, v___x_2839_, v___x_2838_, v___x_2837_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object* v_tk_2844_, lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v___x_2847_, lean_object* v___x_2848_, uint8_t v___x_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, uint8_t v_useReducible_2852_, lean_object* v___f_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v___x_2858_, lean_object* v___x_2859_, lean_object* v_usingArg_2860_, lean_object* v___x_2861_, uint8_t v___x_2862_, lean_object* v___f_2863_, lean_object* v_usingTk_x3f_2864_, lean_object* v_squeeze_2865_, lean_object* v_unfold_2866_, lean_object* v_args_2867_, lean_object* v_only_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v___y_2880_; lean_object* v___y_2884_; lean_object* v_stx_2885_; lean_object* v___y_2886_; lean_object* v_ref_2887_; lean_object* v___y_2888_; lean_object* v___y_2907_; lean_object* v_stx_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2871_, v___y_2873_, v___y_2875_, v___y_2877_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v_ref_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v_args_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3385_; lean_object* v___y_3386_; uint8_t v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v_only_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3492_; uint8_t v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3562_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
v_ref_2935_ = lean_ctor_get(v___y_2876_, 2);
v___x_2936_ = 0;
v___x_2937_ = l_Lean_SourceInfo_fromRef(v_ref_2935_, v___x_2936_);
v___x_2938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_ref(v___x_2847_);
lean_inc_ref(v___x_2846_);
lean_inc_ref(v___x_2845_);
v___x_2939_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_2938_);
lean_inc(v___x_2937_);
v___x_2940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2937_);
lean_ctor_set(v___x_2940_, 1, v___x_2938_);
v___x_2941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_2942_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3);
if (lean_obj_tag(v___y_2869_) == 0)
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3562_ = v___x_3571_;
goto v___jp_3561_;
}
else
{
lean_object* v_val_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_val_3572_ = lean_ctor_get(v___y_2869_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v___y_2869_, 1);
v___x_3573_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___x_3574_ = lean_array_push(v___x_3573_, v_val_3572_);
v___y_3562_ = v___x_3574_;
goto v___jp_3561_;
}
v___jp_2943_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2955_ = l_Array_append___redArg(v___x_2942_, v___y_2954_);
lean_dec_ref(v___y_2954_);
lean_inc_n(v___y_2949_, 2);
v___x_2956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2956_, 0, v___y_2949_);
lean_ctor_set(v___x_2956_, 1, v___x_2941_);
lean_ctor_set(v___x_2956_, 2, v___x_2955_);
v___x_2957_ = l_Lean_Syntax_node5(v___y_2949_, v___x_2850_, v___y_2944_, v___y_2946_, v___y_2952_, v___y_2948_, v___x_2956_);
v___x_2958_ = l_Lean_Syntax_node2(v___y_2949_, v___y_2951_, v___y_2945_, v___x_2957_);
v___y_2907_ = v___y_2950_;
v_stx_2908_ = v___x_2958_;
v___y_2909_ = v___y_2947_;
v___y_2910_ = v___y_2953_;
goto v___jp_2906_;
}
v___jp_2959_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = l_Array_append___redArg(v___x_2942_, v___y_2970_);
lean_dec_ref(v___y_2970_);
lean_inc(v___y_2964_);
v___x_2972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2972_, 0, v___y_2964_);
lean_ctor_set(v___x_2972_, 1, v___x_2941_);
lean_ctor_set(v___x_2972_, 2, v___x_2971_);
if (lean_obj_tag(v___y_2965_) == 1)
{
lean_object* v_val_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec(v___x_2848_);
v_val_2973_ = lean_ctor_get(v___y_2965_, 0);
lean_inc(v_val_2973_);
lean_dec_ref_known(v___y_2965_, 1);
v___x_2974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_2964_);
v___x_2975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___y_2964_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = l_Array_mkArray2___redArg(v___x_2975_, v_val_2973_);
v___y_2944_ = v___y_2960_;
v___y_2945_ = v___y_2962_;
v___y_2946_ = v___y_2961_;
v___y_2947_ = v___y_2963_;
v___y_2948_ = v___x_2972_;
v___y_2949_ = v___y_2964_;
v___y_2950_ = v___y_2968_;
v___y_2951_ = v___y_2967_;
v___y_2952_ = v___y_2966_;
v___y_2953_ = v___y_2969_;
v___y_2954_ = v___x_2976_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_2977_; 
lean_dec(v___y_2965_);
v___x_2977_ = lean_mk_empty_array_with_capacity(v___x_2848_);
lean_dec(v___x_2848_);
v___y_2944_ = v___y_2960_;
v___y_2945_ = v___y_2962_;
v___y_2946_ = v___y_2961_;
v___y_2947_ = v___y_2963_;
v___y_2948_ = v___x_2972_;
v___y_2949_ = v___y_2964_;
v___y_2950_ = v___y_2968_;
v___y_2951_ = v___y_2967_;
v___y_2952_ = v___y_2966_;
v___y_2953_ = v___y_2969_;
v___y_2954_ = v___x_2977_;
goto v___jp_2943_;
}
}
v___jp_2978_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = l_Array_append___redArg(v___x_2942_, v___y_2989_);
lean_dec_ref(v___y_2989_);
lean_inc(v___y_2983_);
v___x_2991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2991_, 0, v___y_2983_);
lean_ctor_set(v___x_2991_, 1, v___x_2941_);
lean_ctor_set(v___x_2991_, 2, v___x_2990_);
if (lean_obj_tag(v___y_2988_) == 1)
{
lean_object* v_val_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_val_2992_ = lean_ctor_get(v___y_2988_, 0);
lean_inc(v_val_2992_);
lean_dec_ref_known(v___y_2988_, 1);
v___x_2993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_2994_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_2993_);
v___x_2995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___y_2983_, 4);
v___x_2996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___y_2983_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = l_Array_append___redArg(v___x_2942_, v_val_2992_);
lean_dec(v_val_2992_);
v___x_2998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2998_, 0, v___y_2983_);
lean_ctor_set(v___x_2998_, 1, v___x_2941_);
lean_ctor_set(v___x_2998_, 2, v___x_2997_);
v___x_2999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_3000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___y_2983_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l_Lean_Syntax_node3(v___y_2983_, v___x_2994_, v___x_2996_, v___x_2998_, v___x_3000_);
v___x_3002_ = l_Array_mkArray1___redArg(v___x_3001_);
v___y_2960_ = v___y_2979_;
v___y_2961_ = v___y_2981_;
v___y_2962_ = v___y_2980_;
v___y_2963_ = v___y_2982_;
v___y_2964_ = v___y_2983_;
v___y_2965_ = v___y_2984_;
v___y_2966_ = v___x_2991_;
v___y_2967_ = v___y_2986_;
v___y_2968_ = v___y_2985_;
v___y_2969_ = v___y_2987_;
v___y_2970_ = v___x_3002_;
goto v___jp_2959_;
}
else
{
lean_object* v___x_3003_; 
lean_dec(v___y_2988_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3003_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_2960_ = v___y_2979_;
v___y_2961_ = v___y_2981_;
v___y_2962_ = v___y_2980_;
v___y_2963_ = v___y_2982_;
v___y_2964_ = v___y_2983_;
v___y_2965_ = v___y_2984_;
v___y_2966_ = v___x_2991_;
v___y_2967_ = v___y_2986_;
v___y_2968_ = v___y_2985_;
v___y_2969_ = v___y_2987_;
v___y_2970_ = v___x_3003_;
goto v___jp_2959_;
}
}
v___jp_3004_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = l_Array_append___redArg(v___x_2942_, v___y_3015_);
lean_dec_ref(v___y_3015_);
lean_inc(v___y_3008_);
v___x_3017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3017_, 0, v___y_3008_);
lean_ctor_set(v___x_3017_, 1, v___x_2941_);
lean_ctor_set(v___x_3017_, 2, v___x_3016_);
if (lean_obj_tag(v___y_3014_) == 1)
{
lean_object* v_val_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_val_3018_ = lean_ctor_get(v___y_3014_, 0);
lean_inc(v_val_3018_);
lean_dec_ref_known(v___y_3014_, 1);
v___x_3019_ = l_Lean_SourceInfo_fromRef(v_val_3018_, v___x_2849_);
lean_dec(v_val_3018_);
v___x_3020_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_3021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = l_Array_mkArray1___redArg(v___x_3021_);
v___y_2979_ = v___y_3005_;
v___y_2980_ = v___y_3006_;
v___y_2981_ = v___x_3017_;
v___y_2982_ = v___y_3007_;
v___y_2983_ = v___y_3008_;
v___y_2984_ = v___y_3009_;
v___y_2985_ = v___y_3011_;
v___y_2986_ = v___y_3010_;
v___y_2987_ = v___y_3012_;
v___y_2988_ = v___y_3013_;
v___y_2989_ = v___x_3022_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3023_; 
lean_dec(v___y_3014_);
v___x_3023_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_2979_ = v___y_3005_;
v___y_2980_ = v___y_3006_;
v___y_2981_ = v___x_3017_;
v___y_2982_ = v___y_3007_;
v___y_2983_ = v___y_3008_;
v___y_2984_ = v___y_3009_;
v___y_2985_ = v___y_3011_;
v___y_2986_ = v___y_3010_;
v___y_2987_ = v___y_3012_;
v___y_2988_ = v___y_3013_;
v___y_2989_ = v___x_3023_;
goto v___jp_2978_;
}
}
v___jp_3024_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3039_ = l_Array_append___redArg(v___x_2942_, v___y_3038_);
lean_dec_ref(v___y_3038_);
lean_inc_n(v___y_3033_, 3);
v___x_3040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3033_);
lean_ctor_set(v___x_3040_, 1, v___x_2941_);
lean_ctor_set(v___x_3040_, 2, v___x_3039_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___y_3033_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = l_Lean_Syntax_node6(v___y_3033_, v___y_3025_, v___y_3026_, v___y_3035_, v___y_3037_, v___x_3040_, v___x_3042_, v___y_3028_);
v___x_3044_ = l_Lean_Syntax_node4(v___y_3033_, v___y_3031_, v___y_3034_, v___y_3027_, v___y_3036_, v___x_3043_);
v___y_2907_ = v___y_3029_;
v_stx_2908_ = v___x_3044_;
v___y_2909_ = v___y_3032_;
v___y_2910_ = v___y_3030_;
goto v___jp_2906_;
}
v___jp_3045_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = l_Array_append___redArg(v___x_2942_, v___y_3059_);
lean_dec_ref(v___y_3059_);
lean_inc(v___y_3054_);
v___x_3061_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3061_, 0, v___y_3054_);
lean_ctor_set(v___x_3061_, 1, v___x_2941_);
lean_ctor_set(v___x_3061_, 2, v___x_3060_);
if (lean_obj_tag(v___y_3058_) == 1)
{
lean_object* v_val_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec(v___x_2848_);
v_val_3062_ = lean_ctor_get(v___y_3058_, 0);
lean_inc(v_val_3062_);
lean_dec_ref_known(v___y_3058_, 1);
v___x_3063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3064_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3063_);
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___y_3054_, 4);
v___x_3066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___y_3054_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Array_append___redArg(v___x_2942_, v_val_3062_);
lean_dec(v_val_3062_);
v___x_3068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3068_, 0, v___y_3054_);
lean_ctor_set(v___x_3068_, 1, v___x_2941_);
lean_ctor_set(v___x_3068_, 2, v___x_3067_);
v___x_3069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_3070_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___y_3054_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = l_Lean_Syntax_node3(v___y_3054_, v___x_3064_, v___x_3066_, v___x_3068_, v___x_3070_);
v___x_3072_ = l_Array_mkArray1___redArg(v___x_3071_);
v___y_3025_ = v___y_3046_;
v___y_3026_ = v___y_3047_;
v___y_3027_ = v___y_3048_;
v___y_3028_ = v___y_3049_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v___y_3051_;
v___y_3031_ = v___y_3052_;
v___y_3032_ = v___y_3053_;
v___y_3033_ = v___y_3054_;
v___y_3034_ = v___y_3055_;
v___y_3035_ = v___y_3056_;
v___y_3036_ = v___y_3057_;
v___y_3037_ = v___x_3061_;
v___y_3038_ = v___x_3072_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3073_; 
lean_dec(v___y_3058_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3073_ = lean_mk_empty_array_with_capacity(v___x_2848_);
lean_dec(v___x_2848_);
v___y_3025_ = v___y_3046_;
v___y_3026_ = v___y_3047_;
v___y_3027_ = v___y_3048_;
v___y_3028_ = v___y_3049_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v___y_3051_;
v___y_3031_ = v___y_3052_;
v___y_3032_ = v___y_3053_;
v___y_3033_ = v___y_3054_;
v___y_3034_ = v___y_3055_;
v___y_3035_ = v___y_3056_;
v___y_3036_ = v___y_3057_;
v___y_3037_ = v___x_3061_;
v___y_3038_ = v___x_3073_;
goto v___jp_3024_;
}
}
v___jp_3074_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = l_Array_append___redArg(v___x_2942_, v___y_3088_);
lean_dec_ref(v___y_3088_);
lean_inc(v___y_3083_);
v___x_3090_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3090_, 0, v___y_3083_);
lean_ctor_set(v___x_3090_, 1, v___x_2941_);
lean_ctor_set(v___x_3090_, 2, v___x_3089_);
if (lean_obj_tag(v___y_3087_) == 1)
{
lean_object* v_val_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_val_3091_ = lean_ctor_get(v___y_3087_, 0);
lean_inc(v_val_3091_);
lean_dec_ref_known(v___y_3087_, 1);
v___x_3092_ = l_Lean_SourceInfo_fromRef(v_val_3091_, v___x_2849_);
lean_dec(v_val_3091_);
v___x_3093_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_3094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3092_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = l_Array_mkArray1___redArg(v___x_3094_);
v___y_3046_ = v___y_3075_;
v___y_3047_ = v___y_3076_;
v___y_3048_ = v___y_3077_;
v___y_3049_ = v___y_3078_;
v___y_3050_ = v___y_3079_;
v___y_3051_ = v___y_3080_;
v___y_3052_ = v___y_3081_;
v___y_3053_ = v___y_3082_;
v___y_3054_ = v___y_3083_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___x_3090_;
v___y_3057_ = v___y_3085_;
v___y_3058_ = v___y_3086_;
v___y_3059_ = v___x_3095_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3096_; 
lean_dec(v___y_3087_);
v___x_3096_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3046_ = v___y_3075_;
v___y_3047_ = v___y_3076_;
v___y_3048_ = v___y_3077_;
v___y_3049_ = v___y_3078_;
v___y_3050_ = v___y_3079_;
v___y_3051_ = v___y_3080_;
v___y_3052_ = v___y_3081_;
v___y_3053_ = v___y_3082_;
v___y_3054_ = v___y_3083_;
v___y_3055_ = v___y_3084_;
v___y_3056_ = v___x_3090_;
v___y_3057_ = v___y_3085_;
v___y_3058_ = v___y_3086_;
v___y_3059_ = v___x_3096_;
goto v___jp_3045_;
}
}
v___jp_3097_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3109_ = l_Array_append___redArg(v___x_2942_, v___y_3108_);
lean_dec_ref(v___y_3108_);
lean_inc_n(v___y_3099_, 2);
v___x_3110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3110_, 0, v___y_3099_);
lean_ctor_set(v___x_3110_, 1, v___x_2941_);
lean_ctor_set(v___x_3110_, 2, v___x_3109_);
v___x_3111_ = l_Lean_Syntax_node5(v___y_3099_, v___x_2850_, v___y_3098_, v___y_3107_, v___y_3103_, v___y_3101_, v___x_3110_);
lean_inc(v___y_3105_);
v___x_3112_ = l_Lean_Syntax_node4(v___y_3099_, v___x_2851_, v___y_3106_, v___y_3105_, v___y_3105_, v___x_3111_);
v___y_2907_ = v___y_3102_;
v_stx_2908_ = v___x_3112_;
v___y_2909_ = v___y_3100_;
v___y_2910_ = v___y_3104_;
goto v___jp_2906_;
}
v___jp_3113_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = l_Array_append___redArg(v___x_2942_, v___y_3124_);
lean_dec_ref(v___y_3124_);
lean_inc(v___y_3115_);
v___x_3126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3126_, 0, v___y_3115_);
lean_ctor_set(v___x_3126_, 1, v___x_2941_);
lean_ctor_set(v___x_3126_, 2, v___x_3125_);
if (lean_obj_tag(v___y_3117_) == 1)
{
lean_object* v_val_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec(v___x_2848_);
v_val_3127_ = lean_ctor_get(v___y_3117_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___y_3117_, 1);
v___x_3128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3115_);
v___x_3129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___y_3115_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Array_mkArray2___redArg(v___x_3129_, v_val_3127_);
v___y_3098_ = v___y_3114_;
v___y_3099_ = v___y_3115_;
v___y_3100_ = v___y_3116_;
v___y_3101_ = v___x_3126_;
v___y_3102_ = v___y_3119_;
v___y_3103_ = v___y_3118_;
v___y_3104_ = v___y_3120_;
v___y_3105_ = v___y_3122_;
v___y_3106_ = v___y_3121_;
v___y_3107_ = v___y_3123_;
v___y_3108_ = v___x_3130_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3131_; 
lean_dec(v___y_3117_);
v___x_3131_ = lean_mk_empty_array_with_capacity(v___x_2848_);
lean_dec(v___x_2848_);
v___y_3098_ = v___y_3114_;
v___y_3099_ = v___y_3115_;
v___y_3100_ = v___y_3116_;
v___y_3101_ = v___x_3126_;
v___y_3102_ = v___y_3119_;
v___y_3103_ = v___y_3118_;
v___y_3104_ = v___y_3120_;
v___y_3105_ = v___y_3122_;
v___y_3106_ = v___y_3121_;
v___y_3107_ = v___y_3123_;
v___y_3108_ = v___x_3131_;
goto v___jp_3097_;
}
}
v___jp_3132_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = l_Array_append___redArg(v___x_2942_, v___y_3143_);
lean_dec_ref(v___y_3143_);
lean_inc(v___y_3134_);
v___x_3145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3145_, 0, v___y_3134_);
lean_ctor_set(v___x_3145_, 1, v___x_2941_);
lean_ctor_set(v___x_3145_, 2, v___x_3144_);
if (lean_obj_tag(v___y_3141_) == 1)
{
lean_object* v_val_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_val_3146_ = lean_ctor_get(v___y_3141_, 0);
lean_inc(v_val_3146_);
lean_dec_ref_known(v___y_3141_, 1);
v___x_3147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3148_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3147_);
v___x_3149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___y_3134_, 4);
v___x_3150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___y_3134_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l_Array_append___redArg(v___x_2942_, v_val_3146_);
lean_dec(v_val_3146_);
v___x_3152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3152_, 0, v___y_3134_);
lean_ctor_set(v___x_3152_, 1, v___x_2941_);
lean_ctor_set(v___x_3152_, 2, v___x_3151_);
v___x_3153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_3154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___y_3134_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = l_Lean_Syntax_node3(v___y_3134_, v___x_3148_, v___x_3150_, v___x_3152_, v___x_3154_);
v___x_3156_ = l_Array_mkArray1___redArg(v___x_3155_);
v___y_3114_ = v___y_3133_;
v___y_3115_ = v___y_3134_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
v___y_3118_ = v___x_3145_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3140_;
v___y_3122_ = v___y_3139_;
v___y_3123_ = v___y_3142_;
v___y_3124_ = v___x_3156_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3157_; 
lean_dec(v___y_3141_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3157_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3114_ = v___y_3133_;
v___y_3115_ = v___y_3134_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v___y_3136_;
v___y_3118_ = v___x_3145_;
v___y_3119_ = v___y_3137_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3140_;
v___y_3122_ = v___y_3139_;
v___y_3123_ = v___y_3142_;
v___y_3124_ = v___x_3157_;
goto v___jp_3113_;
}
}
v___jp_3158_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = l_Array_append___redArg(v___x_2942_, v___y_3169_);
lean_dec_ref(v___y_3169_);
lean_inc(v___y_3160_);
v___x_3171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3171_, 0, v___y_3160_);
lean_ctor_set(v___x_3171_, 1, v___x_2941_);
lean_ctor_set(v___x_3171_, 2, v___x_3170_);
if (lean_obj_tag(v___y_3168_) == 1)
{
lean_object* v_val_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v_val_3172_ = lean_ctor_get(v___y_3168_, 0);
lean_inc(v_val_3172_);
lean_dec_ref_known(v___y_3168_, 1);
v___x_3173_ = l_Lean_SourceInfo_fromRef(v_val_3172_, v___x_2849_);
lean_dec(v_val_3172_);
v___x_3174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_3175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Array_mkArray1___redArg(v___x_3175_);
v___y_3133_ = v___y_3159_;
v___y_3134_ = v___y_3160_;
v___y_3135_ = v___y_3161_;
v___y_3136_ = v___y_3162_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3166_;
v___y_3140_ = v___y_3165_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___x_3171_;
v___y_3143_ = v___x_3176_;
goto v___jp_3132_;
}
else
{
lean_object* v___x_3177_; 
lean_dec(v___y_3168_);
v___x_3177_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3133_ = v___y_3159_;
v___y_3134_ = v___y_3160_;
v___y_3135_ = v___y_3161_;
v___y_3136_ = v___y_3162_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___y_3166_;
v___y_3140_ = v___y_3165_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___x_3171_;
v___y_3143_ = v___x_3177_;
goto v___jp_3132_;
}
}
v___jp_3178_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3192_ = l_Array_append___redArg(v___x_2942_, v___y_3191_);
lean_dec_ref(v___y_3191_);
lean_inc_n(v___y_3189_, 3);
v___x_3193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3193_, 0, v___y_3189_);
lean_ctor_set(v___x_3193_, 1, v___x_2941_);
lean_ctor_set(v___x_3193_, 2, v___x_3192_);
v___x_3194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___y_3189_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_Syntax_node6(v___y_3189_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3183_, v___x_3193_, v___x_3195_, v___y_3190_);
lean_inc(v___y_3182_);
v___x_3197_ = l_Lean_Syntax_node4(v___y_3189_, v___y_3188_, v___y_3185_, v___y_3182_, v___y_3182_, v___x_3196_);
v___y_2907_ = v___y_3184_;
v_stx_2908_ = v___x_3197_;
v___y_2909_ = v___y_3187_;
v___y_2910_ = v___y_3186_;
goto v___jp_2906_;
}
v___jp_3198_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = l_Array_append___redArg(v___x_2942_, v___y_3211_);
lean_dec_ref(v___y_3211_);
lean_inc(v___y_3208_);
v___x_3213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3213_, 0, v___y_3208_);
lean_ctor_set(v___x_3213_, 1, v___x_2941_);
lean_ctor_set(v___x_3213_, 2, v___x_3212_);
if (lean_obj_tag(v___y_3209_) == 1)
{
lean_object* v_val_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
lean_dec(v___x_2848_);
v_val_3214_ = lean_ctor_get(v___y_3209_, 0);
lean_inc(v_val_3214_);
lean_dec_ref_known(v___y_3209_, 1);
v___x_3215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3216_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3215_);
v___x_3217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___y_3208_, 4);
v___x_3218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___y_3208_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = l_Array_append___redArg(v___x_2942_, v_val_3214_);
lean_dec(v_val_3214_);
v___x_3220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3220_, 0, v___y_3208_);
lean_ctor_set(v___x_3220_, 1, v___x_2941_);
lean_ctor_set(v___x_3220_, 2, v___x_3219_);
v___x_3221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_3222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___y_3208_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_Syntax_node3(v___y_3208_, v___x_3216_, v___x_3218_, v___x_3220_, v___x_3222_);
v___x_3224_ = l_Array_mkArray1___redArg(v___x_3223_);
v___y_3179_ = v___y_3199_;
v___y_3180_ = v___y_3200_;
v___y_3181_ = v___y_3201_;
v___y_3182_ = v___y_3202_;
v___y_3183_ = v___x_3213_;
v___y_3184_ = v___y_3203_;
v___y_3185_ = v___y_3204_;
v___y_3186_ = v___y_3205_;
v___y_3187_ = v___y_3206_;
v___y_3188_ = v___y_3207_;
v___y_3189_ = v___y_3208_;
v___y_3190_ = v___y_3210_;
v___y_3191_ = v___x_3224_;
goto v___jp_3178_;
}
else
{
lean_object* v___x_3225_; 
lean_dec(v___y_3209_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3225_ = lean_mk_empty_array_with_capacity(v___x_2848_);
lean_dec(v___x_2848_);
v___y_3179_ = v___y_3199_;
v___y_3180_ = v___y_3200_;
v___y_3181_ = v___y_3201_;
v___y_3182_ = v___y_3202_;
v___y_3183_ = v___x_3213_;
v___y_3184_ = v___y_3203_;
v___y_3185_ = v___y_3204_;
v___y_3186_ = v___y_3205_;
v___y_3187_ = v___y_3206_;
v___y_3188_ = v___y_3207_;
v___y_3189_ = v___y_3208_;
v___y_3190_ = v___y_3210_;
v___y_3191_ = v___x_3225_;
goto v___jp_3178_;
}
}
v___jp_3226_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = l_Array_append___redArg(v___x_2942_, v___y_3239_);
lean_dec_ref(v___y_3239_);
lean_inc(v___y_3235_);
v___x_3241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3241_, 0, v___y_3235_);
lean_ctor_set(v___x_3241_, 1, v___x_2941_);
lean_ctor_set(v___x_3241_, 2, v___x_3240_);
if (lean_obj_tag(v___y_3238_) == 1)
{
lean_object* v_val_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_val_3242_ = lean_ctor_get(v___y_3238_, 0);
lean_inc(v_val_3242_);
lean_dec_ref_known(v___y_3238_, 1);
v___x_3243_ = l_Lean_SourceInfo_fromRef(v_val_3242_, v___x_2849_);
lean_dec(v_val_3242_);
v___x_3244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_3245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Array_mkArray1___redArg(v___x_3245_);
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___x_3241_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___x_3246_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3247_; 
lean_dec(v___y_3238_);
v___x_3247_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___x_3241_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3233_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3235_;
v___y_3209_ = v___y_3236_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___x_3247_;
goto v___jp_3198_;
}
}
v___jp_3248_:
{
if (v___y_3256_ == 0)
{
if (v_useReducible_2852_ == 0)
{
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
if (lean_obj_tag(v___y_3252_) == 0)
{
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3251_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___y_2913_ = v___y_3253_;
v___y_2914_ = v___y_3262_;
v___y_2915_ = v___y_3249_;
v___y_2916_ = v___y_3258_;
v___y_2917_ = v___y_3259_;
v___y_2918_ = v___y_3255_;
v___y_2919_ = v___y_3250_;
v___y_2920_ = v___y_3257_;
v___y_2921_ = v___y_3254_;
goto v___jp_2912_;
}
else
{
lean_object* v_val_3264_; lean_object* v___x_3265_; 
v_val_3264_ = lean_ctor_get(v___y_3252_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v___y_3252_, 1);
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3257_);
v___x_3265_ = lean_apply_9(v___f_2853_, v___y_3262_, v___y_3249_, v___y_3258_, v___y_3259_, v___y_3255_, v___y_3250_, v___y_3257_, v___y_3254_, lean_box(0));
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc_n(v_a_3266_, 3);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2847_, 2);
lean_inc_ref_n(v___x_2846_, 2);
lean_inc_ref_n(v___x_2845_, 2);
v___x_3268_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_a_3266_);
lean_ctor_set(v___x_3269_, 1, v___x_2854_);
v___x_3270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3270_, 0, v_a_3266_);
lean_ctor_set(v___x_3270_, 1, v___x_2941_);
lean_ctor_set(v___x_3270_, 2, v___x_2942_);
v___x_3271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3272_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3271_);
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_object* v___x_3273_; 
v___x_3273_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3227_ = v___x_3272_;
v___y_3228_ = v___y_3251_;
v___y_3229_ = v___x_3270_;
v___y_3230_ = v___y_3253_;
v___y_3231_ = v___x_3269_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___y_3257_;
v___y_3234_ = v___x_3268_;
v___y_3235_ = v_a_3266_;
v___y_3236_ = v___y_3260_;
v___y_3237_ = v_val_3264_;
v___y_3238_ = v___y_3261_;
v___y_3239_ = v___x_3273_;
goto v___jp_3226_;
}
else
{
lean_object* v_val_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_val_3274_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_val_3274_);
lean_dec_ref_known(v___y_3263_, 1);
v___x_3275_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___x_3276_ = lean_array_push(v___x_3275_, v_val_3274_);
v___y_3227_ = v___x_3272_;
v___y_3228_ = v___y_3251_;
v___y_3229_ = v___x_3270_;
v___y_3230_ = v___y_3253_;
v___y_3231_ = v___x_3269_;
v___y_3232_ = v___y_3254_;
v___y_3233_ = v___y_3257_;
v___y_3234_ = v___x_3268_;
v___y_3235_ = v_a_3266_;
v___y_3236_ = v___y_3260_;
v___y_3237_ = v_val_3264_;
v___y_3238_ = v___y_3261_;
v___y_3239_ = v___x_3276_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_val_3264_);
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3251_);
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3277_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3265_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3265_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
else
{
lean_object* v___x_3285_; 
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3257_);
v___x_3285_ = lean_apply_9(v___f_2853_, v___y_3262_, v___y_3249_, v___y_3258_, v___y_3259_, v___y_3255_, v___y_3250_, v___y_3257_, v___y_3254_, lean_box(0));
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc_n(v_a_3286_, 3);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_a_3286_);
lean_ctor_set(v___x_3287_, 1, v___x_2854_);
v___x_3288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3288_, 0, v_a_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_2941_);
lean_ctor_set(v___x_3288_, 2, v___x_2942_);
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3159_ = v___y_3251_;
v___y_3160_ = v_a_3286_;
v___y_3161_ = v___y_3257_;
v___y_3162_ = v___y_3252_;
v___y_3163_ = v___y_3253_;
v___y_3164_ = v___y_3254_;
v___y_3165_ = v___x_3287_;
v___y_3166_ = v___x_3288_;
v___y_3167_ = v___y_3260_;
v___y_3168_ = v___y_3261_;
v___y_3169_ = v___x_3289_;
goto v___jp_3158_;
}
else
{
lean_object* v_val_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_val_3290_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_val_3290_);
lean_dec_ref_known(v___y_3263_, 1);
v___x_3291_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___x_3292_ = lean_array_push(v___x_3291_, v_val_3290_);
v___y_3159_ = v___y_3251_;
v___y_3160_ = v_a_3286_;
v___y_3161_ = v___y_3257_;
v___y_3162_ = v___y_3252_;
v___y_3163_ = v___y_3253_;
v___y_3164_ = v___y_3254_;
v___y_3165_ = v___x_3287_;
v___y_3166_ = v___x_3288_;
v___y_3167_ = v___y_3260_;
v___y_3168_ = v___y_3261_;
v___y_3169_ = v___x_3292_;
goto v___jp_3158_;
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3293_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3285_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3285_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
else
{
lean_dec(v___x_2851_);
if (v_useReducible_2852_ == 0)
{
lean_dec(v___x_2850_);
if (lean_obj_tag(v___y_3252_) == 0)
{
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec(v___y_3251_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___y_2913_ = v___y_3253_;
v___y_2914_ = v___y_3262_;
v___y_2915_ = v___y_3249_;
v___y_2916_ = v___y_3258_;
v___y_2917_ = v___y_3259_;
v___y_2918_ = v___y_3255_;
v___y_2919_ = v___y_3250_;
v___y_2920_ = v___y_3257_;
v___y_2921_ = v___y_3254_;
goto v___jp_2912_;
}
else
{
lean_object* v_val_3301_; lean_object* v___x_3302_; 
v_val_3301_ = lean_ctor_get(v___y_3252_, 0);
lean_inc(v_val_3301_);
lean_dec_ref_known(v___y_3252_, 1);
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3257_);
v___x_3302_ = lean_apply_9(v___f_2853_, v___y_3262_, v___y_3249_, v___y_3258_, v___y_3259_, v___y_3255_, v___y_3250_, v___y_3257_, v___y_3254_, lean_box(0));
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc_n(v_a_3303_, 5);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2847_, 2);
lean_inc_ref_n(v___x_2846_, 2);
lean_inc_ref_n(v___x_2845_, 2);
v___x_3305_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3304_);
v___x_3306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_a_3303_);
lean_ctor_set(v___x_3306_, 1, v___x_2854_);
v___x_3307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3307_, 0, v_a_3303_);
lean_ctor_set(v___x_3307_, 1, v___x_2941_);
lean_ctor_set(v___x_3307_, 2, v___x_2942_);
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_a_3303_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = l_Lean_Syntax_node1(v_a_3303_, v___x_2941_, v___x_3309_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3312_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3311_);
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3075_ = v___x_3312_;
v___y_3076_ = v___y_3251_;
v___y_3077_ = v___x_3307_;
v___y_3078_ = v_val_3301_;
v___y_3079_ = v___y_3253_;
v___y_3080_ = v___y_3254_;
v___y_3081_ = v___x_3305_;
v___y_3082_ = v___y_3257_;
v___y_3083_ = v_a_3303_;
v___y_3084_ = v___x_3306_;
v___y_3085_ = v___x_3310_;
v___y_3086_ = v___y_3260_;
v___y_3087_ = v___y_3261_;
v___y_3088_ = v___x_3313_;
goto v___jp_3074_;
}
else
{
lean_object* v_val_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_val_3314_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_val_3314_);
lean_dec_ref_known(v___y_3263_, 1);
v___x_3315_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___x_3316_ = lean_array_push(v___x_3315_, v_val_3314_);
v___y_3075_ = v___x_3312_;
v___y_3076_ = v___y_3251_;
v___y_3077_ = v___x_3307_;
v___y_3078_ = v_val_3301_;
v___y_3079_ = v___y_3253_;
v___y_3080_ = v___y_3254_;
v___y_3081_ = v___x_3305_;
v___y_3082_ = v___y_3257_;
v___y_3083_ = v_a_3303_;
v___y_3084_ = v___x_3306_;
v___y_3085_ = v___x_3310_;
v___y_3086_ = v___y_3260_;
v___y_3087_ = v___y_3261_;
v___y_3088_ = v___x_3316_;
goto v___jp_3074_;
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_val_3301_);
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3251_);
lean_dec_ref(v___x_2854_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3317_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3302_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3302_);
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
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
else
{
lean_object* v___x_3325_; 
lean_dec_ref(v___x_2854_);
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3257_);
v___x_3325_ = lean_apply_9(v___f_2853_, v___y_3262_, v___y_3249_, v___y_3258_, v___y_3259_, v___y_3255_, v___y_3250_, v___y_3257_, v___y_3254_, lean_box(0));
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc_n(v_a_3326_, 2);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2847_);
lean_inc_ref(v___x_2846_);
lean_inc_ref(v___x_2845_);
v___x_3328_ = l_Lean_Name_mkStr4(v___x_2845_, v___x_2846_, v___x_2847_, v___x_3327_);
v___x_3329_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3330_, 0, v_a_3326_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3005_ = v___y_3251_;
v___y_3006_ = v___x_3330_;
v___y_3007_ = v___y_3257_;
v___y_3008_ = v_a_3326_;
v___y_3009_ = v___y_3252_;
v___y_3010_ = v___x_3328_;
v___y_3011_ = v___y_3253_;
v___y_3012_ = v___y_3254_;
v___y_3013_ = v___y_3260_;
v___y_3014_ = v___y_3261_;
v___y_3015_ = v___x_3331_;
goto v___jp_3004_;
}
else
{
lean_object* v_val_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_val_3332_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v___y_3263_, 1);
v___x_3333_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___x_3334_ = lean_array_push(v___x_3333_, v_val_3332_);
v___y_3005_ = v___y_3251_;
v___y_3006_ = v___x_3330_;
v___y_3007_ = v___y_3257_;
v___y_3008_ = v_a_3326_;
v___y_3009_ = v___y_3252_;
v___y_3010_ = v___x_3328_;
v___y_3011_ = v___y_3253_;
v___y_3012_ = v___y_3254_;
v___y_3013_ = v___y_3260_;
v___y_3014_ = v___y_3261_;
v___y_3015_ = v___x_3334_;
goto v___jp_3004_;
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v___y_3263_);
lean_dec(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3335_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3325_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3325_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
}
v___jp_3343_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3360_ = lean_unsigned_to_nat(5u);
v___x_3361_ = l_Lean_Syntax_getArg(v___y_3349_, v___x_3360_);
lean_dec(v___y_3349_);
v___x_3362_ = l_Lean_Syntax_matchesNull(v___x_3361_, v___x_2848_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v_args_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3347_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3363_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3364_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3363_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___y_2907_ = v___y_3348_;
v_stx_2908_ = v_a_3365_;
v___y_2909_ = v___y_3358_;
v___y_2910_ = v___y_3359_;
goto v___jp_2906_;
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec_ref(v___y_3348_);
lean_dec(v_tk_2844_);
v_a_3366_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3364_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3364_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_Syntax_getOptional_x3f(v___y_3344_);
lean_dec(v___y_3344_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_box(0);
v___y_3249_ = v___y_3353_;
v___y_3250_ = v___y_3357_;
v___y_3251_ = v___y_3345_;
v___y_3252_ = v___y_3347_;
v___y_3253_ = v___y_3348_;
v___y_3254_ = v___y_3359_;
v___y_3255_ = v___y_3356_;
v___y_3256_ = v___y_3346_;
v___y_3257_ = v___y_3358_;
v___y_3258_ = v___y_3354_;
v___y_3259_ = v___y_3355_;
v___y_3260_ = v_args_3351_;
v___y_3261_ = v___y_3350_;
v___y_3262_ = v___y_3352_;
v___y_3263_ = v___x_3375_;
goto v___jp_3248_;
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_val_3376_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3374_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_val_3376_);
lean_dec(v___x_3374_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_val_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
v___y_3249_ = v___y_3353_;
v___y_3250_ = v___y_3357_;
v___y_3251_ = v___y_3345_;
v___y_3252_ = v___y_3347_;
v___y_3253_ = v___y_3348_;
v___y_3254_ = v___y_3359_;
v___y_3255_ = v___y_3356_;
v___y_3256_ = v___y_3346_;
v___y_3257_ = v___y_3358_;
v___y_3258_ = v___y_3354_;
v___y_3259_ = v___y_3355_;
v___y_3260_ = v_args_3351_;
v___y_3261_ = v___y_3350_;
v___y_3262_ = v___y_3352_;
v___y_3263_ = v___x_3381_;
goto v___jp_3248_;
}
}
}
}
}
v___jp_3384_:
{
lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3400_ = l_Lean_Syntax_getArg(v___y_3390_, v___x_2855_);
v___x_3401_ = l_Lean_Syntax_isNone(v___x_3400_);
if (v___x_3401_ == 0)
{
uint8_t v___x_3402_; 
lean_inc(v___x_3400_);
v___x_3402_ = l_Lean_Syntax_matchesNull(v___x_3400_, v___x_2856_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec(v___x_3400_);
lean_dec(v_only_3391_);
lean_dec(v___y_3390_);
lean_dec(v___y_3388_);
lean_dec(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3403_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3404_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3403_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v___y_2907_ = v___y_3389_;
v_stx_2908_ = v_a_3405_;
v___y_2909_ = v___y_3398_;
v___y_2910_ = v___y_3399_;
goto v___jp_2906_;
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec_ref(v___y_3389_);
lean_dec(v_tk_2844_);
v_a_3406_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3404_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3404_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = l_Lean_Syntax_getArg(v___x_3400_, v___x_2857_);
lean_dec(v___x_2857_);
lean_dec(v___x_3400_);
v___x_3415_ = l_Lean_Syntax_getArgs(v___x_3414_);
lean_dec(v___x_3414_);
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
v___y_3344_ = v___y_3385_;
v___y_3345_ = v___y_3386_;
v___y_3346_ = v___y_3387_;
v___y_3347_ = v___y_3388_;
v___y_3348_ = v___y_3389_;
v___y_3349_ = v___y_3390_;
v___y_3350_ = v_only_3391_;
v_args_3351_ = v___x_3416_;
v___y_3352_ = v___y_3392_;
v___y_3353_ = v___y_3393_;
v___y_3354_ = v___y_3394_;
v___y_3355_ = v___y_3395_;
v___y_3356_ = v___y_3396_;
v___y_3357_ = v___y_3397_;
v___y_3358_ = v___y_3398_;
v___y_3359_ = v___y_3399_;
goto v___jp_3343_;
}
}
else
{
lean_object* v___x_3417_; 
lean_dec(v___x_3400_);
lean_dec(v___x_2857_);
v___x_3417_ = lean_box(0);
v___y_3344_ = v___y_3385_;
v___y_3345_ = v___y_3386_;
v___y_3346_ = v___y_3387_;
v___y_3347_ = v___y_3388_;
v___y_3348_ = v___y_3389_;
v___y_3349_ = v___y_3390_;
v___y_3350_ = v_only_3391_;
v_args_3351_ = v___x_3417_;
v___y_3352_ = v___y_3392_;
v___y_3353_ = v___y_3393_;
v___y_3354_ = v___y_3394_;
v___y_3355_ = v___y_3395_;
v___y_3356_ = v___y_3396_;
v___y_3357_ = v___y_3397_;
v___y_3358_ = v___y_3398_;
v___y_3359_ = v___y_3399_;
goto v___jp_3343_;
}
}
v___jp_3418_:
{
lean_object* v_usedTheorems_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_usedTheorems_3423_ = lean_ctor_get(v___y_3420_, 0);
v___x_3424_ = l_Lean_Syntax_unsetTrailing(v___y_3421_);
v___x_3425_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3424_, v_usedTheorems_3423_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; uint8_t v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc_n(v_a_3426_, 2);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = l_Lean_Syntax_isOfKind(v_a_3426_, v___x_2939_);
lean_dec(v___x_2939_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_inc(v_ref_2935_);
lean_dec(v_a_3426_);
lean_dec(v___y_3422_);
lean_dec(v___x_2859_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3428_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3429_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3428_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v___y_2884_ = v___y_3420_;
v_stx_2885_ = v_a_3430_;
v___y_2886_ = v___y_2876_;
v_ref_2887_ = v_ref_2935_;
v___y_2888_ = v___y_2877_;
goto v___jp_2883_;
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v___y_3420_);
lean_dec(v_ref_2935_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v_tk_2844_);
v_a_3431_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3429_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3429_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3439_ = l_Lean_Syntax_getArg(v_a_3426_, v___x_2857_);
lean_inc(v___x_3439_);
v___x_3440_ = l_Lean_Syntax_isOfKind(v___x_3439_, v___x_2858_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_inc(v_ref_2935_);
lean_dec(v___x_3439_);
lean_dec(v_a_3426_);
lean_dec(v___y_3422_);
lean_dec(v___x_2859_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3441_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3442_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3441_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v___y_2884_ = v___y_3420_;
v_stx_2885_ = v_a_3443_;
v___y_2886_ = v___y_2876_;
v_ref_2887_ = v_ref_2935_;
v___y_2888_ = v___y_2877_;
goto v___jp_2883_;
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref(v___y_3420_);
lean_dec(v_ref_2935_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v_tk_2844_);
v_a_3444_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3442_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3452_ = l_Lean_Syntax_getArg(v_a_3426_, v___x_2859_);
lean_dec(v___x_2859_);
v___x_3453_ = l_Lean_Syntax_getArg(v_a_3426_, v___x_2856_);
v___x_3454_ = l_Lean_Syntax_isNone(v___x_3453_);
if (v___x_3454_ == 0)
{
uint8_t v___x_3455_; 
lean_inc(v___x_3453_);
v___x_3455_ = l_Lean_Syntax_matchesNull(v___x_3453_, v___x_2857_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_inc(v_ref_2935_);
lean_dec(v___x_3453_);
lean_dec(v___x_3452_);
lean_dec(v___x_3439_);
lean_dec(v_a_3426_);
lean_dec(v___y_3422_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
v___x_3456_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3457_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3456_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___y_2884_ = v___y_3420_;
v_stx_2885_ = v_a_3458_;
v___y_2886_ = v___y_2876_;
v_ref_2887_ = v_ref_2935_;
v___y_2888_ = v___y_2877_;
goto v___jp_2883_;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___y_3420_);
lean_dec(v_ref_2935_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v_tk_2844_);
v_a_3459_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3457_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3457_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = l_Lean_Syntax_getArg(v___x_3453_, v___x_2848_);
lean_dec(v___x_3453_);
v___x_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
v___y_3385_ = v___x_3452_;
v___y_3386_ = v___x_3439_;
v___y_3387_ = v___y_3419_;
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___y_3420_;
v___y_3390_ = v_a_3426_;
v_only_3391_ = v___x_3468_;
v___y_3392_ = v___y_2870_;
v___y_3393_ = v___y_2871_;
v___y_3394_ = v___y_2872_;
v___y_3395_ = v___y_2873_;
v___y_3396_ = v___y_2874_;
v___y_3397_ = v___y_2875_;
v___y_3398_ = v___y_2876_;
v___y_3399_ = v___y_2877_;
goto v___jp_3384_;
}
}
else
{
lean_object* v___x_3469_; 
lean_dec(v___x_3453_);
v___x_3469_ = lean_box(0);
v___y_3385_ = v___x_3452_;
v___y_3386_ = v___x_3439_;
v___y_3387_ = v___y_3419_;
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___y_3420_;
v___y_3390_ = v_a_3426_;
v_only_3391_ = v___x_3469_;
v___y_3392_ = v___y_2870_;
v___y_3393_ = v___y_2871_;
v___y_3394_ = v___y_2872_;
v___y_3395_ = v___y_2873_;
v___y_3396_ = v___y_2874_;
v___y_3397_ = v___y_2875_;
v___y_3398_ = v___y_2876_;
v___y_3399_ = v___y_2877_;
goto v___jp_3384_;
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3420_);
lean_dec(v___x_2939_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___x_2859_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3470_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3425_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3425_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
v___jp_3478_:
{
if (lean_obj_tag(v_usingArg_2860_) == 0)
{
v___y_3419_ = v___y_3479_;
v___y_3420_ = v___y_3480_;
v___y_3421_ = v___y_3481_;
v___y_3422_ = v_usingArg_2860_;
goto v___jp_3418_;
}
else
{
lean_object* v_val_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3490_; 
v_val_3482_ = lean_ctor_get(v_usingArg_2860_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_usingArg_2860_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3484_ = v_usingArg_2860_;
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_val_3482_);
lean_dec(v_usingArg_2860_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = l_Lean_Syntax_unsetTrailing(v_val_3482_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3486_);
v___x_3488_ = v___x_3484_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
v___y_3419_ = v___y_3479_;
v___y_3420_ = v___y_3480_;
v___y_3421_ = v___y_3481_;
v___y_3422_ = v___x_3488_;
goto v___jp_3418_;
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___f_3502_; lean_object* v___x_3503_; 
v___x_3497_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3496_, v___x_2936_);
v___x_3498_ = lean_box(v___x_2849_);
v___x_3499_ = lean_box(v___x_2936_);
v___x_3500_ = lean_box(v_useReducible_2852_);
v___x_3501_ = lean_box(v___x_2862_);
lean_inc_ref(v___x_2847_);
lean_inc_ref(v___x_2846_);
lean_inc_ref(v___x_2845_);
lean_inc_ref(v___f_2853_);
lean_inc(v___x_2857_);
lean_inc_ref(v___x_2854_);
lean_inc(v_usingArg_2860_);
lean_inc(v___x_2848_);
lean_inc(v_tk_2844_);
lean_inc(v___x_2859_);
v___f_3502_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3502_, 0, v___x_2859_);
lean_closure_set(v___f_3502_, 1, v_tk_2844_);
lean_closure_set(v___f_3502_, 2, v___x_2941_);
lean_closure_set(v___f_3502_, 3, v___x_2848_);
lean_closure_set(v___f_3502_, 4, v___x_3497_);
lean_closure_set(v___f_3502_, 5, v___y_3492_);
lean_closure_set(v___f_3502_, 6, v___x_3498_);
lean_closure_set(v___f_3502_, 7, v_usingArg_2860_);
lean_closure_set(v___f_3502_, 8, v___x_2854_);
lean_closure_set(v___f_3502_, 9, v___x_3499_);
lean_closure_set(v___f_3502_, 10, v___x_3500_);
lean_closure_set(v___f_3502_, 11, v___x_3501_);
lean_closure_set(v___f_3502_, 12, v___x_2857_);
lean_closure_set(v___f_3502_, 13, v___f_2853_);
lean_closure_set(v___f_3502_, 14, v___x_2845_);
lean_closure_set(v___f_3502_, 15, v___x_2846_);
lean_closure_set(v___f_3502_, 16, v___x_2847_);
lean_closure_set(v___f_3502_, 17, v___f_2863_);
lean_closure_set(v___f_3502_, 18, v_a_2934_);
lean_closure_set(v___f_3502_, 19, v_usingTk_x3f_2864_);
v___x_3503_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3494_, v___f_3502_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_3494_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2876_);
v___x_3506_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3507_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_3505_, v___x_3506_);
lean_dec_ref(v___x_3505_);
if (v___x_3507_ == 0)
{
if (lean_obj_tag(v_squeeze_2865_) == 0)
{
lean_dec(v___y_3495_);
lean_dec(v___x_2939_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v_usingArg_2860_);
lean_dec(v___x_2859_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v___y_2880_ = v_a_3504_;
goto v___jp_2879_;
}
else
{
v___y_3479_ = v___y_3493_;
v___y_3480_ = v_a_3504_;
v___y_3481_ = v___y_3495_;
goto v___jp_3478_;
}
}
else
{
v___y_3479_ = v___y_3493_;
v___y_3480_ = v_a_3504_;
v___y_3481_ = v___y_3495_;
goto v___jp_3478_;
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v___y_3495_);
lean_dec(v___x_2939_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v_usingArg_2860_);
lean_dec(v___x_2859_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3508_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3503_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3503_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
v___jp_3516_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3520_ = l_Array_append___redArg(v___x_2942_, v___y_3519_);
lean_dec_ref(v___y_3519_);
lean_inc_n(v___x_2937_, 2);
v___x_3521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3521_, 0, v___x_2937_);
lean_ctor_set(v___x_3521_, 1, v___x_2941_);
lean_ctor_set(v___x_3521_, 2, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3522_, 0, v___x_2937_);
lean_ctor_set(v___x_3522_, 1, v___x_2941_);
lean_ctor_set(v___x_3522_, 2, v___x_2942_);
lean_inc(v___x_2939_);
v___x_3523_ = l_Lean_Syntax_node6(v___x_2937_, v___x_2939_, v___x_2940_, v___x_2861_, v___y_3518_, v___y_3517_, v___x_3521_, v___x_3522_);
v___x_3524_ = 0;
v___x_3525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3526_ = lean_box(v___x_2936_);
v___x_3527_ = lean_box(v___x_3524_);
v___x_3528_ = lean_box(v___x_2936_);
lean_inc(v___x_3523_);
v___x_3529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3529_, 0, v___x_3523_);
lean_closure_set(v___x_3529_, 1, v___x_3526_);
lean_closure_set(v___x_3529_, 2, v___x_3527_);
lean_closure_set(v___x_3529_, 3, v___x_3528_);
lean_closure_set(v___x_3529_, 4, v___x_3525_);
v___x_3530_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3529_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
if (lean_obj_tag(v_unfold_2866_) == 0)
{
lean_object* v_ctx_3532_; lean_object* v_simprocs_3533_; lean_object* v_dischargeWrapper_3534_; 
v_ctx_3532_ = lean_ctor_get(v_a_3531_, 0);
lean_inc_ref(v_ctx_3532_);
v_simprocs_3533_ = lean_ctor_get(v_a_3531_, 1);
lean_inc_ref(v_simprocs_3533_);
v_dischargeWrapper_3534_ = lean_ctor_get(v_a_3531_, 2);
lean_inc(v_dischargeWrapper_3534_);
lean_dec(v_a_3531_);
v___y_3492_ = v_simprocs_3533_;
v___y_3493_ = v___x_2936_;
v___y_3494_ = v_dischargeWrapper_3534_;
v___y_3495_ = v___x_3523_;
v___y_3496_ = v_ctx_3532_;
goto v___jp_3491_;
}
else
{
lean_object* v_ctx_3535_; lean_object* v_simprocs_3536_; lean_object* v_dischargeWrapper_3537_; lean_object* v___x_3538_; 
v_ctx_3535_ = lean_ctor_get(v_a_3531_, 0);
lean_inc_ref(v_ctx_3535_);
v_simprocs_3536_ = lean_ctor_get(v_a_3531_, 1);
lean_inc_ref(v_simprocs_3536_);
v_dischargeWrapper_3537_ = lean_ctor_get(v_a_3531_, 2);
lean_inc(v_dischargeWrapper_3537_);
lean_dec(v_a_3531_);
v___x_3538_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3535_);
v___y_3492_ = v_simprocs_3536_;
v___y_3493_ = v___x_2862_;
v___y_3494_ = v_dischargeWrapper_3537_;
v___y_3495_ = v___x_3523_;
v___y_3496_ = v___x_3538_;
goto v___jp_3491_;
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v___x_3523_);
lean_dec(v___x_2939_);
lean_dec(v_a_2934_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v_usingTk_x3f_2864_);
lean_dec_ref(v___f_2863_);
lean_dec(v_usingArg_2860_);
lean_dec(v___x_2859_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3539_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3530_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3530_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
v___jp_3547_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = l_Array_append___redArg(v___x_2942_, v___y_3549_);
lean_dec_ref(v___y_3549_);
lean_inc(v___x_2937_);
v___x_3551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3551_, 0, v___x_2937_);
lean_ctor_set(v___x_3551_, 1, v___x_2941_);
lean_ctor_set(v___x_3551_, 2, v___x_3550_);
if (lean_obj_tag(v_args_2867_) == 1)
{
lean_object* v_val_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_val_3552_ = lean_ctor_get(v_args_2867_, 0);
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___x_2937_, 3);
v___x_3554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_2937_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = l_Array_append___redArg(v___x_2942_, v_val_3552_);
v___x_3556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3556_, 0, v___x_2937_);
lean_ctor_set(v___x_3556_, 1, v___x_2941_);
lean_ctor_set(v___x_3556_, 2, v___x_3555_);
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_3558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_2937_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = l_Array_mkArray3___redArg(v___x_3554_, v___x_3556_, v___x_3558_);
v___y_3517_ = v___x_3551_;
v___y_3518_ = v___y_3548_;
v___y_3519_ = v___x_3559_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3517_ = v___x_3551_;
v___y_3518_ = v___y_3548_;
v___y_3519_ = v___x_3560_;
goto v___jp_3516_;
}
}
v___jp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = l_Array_append___redArg(v___x_2942_, v___y_3562_);
lean_dec_ref(v___y_3562_);
lean_inc(v___x_2937_);
v___x_3564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3564_, 0, v___x_2937_);
lean_ctor_set(v___x_3564_, 1, v___x_2941_);
lean_ctor_set(v___x_3564_, 2, v___x_3563_);
if (lean_obj_tag(v_only_2868_) == 1)
{
lean_object* v_val_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_val_3565_ = lean_ctor_get(v_only_2868_, 0);
v___x_3566_ = l_Lean_SourceInfo_fromRef(v_val_3565_, v___x_2849_);
v___x_3567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_3568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Array_mkArray1___redArg(v___x_3568_);
v___y_3548_ = v___x_3564_;
v___y_3549_ = v___x_3569_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___y_3548_ = v___x_3564_;
v___y_3549_ = v___x_3570_;
goto v___jp_3547_;
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v_usingTk_x3f_2864_);
lean_dec_ref(v___f_2863_);
lean_dec(v___x_2861_);
lean_dec(v_usingArg_2860_);
lean_dec(v___x_2859_);
lean_dec(v___x_2857_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___f_2853_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec_ref(v___x_2846_);
lean_dec_ref(v___x_2845_);
lean_dec(v_tk_2844_);
v_a_3575_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_2933_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_2933_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
v___jp_2879_:
{
lean_object* v_diag_2881_; lean_object* v___x_2882_; 
v_diag_2881_ = lean_ctor_get(v___y_2880_, 1);
lean_inc_ref(v_diag_2881_);
lean_dec_ref(v___y_2880_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_diag_2881_);
return v___x_2882_;
}
v___jp_2883_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v_stx_2885_);
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
lean_ctor_set(v___x_2892_, 2, v___x_2891_);
lean_ctor_set(v___x_2892_, 3, v___x_2891_);
lean_ctor_set(v___x_2892_, 4, v___x_2891_);
lean_ctor_set(v___x_2892_, 5, v___x_2891_);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_ref_2887_);
v___x_2894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0));
v___x_2895_ = 4;
v___x_2896_ = l_Lean_MessageData_nil;
v___x_2897_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2844_, v___x_2892_, v___x_2893_, v___x_2894_, v___x_2891_, v___x_2895_, v___x_2896_, v___y_2886_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2886_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_dec_ref_known(v___x_2897_, 1);
v___y_2880_ = v___y_2884_;
goto v___jp_2879_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v___y_2884_);
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
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
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
v___jp_2906_:
{
lean_object* v_ref_2911_; 
v_ref_2911_ = lean_ctor_get(v___y_2909_, 2);
lean_inc(v_ref_2911_);
v___y_2884_ = v___y_2907_;
v_stx_2885_ = v_stx_2908_;
v___y_2886_ = v___y_2909_;
v_ref_2887_ = v_ref_2911_;
v___y_2888_ = v___y_2910_;
goto v___jp_2883_;
}
v___jp_2912_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4);
v___x_2923_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_2922_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___y_2907_ = v___y_2913_;
v_stx_2908_ = v_a_2924_;
v___y_2909_ = v___y_2920_;
v___y_2910_ = v___y_2921_;
goto v___jp_2906_;
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___y_2913_);
lean_dec(v_tk_2844_);
v_a_2925_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2923_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2923_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object** _args){
lean_object* v_tk_3583_ = _args[0];
lean_object* v___x_3584_ = _args[1];
lean_object* v___x_3585_ = _args[2];
lean_object* v___x_3586_ = _args[3];
lean_object* v___x_3587_ = _args[4];
lean_object* v___x_3588_ = _args[5];
lean_object* v___x_3589_ = _args[6];
lean_object* v___x_3590_ = _args[7];
lean_object* v_useReducible_3591_ = _args[8];
lean_object* v___f_3592_ = _args[9];
lean_object* v___x_3593_ = _args[10];
lean_object* v___x_3594_ = _args[11];
lean_object* v___x_3595_ = _args[12];
lean_object* v___x_3596_ = _args[13];
lean_object* v___x_3597_ = _args[14];
lean_object* v___x_3598_ = _args[15];
lean_object* v_usingArg_3599_ = _args[16];
lean_object* v___x_3600_ = _args[17];
lean_object* v___x_3601_ = _args[18];
lean_object* v___f_3602_ = _args[19];
lean_object* v_usingTk_x3f_3603_ = _args[20];
lean_object* v_squeeze_3604_ = _args[21];
lean_object* v_unfold_3605_ = _args[22];
lean_object* v_args_3606_ = _args[23];
lean_object* v_only_3607_ = _args[24];
lean_object* v___y_3608_ = _args[25];
lean_object* v___y_3609_ = _args[26];
lean_object* v___y_3610_ = _args[27];
lean_object* v___y_3611_ = _args[28];
lean_object* v___y_3612_ = _args[29];
lean_object* v___y_3613_ = _args[30];
lean_object* v___y_3614_ = _args[31];
lean_object* v___y_3615_ = _args[32];
lean_object* v___y_3616_ = _args[33];
lean_object* v___y_3617_ = _args[34];
_start:
{
uint8_t v___x_97578__boxed_3618_; uint8_t v_useReducible_boxed_3619_; uint8_t v___x_97589__boxed_3620_; lean_object* v_res_3621_; 
v___x_97578__boxed_3618_ = lean_unbox(v___x_3588_);
v_useReducible_boxed_3619_ = lean_unbox(v_useReducible_3591_);
v___x_97589__boxed_3620_ = lean_unbox(v___x_3601_);
v_res_3621_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3583_, v___x_3584_, v___x_3585_, v___x_3586_, v___x_3587_, v___x_97578__boxed_3618_, v___x_3589_, v___x_3590_, v_useReducible_boxed_3619_, v___f_3592_, v___x_3593_, v___x_3594_, v___x_3595_, v___x_3596_, v___x_3597_, v___x_3598_, v_usingArg_3599_, v___x_3600_, v___x_97589__boxed_3620_, v___f_3602_, v_usingTk_x3f_3603_, v_squeeze_3604_, v_unfold_3605_, v_args_3606_, v_only_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v_only_3607_);
lean_dec(v_args_3606_);
lean_dec(v_unfold_3605_);
lean_dec(v_squeeze_3604_);
lean_dec(v___x_3597_);
lean_dec(v___x_3595_);
lean_dec(v___x_3594_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3647_, lean_object* v_stx_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_3659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3660_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3648_);
v___x_3663_ = l_Lean_Syntax_isOfKind(v_stx_3648_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
lean_dec(v_stx_3648_);
v___x_3664_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3664_;
}
else
{
lean_object* v___f_3665_; lean_object* v___x_3666_; lean_object* v_tk_3667_; lean_object* v___x_3668_; uint8_t v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; uint8_t v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v_usingTk_x3f_3721_; lean_object* v_usingArg_3722_; uint8_t v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v_args_3754_; uint8_t v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v_only_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v_unfold_3810_; lean_object* v_squeeze_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___f_3665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3666_ = lean_unsigned_to_nat(0u);
v_tk_3667_ = l_Lean_Syntax_getArg(v_stx_3648_, v___x_3666_);
v___x_3668_ = lean_unsigned_to_nat(1u);
v___x_3846_ = l_Lean_Syntax_getArg(v_stx_3648_, v___x_3668_);
v___x_3847_ = l_Lean_Syntax_isNone(v___x_3846_);
if (v___x_3847_ == 0)
{
uint8_t v___x_3848_; 
lean_inc(v___x_3846_);
v___x_3848_ = l_Lean_Syntax_matchesNull(v___x_3846_, v___x_3668_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
lean_dec(v___x_3846_);
lean_dec(v_tk_3667_);
lean_dec(v_stx_3648_);
v___x_3849_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3849_;
}
else
{
lean_object* v_squeeze_3850_; lean_object* v___x_3851_; 
v_squeeze_3850_ = l_Lean_Syntax_getArg(v___x_3846_, v___x_3666_);
lean_dec(v___x_3846_);
v___x_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_squeeze_3850_);
v_squeeze_3829_ = v___x_3851_;
v___y_3830_ = v_a_3649_;
v___y_3831_ = v_a_3650_;
v___y_3832_ = v_a_3651_;
v___y_3833_ = v_a_3652_;
v___y_3834_ = v_a_3653_;
v___y_3835_ = v_a_3654_;
v___y_3836_ = v_a_3655_;
v___y_3837_ = v_a_3656_;
goto v___jp_3828_;
}
}
else
{
lean_object* v___x_3852_; 
lean_dec(v___x_3846_);
v___x_3852_ = lean_box(0);
v_squeeze_3829_ = v___x_3852_;
v___y_3830_ = v_a_3649_;
v___y_3831_ = v_a_3650_;
v___y_3832_ = v_a_3651_;
v___y_3833_ = v_a_3652_;
v___y_3834_ = v_a_3653_;
v___y_3835_ = v_a_3654_;
v___y_3836_ = v_a_3655_;
v___y_3837_ = v_a_3656_;
goto v___jp_3828_;
}
v___jp_3669_:
{
lean_object* v___x_3692_; lean_object* v___f_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___f_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3692_ = lean_box(v___x_3663_);
lean_inc(v___y_3691_);
lean_inc(v___y_3681_);
lean_inc(v___y_3683_);
lean_inc(v___y_3671_);
lean_inc(v___y_3685_);
lean_inc(v___y_3676_);
v___f_3693_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 21, 11);
lean_closure_set(v___f_3693_, 0, v___y_3676_);
lean_closure_set(v___f_3693_, 1, v___y_3685_);
lean_closure_set(v___f_3693_, 2, v___x_3658_);
lean_closure_set(v___f_3693_, 3, v___x_3659_);
lean_closure_set(v___f_3693_, 4, v___x_3660_);
lean_closure_set(v___f_3693_, 5, v___y_3671_);
lean_closure_set(v___f_3693_, 6, v___x_3666_);
lean_closure_set(v___f_3693_, 7, v___y_3683_);
lean_closure_set(v___f_3693_, 8, v___y_3681_);
lean_closure_set(v___f_3693_, 9, v___x_3692_);
lean_closure_set(v___f_3693_, 10, v___y_3691_);
v___x_3694_ = lean_box(v___x_3663_);
v___x_3695_ = lean_box(v_useReducible_3647_);
v___x_3696_ = lean_box(v___y_3670_);
lean_inc(v___y_3687_);
lean_inc(v___y_3674_);
v___f_3697_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3697_, 0, v_tk_3667_);
lean_closure_set(v___f_3697_, 1, v___x_3658_);
lean_closure_set(v___f_3697_, 2, v___x_3659_);
lean_closure_set(v___f_3697_, 3, v___x_3660_);
lean_closure_set(v___f_3697_, 4, v___x_3666_);
lean_closure_set(v___f_3697_, 5, v___x_3694_);
lean_closure_set(v___f_3697_, 6, v___y_3674_);
lean_closure_set(v___f_3697_, 7, v___x_3662_);
lean_closure_set(v___f_3697_, 8, v___x_3695_);
lean_closure_set(v___f_3697_, 9, v___f_3665_);
lean_closure_set(v___f_3697_, 10, v___x_3661_);
lean_closure_set(v___f_3697_, 11, v___y_3690_);
lean_closure_set(v___f_3697_, 12, v___y_3678_);
lean_closure_set(v___f_3697_, 13, v___x_3668_);
lean_closure_set(v___f_3697_, 14, v___y_3687_);
lean_closure_set(v___f_3697_, 15, v___y_3686_);
lean_closure_set(v___f_3697_, 16, v___y_3688_);
lean_closure_set(v___f_3697_, 17, v___y_3671_);
lean_closure_set(v___f_3697_, 18, v___x_3696_);
lean_closure_set(v___f_3697_, 19, v___f_3693_);
lean_closure_set(v___f_3697_, 20, v___y_3684_);
lean_closure_set(v___f_3697_, 21, v___y_3676_);
lean_closure_set(v___f_3697_, 22, v___y_3685_);
lean_closure_set(v___f_3697_, 23, v___y_3683_);
lean_closure_set(v___f_3697_, 24, v___y_3681_);
lean_closure_set(v___f_3697_, 25, v___y_3691_);
v___x_3698_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3698_, 0, v___f_3697_);
v___x_3699_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3698_, v___y_3679_, v___y_3675_, v___y_3673_, v___y_3680_, v___y_3677_, v___y_3672_, v___y_3689_, v___y_3682_);
return v___x_3699_;
}
v___jp_3700_:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_Syntax_getOptional_x3f(v___y_3715_);
lean_dec(v___y_3715_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_box(0);
v___y_3670_ = v___y_3701_;
v___y_3671_ = v___y_3702_;
v___y_3672_ = v___y_3703_;
v___y_3673_ = v___y_3704_;
v___y_3674_ = v___y_3705_;
v___y_3675_ = v___y_3706_;
v___y_3676_ = v___y_3707_;
v___y_3677_ = v___y_3708_;
v___y_3678_ = v___y_3709_;
v___y_3679_ = v___y_3710_;
v___y_3680_ = v___y_3711_;
v___y_3681_ = v___y_3712_;
v___y_3682_ = v___y_3713_;
v___y_3683_ = v___y_3714_;
v___y_3684_ = v_usingTk_x3f_3721_;
v___y_3685_ = v___y_3716_;
v___y_3686_ = v___y_3717_;
v___y_3687_ = v___y_3718_;
v___y_3688_ = v_usingArg_3722_;
v___y_3689_ = v___y_3719_;
v___y_3690_ = v___y_3720_;
v___y_3691_ = v___x_3724_;
goto v___jp_3669_;
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
v_val_3725_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3723_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_val_3725_);
lean_dec(v___x_3723_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_val_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
v___y_3670_ = v___y_3701_;
v___y_3671_ = v___y_3702_;
v___y_3672_ = v___y_3703_;
v___y_3673_ = v___y_3704_;
v___y_3674_ = v___y_3705_;
v___y_3675_ = v___y_3706_;
v___y_3676_ = v___y_3707_;
v___y_3677_ = v___y_3708_;
v___y_3678_ = v___y_3709_;
v___y_3679_ = v___y_3710_;
v___y_3680_ = v___y_3711_;
v___y_3681_ = v___y_3712_;
v___y_3682_ = v___y_3713_;
v___y_3683_ = v___y_3714_;
v___y_3684_ = v_usingTk_x3f_3721_;
v___y_3685_ = v___y_3716_;
v___y_3686_ = v___y_3717_;
v___y_3687_ = v___y_3718_;
v___y_3688_ = v_usingArg_3722_;
v___y_3689_ = v___y_3719_;
v___y_3690_ = v___y_3720_;
v___y_3691_ = v___x_3730_;
goto v___jp_3669_;
}
}
}
}
v___jp_3733_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3755_ = lean_unsigned_to_nat(4u);
v___x_3756_ = l_Lean_Syntax_getArg(v___y_3748_, v___x_3755_);
lean_dec(v___y_3748_);
v___x_3757_ = l_Lean_Syntax_isNone(v___x_3756_);
if (v___x_3757_ == 0)
{
uint8_t v___x_3758_; 
lean_inc(v___x_3756_);
v___x_3758_ = l_Lean_Syntax_matchesNull(v___x_3756_, v___y_3742_);
lean_dec(v___y_3742_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
lean_dec(v___x_3756_);
lean_dec(v_args_3754_);
lean_dec(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec(v___y_3746_);
lean_dec(v___y_3743_);
lean_dec(v___y_3740_);
lean_dec(v___y_3735_);
lean_dec(v_tk_3667_);
v___x_3759_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3759_;
}
else
{
lean_object* v_usingTk_x3f_3760_; lean_object* v_usingArg_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_usingTk_x3f_3760_ = l_Lean_Syntax_getArg(v___x_3756_, v___x_3666_);
v_usingArg_3761_ = l_Lean_Syntax_getArg(v___x_3756_, v___x_3668_);
lean_dec(v___x_3756_);
v___x_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3762_, 0, v_usingTk_x3f_3760_);
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_usingArg_3761_);
v___y_3701_ = v___y_3734_;
v___y_3702_ = v___y_3735_;
v___y_3703_ = v___y_3736_;
v___y_3704_ = v___y_3737_;
v___y_3705_ = v___y_3738_;
v___y_3706_ = v___y_3739_;
v___y_3707_ = v___y_3740_;
v___y_3708_ = v___y_3741_;
v___y_3709_ = v___y_3743_;
v___y_3710_ = v___y_3744_;
v___y_3711_ = v___y_3745_;
v___y_3712_ = v___y_3746_;
v___y_3713_ = v___y_3747_;
v___y_3714_ = v_args_3754_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v___y_3749_;
v___y_3717_ = v___y_3751_;
v___y_3718_ = v___y_3752_;
v___y_3719_ = v___y_3753_;
v___y_3720_ = v___x_3755_;
v_usingTk_x3f_3721_ = v___x_3762_;
v_usingArg_3722_ = v___x_3763_;
goto v___jp_3700_;
}
}
else
{
lean_object* v___x_3764_; 
lean_dec(v___x_3756_);
lean_dec(v___y_3742_);
v___x_3764_ = lean_box(0);
v___y_3701_ = v___y_3734_;
v___y_3702_ = v___y_3735_;
v___y_3703_ = v___y_3736_;
v___y_3704_ = v___y_3737_;
v___y_3705_ = v___y_3738_;
v___y_3706_ = v___y_3739_;
v___y_3707_ = v___y_3740_;
v___y_3708_ = v___y_3741_;
v___y_3709_ = v___y_3743_;
v___y_3710_ = v___y_3744_;
v___y_3711_ = v___y_3745_;
v___y_3712_ = v___y_3746_;
v___y_3713_ = v___y_3747_;
v___y_3714_ = v_args_3754_;
v___y_3715_ = v___y_3750_;
v___y_3716_ = v___y_3749_;
v___y_3717_ = v___y_3751_;
v___y_3718_ = v___y_3752_;
v___y_3719_ = v___y_3753_;
v___y_3720_ = v___x_3755_;
v_usingTk_x3f_3721_ = v___x_3764_;
v_usingArg_3722_ = v___x_3764_;
goto v___jp_3700_;
}
}
v___jp_3765_:
{
lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3787_ = l_Lean_Syntax_getArg(v___y_3776_, v___y_3775_);
lean_dec(v___y_3775_);
v___x_3788_ = l_Lean_Syntax_isNone(v___x_3787_);
if (v___x_3788_ == 0)
{
uint8_t v___x_3789_; 
lean_inc(v___x_3787_);
v___x_3789_ = l_Lean_Syntax_matchesNull(v___x_3787_, v___x_3668_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; 
lean_dec(v___x_3787_);
lean_dec(v_only_3778_);
lean_dec(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec(v___y_3767_);
lean_dec(v_tk_3667_);
v___x_3790_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3791_ = l_Lean_Syntax_getArg(v___x_3787_, v___x_3666_);
lean_dec(v___x_3787_);
v___x_3792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3791_);
v___x_3793_ = l_Lean_Syntax_isOfKind(v___x_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; 
lean_dec(v___x_3791_);
lean_dec(v_only_3778_);
lean_dec(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec(v___y_3767_);
lean_dec(v_tk_3667_);
v___x_3794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3794_;
}
else
{
lean_object* v___x_3795_; lean_object* v_args_3796_; lean_object* v___x_3797_; 
v___x_3795_ = l_Lean_Syntax_getArg(v___x_3791_, v___x_3668_);
lean_dec(v___x_3791_);
v_args_3796_ = l_Lean_Syntax_getArgs(v___x_3795_);
lean_dec(v___x_3795_);
v___x_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_args_3796_);
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3784_;
v___y_3737_ = v___y_3781_;
v___y_3738_ = v___y_3768_;
v___y_3739_ = v___y_3780_;
v___y_3740_ = v___y_3771_;
v___y_3741_ = v___y_3783_;
v___y_3742_ = v___y_3774_;
v___y_3743_ = v___y_3773_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___y_3782_;
v___y_3746_ = v_only_3778_;
v___y_3747_ = v___y_3786_;
v___y_3748_ = v___y_3776_;
v___y_3749_ = v___y_3769_;
v___y_3750_ = v___y_3777_;
v___y_3751_ = v___y_3770_;
v___y_3752_ = v___y_3772_;
v___y_3753_ = v___y_3785_;
v_args_3754_ = v___x_3797_;
goto v___jp_3733_;
}
}
}
else
{
lean_object* v___x_3798_; 
lean_dec(v___x_3787_);
v___x_3798_ = lean_box(0);
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3767_;
v___y_3736_ = v___y_3784_;
v___y_3737_ = v___y_3781_;
v___y_3738_ = v___y_3768_;
v___y_3739_ = v___y_3780_;
v___y_3740_ = v___y_3771_;
v___y_3741_ = v___y_3783_;
v___y_3742_ = v___y_3774_;
v___y_3743_ = v___y_3773_;
v___y_3744_ = v___y_3779_;
v___y_3745_ = v___y_3782_;
v___y_3746_ = v_only_3778_;
v___y_3747_ = v___y_3786_;
v___y_3748_ = v___y_3776_;
v___y_3749_ = v___y_3769_;
v___y_3750_ = v___y_3777_;
v___y_3751_ = v___y_3770_;
v___y_3752_ = v___y_3772_;
v___y_3753_ = v___y_3785_;
v_args_3754_ = v___x_3798_;
goto v___jp_3733_;
}
}
v___jp_3799_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3811_ = lean_unsigned_to_nat(3u);
v___x_3812_ = l_Lean_Syntax_getArg(v_stx_3648_, v___x_3811_);
lean_dec(v_stx_3648_);
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3812_);
v___x_3814_ = l_Lean_Syntax_isOfKind(v___x_3812_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec(v___x_3812_);
lean_dec(v_unfold_3810_);
lean_dec(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec(v_tk_3667_);
v___x_3815_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3815_;
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3816_ = l_Lean_Syntax_getArg(v___x_3812_, v___x_3666_);
v___x_3817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3816_);
v___x_3818_ = l_Lean_Syntax_isOfKind(v___x_3816_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; 
lean_dec(v___x_3816_);
lean_dec(v___x_3812_);
lean_dec(v_unfold_3810_);
lean_dec(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec(v_tk_3667_);
v___x_3819_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3819_;
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = l_Lean_Syntax_getArg(v___x_3812_, v___x_3668_);
v___x_3821_ = l_Lean_Syntax_getArg(v___x_3812_, v___y_3805_);
v___x_3822_ = l_Lean_Syntax_isNone(v___x_3821_);
if (v___x_3822_ == 0)
{
uint8_t v___x_3823_; 
lean_inc(v___x_3821_);
v___x_3823_ = l_Lean_Syntax_matchesNull(v___x_3821_, v___x_3668_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; 
lean_dec(v___x_3821_);
lean_dec(v___x_3820_);
lean_dec(v___x_3816_);
lean_dec(v___x_3812_);
lean_dec(v_unfold_3810_);
lean_dec(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec(v_tk_3667_);
v___x_3824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3824_;
}
else
{
lean_object* v_only_3825_; lean_object* v___x_3826_; 
v_only_3825_ = l_Lean_Syntax_getArg(v___x_3821_, v___x_3666_);
lean_dec(v___x_3821_);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_only_3825_);
lean_inc(v___y_3805_);
v___y_3766_ = v___x_3814_;
v___y_3767_ = v___x_3816_;
v___y_3768_ = v___x_3813_;
v___y_3769_ = v_unfold_3810_;
v___y_3770_ = v___y_3805_;
v___y_3771_ = v___y_3804_;
v___y_3772_ = v___x_3817_;
v___y_3773_ = v___x_3811_;
v___y_3774_ = v___y_3805_;
v___y_3775_ = v___x_3811_;
v___y_3776_ = v___x_3812_;
v___y_3777_ = v___x_3820_;
v_only_3778_ = v___x_3826_;
v___y_3779_ = v___y_3809_;
v___y_3780_ = v___y_3807_;
v___y_3781_ = v___y_3808_;
v___y_3782_ = v___y_3801_;
v___y_3783_ = v___y_3802_;
v___y_3784_ = v___y_3803_;
v___y_3785_ = v___y_3800_;
v___y_3786_ = v___y_3806_;
goto v___jp_3765_;
}
}
else
{
lean_object* v___x_3827_; 
lean_dec(v___x_3821_);
v___x_3827_ = lean_box(0);
lean_inc(v___y_3805_);
v___y_3766_ = v___x_3814_;
v___y_3767_ = v___x_3816_;
v___y_3768_ = v___x_3813_;
v___y_3769_ = v_unfold_3810_;
v___y_3770_ = v___y_3805_;
v___y_3771_ = v___y_3804_;
v___y_3772_ = v___x_3817_;
v___y_3773_ = v___x_3811_;
v___y_3774_ = v___y_3805_;
v___y_3775_ = v___x_3811_;
v___y_3776_ = v___x_3812_;
v___y_3777_ = v___x_3820_;
v_only_3778_ = v___x_3827_;
v___y_3779_ = v___y_3809_;
v___y_3780_ = v___y_3807_;
v___y_3781_ = v___y_3808_;
v___y_3782_ = v___y_3801_;
v___y_3783_ = v___y_3802_;
v___y_3784_ = v___y_3803_;
v___y_3785_ = v___y_3800_;
v___y_3786_ = v___y_3806_;
goto v___jp_3765_;
}
}
}
}
v___jp_3828_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v___x_3838_ = lean_unsigned_to_nat(2u);
v___x_3839_ = l_Lean_Syntax_getArg(v_stx_3648_, v___x_3838_);
v___x_3840_ = l_Lean_Syntax_isNone(v___x_3839_);
if (v___x_3840_ == 0)
{
uint8_t v___x_3841_; 
lean_inc(v___x_3839_);
v___x_3841_ = l_Lean_Syntax_matchesNull(v___x_3839_, v___x_3668_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; 
lean_dec(v___x_3839_);
lean_dec(v_squeeze_3829_);
lean_dec(v_tk_3667_);
lean_dec(v_stx_3648_);
v___x_3842_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3842_;
}
else
{
lean_object* v_unfold_3843_; lean_object* v___x_3844_; 
v_unfold_3843_ = l_Lean_Syntax_getArg(v___x_3839_, v___x_3666_);
lean_dec(v___x_3839_);
v___x_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3844_, 0, v_unfold_3843_);
v___y_3800_ = v___y_3836_;
v___y_3801_ = v___y_3833_;
v___y_3802_ = v___y_3834_;
v___y_3803_ = v___y_3835_;
v___y_3804_ = v_squeeze_3829_;
v___y_3805_ = v___x_3838_;
v___y_3806_ = v___y_3837_;
v___y_3807_ = v___y_3831_;
v___y_3808_ = v___y_3832_;
v___y_3809_ = v___y_3830_;
v_unfold_3810_ = v___x_3844_;
goto v___jp_3799_;
}
}
else
{
lean_object* v___x_3845_; 
lean_dec(v___x_3839_);
v___x_3845_ = lean_box(0);
v___y_3800_ = v___y_3836_;
v___y_3801_ = v___y_3833_;
v___y_3802_ = v___y_3834_;
v___y_3803_ = v___y_3835_;
v___y_3804_ = v_squeeze_3829_;
v___y_3805_ = v___x_3838_;
v___y_3806_ = v___y_3837_;
v___y_3807_ = v___y_3831_;
v___y_3808_ = v___y_3832_;
v___y_3809_ = v___y_3830_;
v_unfold_3810_ = v___x_3845_;
goto v___jp_3799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3853_, lean_object* v_stx_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
uint8_t v_useReducible_boxed_3864_; lean_object* v_res_3865_; 
v_useReducible_boxed_3864_ = lean_unbox(v_useReducible_3853_);
v_res_3865_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3864_, v_stx_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_3866_, lean_object* v_val_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_3866_, v_val_3867_, v___y_3873_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_3878_, lean_object* v_val_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_3878_, v_val_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_o_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_3890_, v___y_3898_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___boxed(lean_object* v_o_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(v_o_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_3912_, lean_object* v_msg_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_3913_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_3924_, lean_object* v_msg_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_3924_, v_msg_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v_00_u03b1_3936_, lean_object* v_x_3937_, lean_object* v_mkInfoTree_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_3937_, v_mkInfoTree_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v_00_u03b1_3949_, lean_object* v_x_3950_, lean_object* v_mkInfoTree_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v_00_u03b1_3949_, v_x_3950_, v_mkInfoTree_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_00_u03b2_3962_, lean_object* v_x_3963_, lean_object* v_x_3964_, lean_object* v_x_3965_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_x_3963_, v_x_3964_, v_x_3965_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3967_, lean_object* v_x_3968_, size_t v_x_3969_, size_t v_x_3970_, lean_object* v_x_3971_, lean_object* v_x_3972_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_3968_, v_x_3969_, v_x_3970_, v_x_3971_, v_x_3972_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3974_, lean_object* v_x_3975_, lean_object* v_x_3976_, lean_object* v_x_3977_, lean_object* v_x_3978_, lean_object* v_x_3979_){
_start:
{
size_t v_x_99725__boxed_3980_; size_t v_x_99726__boxed_3981_; lean_object* v_res_3982_; 
v_x_99725__boxed_3980_ = lean_unbox_usize(v_x_3976_);
lean_dec(v_x_3976_);
v_x_99726__boxed_3981_ = lean_unbox_usize(v_x_3977_);
lean_dec(v_x_3977_);
v_res_3982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_3974_, v_x_3975_, v_x_99725__boxed_3980_, v_x_99726__boxed_3981_, v_x_3978_, v_x_3979_);
return v_res_3982_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_3983_, lean_object* v_m_3984_, lean_object* v_a_3985_){
_start:
{
uint8_t v___x_3986_; 
v___x_3986_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_3984_, v_a_3985_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3987_, lean_object* v_m_3988_, lean_object* v_a_3989_){
_start:
{
uint8_t v_res_3990_; lean_object* v_r_3991_; 
v_res_3990_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(v_00_u03b2_3987_, v_m_3988_, v_a_3989_);
lean_dec_ref(v_a_3989_);
lean_dec_ref(v_m_3988_);
v_r_3991_ = lean_box(v_res_3990_);
return v_r_3991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_3992_, lean_object* v_m_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_m_3993_, v_a_3994_, v_b_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(lean_object* v_mvarId_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_3997_, v___y_3998_, v___y_4004_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___boxed(lean_object* v_mvarId_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(v_mvarId_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v_mvarId_4009_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(lean_object* v_mvarId_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_4021_, v___y_4022_, v___y_4028_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___boxed(lean_object* v_mvarId_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(v_mvarId_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v_mvarId_4033_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4045_, lean_object* v_n_4046_, lean_object* v_k_4047_, lean_object* v_v_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_n_4046_, v_k_4047_, v_v_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_4050_, size_t v_depth_4051_, lean_object* v_keys_4052_, lean_object* v_vals_4053_, lean_object* v_heq_4054_, lean_object* v_i_4055_, lean_object* v_entries_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_4051_, v_keys_4052_, v_vals_4053_, v_i_4055_, v_entries_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_4058_, lean_object* v_depth_4059_, lean_object* v_keys_4060_, lean_object* v_vals_4061_, lean_object* v_heq_4062_, lean_object* v_i_4063_, lean_object* v_entries_4064_){
_start:
{
size_t v_depth_boxed_4065_; lean_object* v_res_4066_; 
v_depth_boxed_4065_ = lean_unbox_usize(v_depth_4059_);
lean_dec(v_depth_4059_);
v_res_4066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(v_00_u03b2_4058_, v_depth_boxed_4065_, v_keys_4060_, v_vals_4061_, v_heq_4062_, v_i_4063_, v_entries_4064_);
lean_dec_ref(v_vals_4061_);
lean_dec_ref(v_keys_4060_);
return v_res_4066_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(lean_object* v_00_u03b2_4067_, lean_object* v_a_4068_, lean_object* v_x_4069_){
_start:
{
uint8_t v___x_4070_; 
v___x_4070_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_4068_, v_x_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03b2_4071_, lean_object* v_a_4072_, lean_object* v_x_4073_){
_start:
{
uint8_t v_res_4074_; lean_object* v_r_4075_; 
v_res_4074_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(v_00_u03b2_4071_, v_a_4072_, v_x_4073_);
lean_dec(v_x_4073_);
lean_dec_ref(v_a_4072_);
v_r_4075_ = lean_box(v_res_4074_);
return v_r_4075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17(lean_object* v_00_u03b2_4076_, lean_object* v_data_4077_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_data_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_4079_, lean_object* v_x_4080_, lean_object* v_x_4081_, lean_object* v_x_4082_, lean_object* v_x_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_x_4080_, v_x_4081_, v_x_4082_, v_x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19(lean_object* v_00_u03b2_4085_, lean_object* v_i_4086_, lean_object* v_source_4087_, lean_object* v_target_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v_i_4086_, v_source_4087_, v_target_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23(lean_object* v_00_u03b2_4090_, lean_object* v_x_4091_, lean_object* v_x_4092_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_x_4091_, v_x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
uint8_t v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = 1;
v___x_4105_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_4104_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
lean_dec(v_a_4112_);
lean_dec_ref(v_a_4111_);
lean_dec(v_a_4110_);
lean_dec_ref(v_a_4109_);
lean_dec(v_a_4108_);
lean_dec_ref(v_a_4107_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4126_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4129_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_4130_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4126_, v___x_4127_, v___x_4128_, v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_4161_ = l_Lean_addBuiltinDeclarationRanges(v___x_4159_, v___x_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_4166_){
_start:
{
lean_object* v___x_4167_; 
v___x_4167_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_4168_);
lean_dec(v_x_4168_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; uint8_t v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___x_4222_; uint8_t v___x_4223_; 
v___x_4222_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_4181_);
v___x_4223_ = l_Lean_Syntax_isOfKind(v_stx_4181_, v___x_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; 
lean_dec(v_stx_4181_);
v___x_4224_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4224_;
}
else
{
lean_object* v___x_4225_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; uint8_t v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; uint8_t v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; uint8_t v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; uint8_t v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v_tk_4352_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v_args_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___x_4412_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v_only_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v_unfold_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v_squeeze_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4225_ = lean_unsigned_to_nat(0u);
v_tk_4352_ = l_Lean_Syntax_getArg(v_stx_4181_, v___x_4225_);
v___x_4412_ = lean_unsigned_to_nat(1u);
v___x_4488_ = l_Lean_Syntax_getArg(v_stx_4181_, v___x_4412_);
v___x_4489_ = l_Lean_Syntax_isNone(v___x_4488_);
if (v___x_4489_ == 0)
{
uint8_t v___x_4490_; 
lean_inc(v___x_4488_);
v___x_4490_ = l_Lean_Syntax_matchesNull(v___x_4488_, v___x_4412_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
lean_dec(v___x_4488_);
lean_dec(v_tk_4352_);
lean_dec(v_stx_4181_);
v___x_4491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4491_;
}
else
{
lean_object* v_squeeze_4492_; lean_object* v___x_4493_; 
v_squeeze_4492_ = l_Lean_Syntax_getArg(v___x_4488_, v___x_4225_);
lean_dec(v___x_4488_);
v___x_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4493_, 0, v_squeeze_4492_);
v_squeeze_4471_ = v___x_4493_;
v___y_4472_ = v_a_4182_;
v___y_4473_ = v_a_4183_;
v___y_4474_ = v_a_4184_;
v___y_4475_ = v_a_4185_;
v___y_4476_ = v_a_4186_;
v___y_4477_ = v_a_4187_;
v___y_4478_ = v_a_4188_;
v___y_4479_ = v_a_4189_;
goto v___jp_4470_;
}
}
else
{
lean_object* v___x_4494_; 
lean_dec(v___x_4488_);
v___x_4494_ = lean_box(0);
v_squeeze_4471_ = v___x_4494_;
v___y_4472_ = v_a_4182_;
v___y_4473_ = v_a_4183_;
v___y_4474_ = v_a_4184_;
v___y_4475_ = v_a_4185_;
v___y_4476_ = v_a_4186_;
v___y_4477_ = v_a_4187_;
v___y_4478_ = v_a_4188_;
v___y_4479_ = v_a_4189_;
goto v___jp_4470_;
}
v___jp_4226_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
lean_inc_ref(v___y_4246_);
v___x_4249_ = l_Array_append___redArg(v___y_4246_, v___y_4248_);
lean_dec_ref(v___y_4248_);
lean_inc(v___y_4237_);
lean_inc(v___y_4234_);
v___x_4250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4250_, 0, v___y_4234_);
lean_ctor_set(v___x_4250_, 1, v___y_4237_);
lean_ctor_set(v___x_4250_, 2, v___x_4249_);
if (lean_obj_tag(v___y_4230_) == 1)
{
lean_object* v_val_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_val_4251_ = lean_ctor_get(v___y_4230_, 0);
lean_inc(v_val_4251_);
lean_dec_ref_known(v___y_4230_, 1);
v___x_4252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4));
lean_inc_n(v___y_4234_, 4);
v___x_4254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___y_4234_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
lean_inc_ref(v___y_4246_);
v___x_4255_ = l_Array_append___redArg(v___y_4246_, v_val_4251_);
lean_dec(v_val_4251_);
lean_inc(v___y_4237_);
v___x_4256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4256_, 0, v___y_4234_);
lean_ctor_set(v___x_4256_, 1, v___y_4237_);
lean_ctor_set(v___x_4256_, 2, v___x_4255_);
v___x_4257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_4258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___y_4234_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = l_Lean_Syntax_node3(v___y_4234_, v___x_4252_, v___x_4254_, v___x_4256_, v___x_4258_);
v___x_4260_ = l_Array_mkArray1___redArg(v___x_4259_);
v___y_4192_ = v___y_4227_;
v___y_4193_ = v___y_4228_;
v___y_4194_ = v___y_4229_;
v___y_4195_ = v___y_4231_;
v___y_4196_ = v___y_4232_;
v___y_4197_ = v___y_4233_;
v___y_4198_ = v___y_4234_;
v___y_4199_ = v___x_4250_;
v___y_4200_ = v___y_4235_;
v___y_4201_ = v___y_4236_;
v___y_4202_ = v___y_4237_;
v___y_4203_ = v___y_4238_;
v___y_4204_ = v___y_4239_;
v___y_4205_ = v___y_4241_;
v___y_4206_ = v___y_4240_;
v___y_4207_ = v___y_4243_;
v___y_4208_ = v___y_4242_;
v___y_4209_ = v___y_4245_;
v___y_4210_ = v___y_4244_;
v___y_4211_ = v___y_4246_;
v___y_4212_ = v___y_4247_;
v___y_4213_ = v___x_4260_;
goto v___jp_4191_;
}
else
{
lean_object* v___x_4261_; 
lean_dec(v___y_4230_);
v___x_4261_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4192_ = v___y_4227_;
v___y_4193_ = v___y_4228_;
v___y_4194_ = v___y_4229_;
v___y_4195_ = v___y_4231_;
v___y_4196_ = v___y_4232_;
v___y_4197_ = v___y_4233_;
v___y_4198_ = v___y_4234_;
v___y_4199_ = v___x_4250_;
v___y_4200_ = v___y_4235_;
v___y_4201_ = v___y_4236_;
v___y_4202_ = v___y_4237_;
v___y_4203_ = v___y_4238_;
v___y_4204_ = v___y_4239_;
v___y_4205_ = v___y_4241_;
v___y_4206_ = v___y_4240_;
v___y_4207_ = v___y_4243_;
v___y_4208_ = v___y_4242_;
v___y_4209_ = v___y_4245_;
v___y_4210_ = v___y_4244_;
v___y_4211_ = v___y_4246_;
v___y_4212_ = v___y_4247_;
v___y_4213_ = v___x_4261_;
goto v___jp_4191_;
}
}
v___jp_4262_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
lean_inc_ref(v___y_4282_);
v___x_4285_ = l_Array_append___redArg(v___y_4282_, v___y_4284_);
lean_dec_ref(v___y_4284_);
lean_inc(v___y_4275_);
lean_inc(v___y_4271_);
v___x_4286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4286_, 0, v___y_4271_);
lean_ctor_set(v___x_4286_, 1, v___y_4275_);
lean_ctor_set(v___x_4286_, 2, v___x_4285_);
if (lean_obj_tag(v___y_4270_) == 1)
{
lean_object* v_val_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v_val_4287_ = lean_ctor_get(v___y_4270_, 0);
lean_inc(v_val_4287_);
lean_dec_ref_known(v___y_4270_, 1);
v___x_4288_ = l_Lean_SourceInfo_fromRef(v_val_4287_, v___x_4223_);
lean_dec(v_val_4287_);
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6));
v___x_4290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4288_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = l_Array_mkArray1___redArg(v___x_4290_);
v___y_4227_ = v___y_4263_;
v___y_4228_ = v___y_4264_;
v___y_4229_ = v___y_4265_;
v___y_4230_ = v___y_4266_;
v___y_4231_ = v___y_4267_;
v___y_4232_ = v___y_4268_;
v___y_4233_ = v___y_4269_;
v___y_4234_ = v___y_4271_;
v___y_4235_ = v___y_4272_;
v___y_4236_ = v___y_4273_;
v___y_4237_ = v___y_4275_;
v___y_4238_ = v___y_4274_;
v___y_4239_ = v___y_4276_;
v___y_4240_ = v___x_4286_;
v___y_4241_ = v___y_4277_;
v___y_4242_ = v___y_4279_;
v___y_4243_ = v___y_4278_;
v___y_4244_ = v___y_4281_;
v___y_4245_ = v___y_4280_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___x_4291_;
goto v___jp_4226_;
}
else
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4270_);
lean_dec(v___y_4270_);
v___y_4227_ = v___y_4263_;
v___y_4228_ = v___y_4264_;
v___y_4229_ = v___y_4265_;
v___y_4230_ = v___y_4266_;
v___y_4231_ = v___y_4267_;
v___y_4232_ = v___y_4268_;
v___y_4233_ = v___y_4269_;
v___y_4234_ = v___y_4271_;
v___y_4235_ = v___y_4272_;
v___y_4236_ = v___y_4273_;
v___y_4237_ = v___y_4275_;
v___y_4238_ = v___y_4274_;
v___y_4239_ = v___y_4276_;
v___y_4240_ = v___x_4286_;
v___y_4241_ = v___y_4277_;
v___y_4242_ = v___y_4279_;
v___y_4243_ = v___y_4278_;
v___y_4244_ = v___y_4281_;
v___y_4245_ = v___y_4280_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___x_4292_;
goto v___jp_4226_;
}
}
v___jp_4293_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
lean_inc_ref(v___y_4312_);
v___x_4315_ = l_Array_append___redArg(v___y_4312_, v___y_4314_);
lean_dec_ref(v___y_4314_);
lean_inc(v___y_4306_);
lean_inc(v___y_4302_);
v___x_4316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4316_, 0, v___y_4302_);
lean_ctor_set(v___x_4316_, 1, v___y_4306_);
lean_ctor_set(v___x_4316_, 2, v___x_4315_);
v___x_4317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4309_) == 0)
{
lean_object* v___x_4318_; 
v___x_4318_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4263_ = v___y_4294_;
v___y_4264_ = v___y_4295_;
v___y_4265_ = v___y_4296_;
v___y_4266_ = v___y_4297_;
v___y_4267_ = v___y_4298_;
v___y_4268_ = v___y_4299_;
v___y_4269_ = v___y_4300_;
v___y_4270_ = v___y_4301_;
v___y_4271_ = v___y_4302_;
v___y_4272_ = v___y_4304_;
v___y_4273_ = v___y_4303_;
v___y_4274_ = v___y_4305_;
v___y_4275_ = v___y_4306_;
v___y_4276_ = v___y_4307_;
v___y_4277_ = v___y_4308_;
v___y_4278_ = v___x_4317_;
v___y_4279_ = v___x_4316_;
v___y_4280_ = v___y_4311_;
v___y_4281_ = v___y_4310_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___y_4313_;
v___y_4284_ = v___x_4318_;
goto v___jp_4262_;
}
else
{
lean_object* v_val_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v_val_4319_ = lean_ctor_get(v___y_4309_, 0);
lean_inc(v_val_4319_);
lean_dec_ref_known(v___y_4309_, 1);
v___x_4320_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4321_ = lean_array_push(v___x_4320_, v_val_4319_);
v___y_4263_ = v___y_4294_;
v___y_4264_ = v___y_4295_;
v___y_4265_ = v___y_4296_;
v___y_4266_ = v___y_4297_;
v___y_4267_ = v___y_4298_;
v___y_4268_ = v___y_4299_;
v___y_4269_ = v___y_4300_;
v___y_4270_ = v___y_4301_;
v___y_4271_ = v___y_4302_;
v___y_4272_ = v___y_4304_;
v___y_4273_ = v___y_4303_;
v___y_4274_ = v___y_4305_;
v___y_4275_ = v___y_4306_;
v___y_4276_ = v___y_4307_;
v___y_4277_ = v___y_4308_;
v___y_4278_ = v___x_4317_;
v___y_4279_ = v___x_4316_;
v___y_4280_ = v___y_4311_;
v___y_4281_ = v___y_4310_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___y_4313_;
v___y_4284_ = v___x_4321_;
goto v___jp_4262_;
}
}
v___jp_4322_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_inc_ref(v___y_4341_);
v___x_4344_ = l_Array_append___redArg(v___y_4341_, v___y_4343_);
lean_dec_ref(v___y_4343_);
lean_inc(v___y_4335_);
lean_inc(v___y_4331_);
v___x_4345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4345_, 0, v___y_4331_);
lean_ctor_set(v___x_4345_, 1, v___y_4335_);
lean_ctor_set(v___x_4345_, 2, v___x_4344_);
if (lean_obj_tag(v___y_4332_) == 1)
{
lean_object* v_val_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_val_4346_ = lean_ctor_get(v___y_4332_, 0);
lean_inc(v_val_4346_);
lean_dec_ref_known(v___y_4332_, 1);
v___x_4347_ = l_Lean_SourceInfo_fromRef(v_val_4346_, v___x_4223_);
lean_dec(v_val_4346_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_4349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4347_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = l_Array_mkArray1___redArg(v___x_4349_);
v___y_4294_ = v___y_4323_;
v___y_4295_ = v___y_4324_;
v___y_4296_ = v___y_4325_;
v___y_4297_ = v___y_4326_;
v___y_4298_ = v___y_4327_;
v___y_4299_ = v___y_4328_;
v___y_4300_ = v___y_4329_;
v___y_4301_ = v___y_4330_;
v___y_4302_ = v___y_4331_;
v___y_4303_ = v___x_4345_;
v___y_4304_ = v___y_4333_;
v___y_4305_ = v___y_4334_;
v___y_4306_ = v___y_4335_;
v___y_4307_ = v___y_4336_;
v___y_4308_ = v___y_4337_;
v___y_4309_ = v___y_4338_;
v___y_4310_ = v___y_4340_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___y_4341_;
v___y_4313_ = v___y_4342_;
v___y_4314_ = v___x_4350_;
goto v___jp_4293_;
}
else
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4332_);
lean_dec(v___y_4332_);
v___y_4294_ = v___y_4323_;
v___y_4295_ = v___y_4324_;
v___y_4296_ = v___y_4325_;
v___y_4297_ = v___y_4326_;
v___y_4298_ = v___y_4327_;
v___y_4299_ = v___y_4328_;
v___y_4300_ = v___y_4329_;
v___y_4301_ = v___y_4330_;
v___y_4302_ = v___y_4331_;
v___y_4303_ = v___x_4345_;
v___y_4304_ = v___y_4333_;
v___y_4305_ = v___y_4334_;
v___y_4306_ = v___y_4335_;
v___y_4307_ = v___y_4336_;
v___y_4308_ = v___y_4337_;
v___y_4309_ = v___y_4338_;
v___y_4310_ = v___y_4340_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___y_4341_;
v___y_4313_ = v___y_4342_;
v___y_4314_ = v___x_4351_;
goto v___jp_4293_;
}
}
v___jp_4353_:
{
lean_object* v_ref_4369_; uint8_t v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_ref_4369_ = lean_ctor_get(v___y_4355_, 2);
v___x_4370_ = 0;
v___x_4371_ = l_Lean_SourceInfo_fromRef(v_ref_4369_, v___x_4370_);
v___x_4372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4374_ = l_Lean_SourceInfo_fromRef(v_tk_4352_, v___x_4223_);
lean_dec(v_tk_4352_);
v___x_4375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
lean_ctor_set(v___x_4375_, 1, v___x_4372_);
v___x_4376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4377_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3);
if (lean_obj_tag(v___y_4366_) == 1)
{
lean_object* v_val_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_val_4378_ = lean_ctor_get(v___y_4366_, 0);
lean_inc(v_val_4378_);
lean_dec_ref_known(v___y_4366_, 1);
v___x_4379_ = l_Lean_SourceInfo_fromRef(v_val_4378_, v___x_4223_);
lean_dec(v_val_4378_);
v___x_4380_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = l_Array_mkArray1___redArg(v___x_4381_);
v___y_4323_ = v___y_4354_;
v___y_4324_ = v___x_4375_;
v___y_4325_ = v___x_4373_;
v___y_4326_ = v___y_4356_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4357_;
v___y_4329_ = v___y_4358_;
v___y_4330_ = v___y_4359_;
v___y_4331_ = v___x_4371_;
v___y_4332_ = v___y_4360_;
v___y_4333_ = v___y_4361_;
v___y_4334_ = v___x_4370_;
v___y_4335_ = v___x_4376_;
v___y_4336_ = v___y_4362_;
v___y_4337_ = v___y_4363_;
v___y_4338_ = v___y_4368_;
v___y_4339_ = v___y_4364_;
v___y_4340_ = v___y_4365_;
v___y_4341_ = v___x_4377_;
v___y_4342_ = v___y_4367_;
v___y_4343_ = v___x_4382_;
goto v___jp_4322_;
}
else
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4366_);
lean_dec(v___y_4366_);
v___y_4323_ = v___y_4354_;
v___y_4324_ = v___x_4375_;
v___y_4325_ = v___x_4373_;
v___y_4326_ = v___y_4356_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4357_;
v___y_4329_ = v___y_4358_;
v___y_4330_ = v___y_4359_;
v___y_4331_ = v___x_4371_;
v___y_4332_ = v___y_4360_;
v___y_4333_ = v___y_4361_;
v___y_4334_ = v___x_4370_;
v___y_4335_ = v___x_4376_;
v___y_4336_ = v___y_4362_;
v___y_4337_ = v___y_4363_;
v___y_4338_ = v___y_4368_;
v___y_4339_ = v___y_4364_;
v___y_4340_ = v___y_4365_;
v___y_4341_ = v___x_4377_;
v___y_4342_ = v___y_4367_;
v___y_4343_ = v___x_4383_;
goto v___jp_4322_;
}
}
v___jp_4384_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4400_ = lean_unsigned_to_nat(5u);
v___x_4401_ = l_Lean_Syntax_getArg(v___y_4386_, v___x_4400_);
lean_dec(v___y_4386_);
v___x_4402_ = l_Lean_Syntax_getOptional_x3f(v___y_4385_);
lean_dec(v___y_4385_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v___x_4403_; 
v___x_4403_ = lean_box(0);
v___y_4354_ = v___y_4392_;
v___y_4355_ = v___y_4398_;
v___y_4356_ = v_args_4391_;
v___y_4357_ = v___y_4397_;
v___y_4358_ = v___y_4395_;
v___y_4359_ = v___y_4387_;
v___y_4360_ = v___y_4388_;
v___y_4361_ = v___y_4394_;
v___y_4362_ = v___y_4399_;
v___y_4363_ = v___y_4393_;
v___y_4364_ = v___y_4396_;
v___y_4365_ = v___y_4389_;
v___y_4366_ = v___y_4390_;
v___y_4367_ = v___x_4401_;
v___y_4368_ = v___x_4403_;
goto v___jp_4353_;
}
else
{
lean_object* v_val_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
v_val_4404_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4402_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_val_4404_);
lean_dec(v___x_4402_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_val_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
v___y_4354_ = v___y_4392_;
v___y_4355_ = v___y_4398_;
v___y_4356_ = v_args_4391_;
v___y_4357_ = v___y_4397_;
v___y_4358_ = v___y_4395_;
v___y_4359_ = v___y_4387_;
v___y_4360_ = v___y_4388_;
v___y_4361_ = v___y_4394_;
v___y_4362_ = v___y_4399_;
v___y_4363_ = v___y_4393_;
v___y_4364_ = v___y_4396_;
v___y_4365_ = v___y_4389_;
v___y_4366_ = v___y_4390_;
v___y_4367_ = v___x_4401_;
v___y_4368_ = v___x_4409_;
goto v___jp_4353_;
}
}
}
}
v___jp_4413_:
{
lean_object* v___x_4429_; uint8_t v___x_4430_; 
v___x_4429_ = l_Lean_Syntax_getArg(v___y_4415_, v___y_4419_);
v___x_4430_ = l_Lean_Syntax_isNone(v___x_4429_);
if (v___x_4430_ == 0)
{
uint8_t v___x_4431_; 
lean_inc(v___x_4429_);
v___x_4431_ = l_Lean_Syntax_matchesNull(v___x_4429_, v___x_4412_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; 
lean_dec(v___x_4429_);
lean_dec(v_only_4420_);
lean_dec(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec(v_tk_4352_);
v___x_4432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4432_;
}
else
{
lean_object* v___x_4433_; lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4433_ = l_Lean_Syntax_getArg(v___x_4429_, v___x_4225_);
lean_dec(v___x_4429_);
v___x_4434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4433_);
v___x_4435_ = l_Lean_Syntax_isOfKind(v___x_4433_, v___x_4434_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; 
lean_dec(v___x_4433_);
lean_dec(v_only_4420_);
lean_dec(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec(v_tk_4352_);
v___x_4436_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4436_;
}
else
{
lean_object* v___x_4437_; lean_object* v_args_4438_; lean_object* v___x_4439_; 
v___x_4437_ = l_Lean_Syntax_getArg(v___x_4433_, v___x_4412_);
lean_dec(v___x_4433_);
v_args_4438_ = l_Lean_Syntax_getArgs(v___x_4437_);
lean_dec(v___x_4437_);
v___x_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4439_, 0, v_args_4438_);
v___y_4385_ = v___y_4414_;
v___y_4386_ = v___y_4415_;
v___y_4387_ = v_only_4420_;
v___y_4388_ = v___y_4416_;
v___y_4389_ = v___y_4417_;
v___y_4390_ = v___y_4418_;
v_args_4391_ = v___x_4439_;
v___y_4392_ = v___y_4421_;
v___y_4393_ = v___y_4422_;
v___y_4394_ = v___y_4423_;
v___y_4395_ = v___y_4424_;
v___y_4396_ = v___y_4425_;
v___y_4397_ = v___y_4426_;
v___y_4398_ = v___y_4427_;
v___y_4399_ = v___y_4428_;
goto v___jp_4384_;
}
}
}
else
{
lean_object* v___x_4440_; 
lean_dec(v___x_4429_);
v___x_4440_ = lean_box(0);
v___y_4385_ = v___y_4414_;
v___y_4386_ = v___y_4415_;
v___y_4387_ = v_only_4420_;
v___y_4388_ = v___y_4416_;
v___y_4389_ = v___y_4417_;
v___y_4390_ = v___y_4418_;
v_args_4391_ = v___x_4440_;
v___y_4392_ = v___y_4421_;
v___y_4393_ = v___y_4422_;
v___y_4394_ = v___y_4423_;
v___y_4395_ = v___y_4424_;
v___y_4396_ = v___y_4425_;
v___y_4397_ = v___y_4426_;
v___y_4398_ = v___y_4427_;
v___y_4399_ = v___y_4428_;
goto v___jp_4384_;
}
}
v___jp_4441_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; uint8_t v___x_4456_; 
v___x_4453_ = lean_unsigned_to_nat(3u);
v___x_4454_ = l_Lean_Syntax_getArg(v_stx_4181_, v___x_4453_);
lean_dec(v_stx_4181_);
v___x_4455_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4454_);
v___x_4456_ = l_Lean_Syntax_isOfKind(v___x_4454_, v___x_4455_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; 
lean_dec(v___x_4454_);
lean_dec(v_unfold_4444_);
lean_dec(v___y_4443_);
lean_dec(v_tk_4352_);
v___x_4457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4457_;
}
else
{
lean_object* v___x_4458_; lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4458_ = l_Lean_Syntax_getArg(v___x_4454_, v___x_4225_);
v___x_4459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4458_);
v___x_4460_ = l_Lean_Syntax_isOfKind(v___x_4458_, v___x_4459_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; 
lean_dec(v___x_4458_);
lean_dec(v___x_4454_);
lean_dec(v_unfold_4444_);
lean_dec(v___y_4443_);
lean_dec(v_tk_4352_);
v___x_4461_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4461_;
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4462_ = l_Lean_Syntax_getArg(v___x_4454_, v___x_4412_);
v___x_4463_ = l_Lean_Syntax_getArg(v___x_4454_, v___y_4442_);
v___x_4464_ = l_Lean_Syntax_isNone(v___x_4463_);
if (v___x_4464_ == 0)
{
uint8_t v___x_4465_; 
lean_inc(v___x_4463_);
v___x_4465_ = l_Lean_Syntax_matchesNull(v___x_4463_, v___x_4412_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; 
lean_dec(v___x_4463_);
lean_dec(v___x_4462_);
lean_dec(v___x_4458_);
lean_dec(v___x_4454_);
lean_dec(v_unfold_4444_);
lean_dec(v___y_4443_);
lean_dec(v_tk_4352_);
v___x_4466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4466_;
}
else
{
lean_object* v_only_4467_; lean_object* v___x_4468_; 
v_only_4467_ = l_Lean_Syntax_getArg(v___x_4463_, v___x_4225_);
lean_dec(v___x_4463_);
v___x_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4468_, 0, v_only_4467_);
v___y_4414_ = v___x_4462_;
v___y_4415_ = v___x_4454_;
v___y_4416_ = v_unfold_4444_;
v___y_4417_ = v___x_4458_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v___x_4453_;
v_only_4420_ = v___x_4468_;
v___y_4421_ = v___y_4445_;
v___y_4422_ = v___y_4446_;
v___y_4423_ = v___y_4447_;
v___y_4424_ = v___y_4448_;
v___y_4425_ = v___y_4449_;
v___y_4426_ = v___y_4450_;
v___y_4427_ = v___y_4451_;
v___y_4428_ = v___y_4452_;
goto v___jp_4413_;
}
}
else
{
lean_object* v___x_4469_; 
lean_dec(v___x_4463_);
v___x_4469_ = lean_box(0);
v___y_4414_ = v___x_4462_;
v___y_4415_ = v___x_4454_;
v___y_4416_ = v_unfold_4444_;
v___y_4417_ = v___x_4458_;
v___y_4418_ = v___y_4443_;
v___y_4419_ = v___x_4453_;
v_only_4420_ = v___x_4469_;
v___y_4421_ = v___y_4445_;
v___y_4422_ = v___y_4446_;
v___y_4423_ = v___y_4447_;
v___y_4424_ = v___y_4448_;
v___y_4425_ = v___y_4449_;
v___y_4426_ = v___y_4450_;
v___y_4427_ = v___y_4451_;
v___y_4428_ = v___y_4452_;
goto v___jp_4413_;
}
}
}
}
v___jp_4470_:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; 
v___x_4480_ = lean_unsigned_to_nat(2u);
v___x_4481_ = l_Lean_Syntax_getArg(v_stx_4181_, v___x_4480_);
v___x_4482_ = l_Lean_Syntax_isNone(v___x_4481_);
if (v___x_4482_ == 0)
{
uint8_t v___x_4483_; 
lean_inc(v___x_4481_);
v___x_4483_ = l_Lean_Syntax_matchesNull(v___x_4481_, v___x_4412_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; 
lean_dec(v___x_4481_);
lean_dec(v_squeeze_4471_);
lean_dec(v_tk_4352_);
lean_dec(v_stx_4181_);
v___x_4484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4484_;
}
else
{
lean_object* v_unfold_4485_; lean_object* v___x_4486_; 
v_unfold_4485_ = l_Lean_Syntax_getArg(v___x_4481_, v___x_4225_);
lean_dec(v___x_4481_);
v___x_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4486_, 0, v_unfold_4485_);
v___y_4442_ = v___x_4480_;
v___y_4443_ = v_squeeze_4471_;
v_unfold_4444_ = v___x_4486_;
v___y_4445_ = v___y_4472_;
v___y_4446_ = v___y_4473_;
v___y_4447_ = v___y_4474_;
v___y_4448_ = v___y_4475_;
v___y_4449_ = v___y_4476_;
v___y_4450_ = v___y_4477_;
v___y_4451_ = v___y_4478_;
v___y_4452_ = v___y_4479_;
goto v___jp_4441_;
}
}
else
{
lean_object* v___x_4487_; 
lean_dec(v___x_4481_);
v___x_4487_ = lean_box(0);
v___y_4442_ = v___x_4480_;
v___y_4443_ = v_squeeze_4471_;
v_unfold_4444_ = v___x_4487_;
v___y_4445_ = v___y_4472_;
v___y_4446_ = v___y_4473_;
v___y_4447_ = v___y_4474_;
v___y_4448_ = v___y_4475_;
v___y_4449_ = v___y_4476_;
v___y_4450_ = v___y_4477_;
v___y_4451_ = v___y_4478_;
v___y_4452_ = v___y_4479_;
goto v___jp_4441_;
}
}
}
v___jp_4191_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
lean_inc_ref(v___y_4211_);
v___x_4214_ = l_Array_append___redArg(v___y_4211_, v___y_4213_);
lean_dec_ref(v___y_4213_);
lean_inc_n(v___y_4202_, 2);
lean_inc_n(v___y_4198_, 4);
v___x_4215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4215_, 0, v___y_4198_);
lean_ctor_set(v___x_4215_, 1, v___y_4202_);
lean_ctor_set(v___x_4215_, 2, v___x_4214_);
v___x_4216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___y_4198_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = l_Lean_Syntax_node2(v___y_4198_, v___y_4202_, v___x_4217_, v___y_4212_);
lean_inc(v___y_4207_);
v___x_4219_ = l_Lean_Syntax_node5(v___y_4198_, v___y_4207_, v___y_4210_, v___y_4206_, v___y_4199_, v___x_4215_, v___x_4218_);
lean_inc(v___y_4194_);
v___x_4220_ = l_Lean_Syntax_node4(v___y_4198_, v___y_4194_, v___y_4193_, v___y_4201_, v___y_4208_, v___x_4219_);
v___x_4221_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4203_, v___x_4220_, v___y_4192_, v___y_4205_, v___y_4200_, v___y_4197_, v___y_4209_, v___y_4196_, v___y_4195_, v___y_4204_);
return v___x_4221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec(v_a_4499_);
lean_dec_ref(v_a_4498_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4514_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4515_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4517_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4518_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4514_, v___x_4515_, v___x_4516_, v___x_4517_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4520_;
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
res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_();
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
