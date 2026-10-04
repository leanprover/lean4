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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_85_, uint8_t v___y_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 1)
{
lean_object* v_pre_88_; 
v_pre_88_ = lean_ctor_get(v_x_87_, 0);
switch(lean_obj_tag(v_pre_88_))
{
case 1:
{
lean_object* v_pre_89_; 
v_pre_89_ = lean_ctor_get(v_pre_88_, 0);
switch(lean_obj_tag(v_pre_89_))
{
case 0:
{
lean_object* v_str_90_; lean_object* v_str_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v_str_90_ = lean_ctor_get(v_x_87_, 1);
v_str_91_ = lean_ctor_get(v_pre_88_, 1);
v___x_92_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_93_ = lean_string_dec_eq(v_str_91_, v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_95_ = lean_string_dec_eq(v_str_91_, v___x_94_);
if (v___x_95_ == 0)
{
return v___x_95_;
}
else
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_97_ = lean_string_dec_eq(v_str_90_, v___x_96_);
if (v___x_97_ == 0)
{
return v___x_97_;
}
else
{
return v_suppressElabErrors_85_;
}
}
}
else
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_99_ = lean_string_dec_eq(v_str_90_, v___x_98_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
return v_suppressElabErrors_85_;
}
}
}
case 1:
{
lean_object* v_pre_100_; 
v_pre_100_ = lean_ctor_get(v_pre_89_, 0);
if (lean_obj_tag(v_pre_100_) == 0)
{
lean_object* v_str_101_; lean_object* v_str_102_; lean_object* v_str_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_str_101_ = lean_ctor_get(v_x_87_, 1);
v_str_102_ = lean_ctor_get(v_pre_88_, 1);
v_str_103_ = lean_ctor_get(v_pre_89_, 1);
v___x_104_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_105_ = lean_string_dec_eq(v_str_103_, v___x_104_);
if (v___x_105_ == 0)
{
return v___x_105_;
}
else
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_107_ = lean_string_dec_eq(v_str_102_, v___x_106_);
if (v___x_107_ == 0)
{
return v___x_107_;
}
else
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_109_ = lean_string_dec_eq(v_str_101_, v___x_108_);
if (v___x_109_ == 0)
{
return v___x_109_;
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
return v___y_86_;
}
}
default: 
{
return v___y_86_;
}
}
}
case 0:
{
lean_object* v_str_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_str_110_ = lean_ctor_get(v_x_87_, 1);
v___x_111_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_112_ = lean_string_dec_eq(v_str_110_, v___x_111_);
if (v___x_112_ == 0)
{
return v___x_112_;
}
else
{
return v_suppressElabErrors_85_;
}
}
default: 
{
return v___y_86_;
}
}
}
else
{
return v___y_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_113_, lean_object* v___y_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_suppressElabErrors_boxed_116_; uint8_t v___y_4868__boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_suppressElabErrors_boxed_116_ = lean_unbox(v_suppressElabErrors_113_);
v___y_4868__boxed_117_ = lean_unbox(v___y_114_);
v_res_118_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_116_, v___y_4868__boxed_117_, v_x_115_);
lean_dec(v_x_115_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; lean_object* v_env_127_; uint8_t v___x_128_; lean_object* v_env_129_; lean_object* v___x_130_; lean_object* v_toCold_131_; lean_object* v_mctx_132_; lean_object* v_lctx_133_; lean_object* v_options_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_126_ = lean_st_ref_get(v___y_124_);
v_env_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_env_127_);
lean_dec(v___x_126_);
v___x_128_ = 0;
v_env_129_ = l_Lean_Environment_setRecordingDeps(v_env_127_, v___x_128_);
v___x_130_ = lean_st_ref_get(v___y_122_);
v_toCold_131_ = lean_ctor_get(v___y_123_, 0);
v_mctx_132_ = lean_ctor_get(v___x_130_, 0);
lean_inc_ref(v_mctx_132_);
lean_dec(v___x_130_);
v_lctx_133_ = lean_ctor_get(v___y_121_, 2);
v_options_134_ = lean_ctor_get(v_toCold_131_, 2);
lean_inc_ref(v_options_134_);
lean_inc_ref(v_lctx_133_);
v___x_135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_135_, 0, v_env_129_);
lean_ctor_set(v___x_135_, 1, v_mctx_132_);
lean_ctor_set(v___x_135_, 2, v_lctx_133_);
lean_ctor_set(v___x_135_, 3, v_options_134_);
v___x_136_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v_msgData_120_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msgData_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_146_, lean_object* v_msgData_147_, uint8_t v_severity_148_, uint8_t v_isSilent_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
uint8_t v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; uint8_t v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v_toCold_163_; lean_object* v___y_164_; lean_object* v___y_193_; lean_object* v___y_194_; uint8_t v___y_195_; uint8_t v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; uint8_t v___y_199_; lean_object* v___y_200_; lean_object* v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; uint8_t v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; uint8_t v___y_230_; uint8_t v___y_231_; uint8_t v___y_232_; uint8_t v___x_243_; uint8_t v___y_245_; uint8_t v___y_246_; uint8_t v___y_247_; uint8_t v___y_249_; uint8_t v___x_257_; 
v___x_243_ = 2;
v___x_257_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_243_);
if (v___x_257_ == 0)
{
v___y_249_ = v___x_257_;
goto v___jp_248_;
}
else
{
uint8_t v___x_258_; 
lean_inc_ref(v_msgData_147_);
v___x_258_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_147_);
v___y_249_ = v___x_258_;
goto v___jp_248_;
}
v___jp_155_:
{
lean_object* v_currNamespace_165_; lean_object* v_openDecls_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_env_171_; lean_object* v_nextMacroScope_172_; lean_object* v_ngen_173_; lean_object* v_auxDeclNGen_174_; lean_object* v_traceState_175_; lean_object* v_cache_176_; lean_object* v_recordedDeps_177_; lean_object* v_messages_178_; lean_object* v_infoState_179_; lean_object* v_snapshotTasks_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_191_; 
v_currNamespace_165_ = lean_ctor_get(v_toCold_163_, 4);
v_openDecls_166_ = lean_ctor_get(v_toCold_163_, 5);
lean_inc(v_openDecls_166_);
lean_inc(v_currNamespace_165_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v_currNamespace_165_);
lean_ctor_set(v___x_167_, 1, v_openDecls_166_);
v___x_168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___y_159_);
lean_inc_ref(v___y_158_);
lean_inc_ref(v___y_161_);
v___x_169_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_169_, 0, v___y_161_);
lean_ctor_set(v___x_169_, 1, v___y_162_);
lean_ctor_set(v___x_169_, 2, v___y_157_);
lean_ctor_set(v___x_169_, 3, v___y_158_);
lean_ctor_set(v___x_169_, 4, v___x_168_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5, v___y_160_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5 + 1, v___y_156_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5 + 2, v_isSilent_149_);
v___x_170_ = lean_st_ref_take(v___y_164_);
v_env_171_ = lean_ctor_get(v___x_170_, 0);
v_nextMacroScope_172_ = lean_ctor_get(v___x_170_, 1);
v_ngen_173_ = lean_ctor_get(v___x_170_, 2);
v_auxDeclNGen_174_ = lean_ctor_get(v___x_170_, 3);
v_traceState_175_ = lean_ctor_get(v___x_170_, 4);
v_cache_176_ = lean_ctor_get(v___x_170_, 5);
v_recordedDeps_177_ = lean_ctor_get(v___x_170_, 6);
v_messages_178_ = lean_ctor_get(v___x_170_, 7);
v_infoState_179_ = lean_ctor_get(v___x_170_, 8);
v_snapshotTasks_180_ = lean_ctor_get(v___x_170_, 9);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_191_ == 0)
{
v___x_182_ = v___x_170_;
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_snapshotTasks_180_);
lean_inc(v_infoState_179_);
lean_inc(v_messages_178_);
lean_inc(v_recordedDeps_177_);
lean_inc(v_cache_176_);
lean_inc(v_traceState_175_);
lean_inc(v_auxDeclNGen_174_);
lean_inc(v_ngen_173_);
lean_inc(v_nextMacroScope_172_);
lean_inc(v_env_171_);
lean_dec(v___x_170_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_box(0);
v___x_185_ = l_Lean_MessageLog_add(v___x_169_, v_messages_178_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 7, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_env_171_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_nextMacroScope_172_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_ngen_173_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_auxDeclNGen_174_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v_traceState_175_);
lean_ctor_set(v_reuseFailAlloc_190_, 5, v_cache_176_);
lean_ctor_set(v_reuseFailAlloc_190_, 6, v_recordedDeps_177_);
lean_ctor_set(v_reuseFailAlloc_190_, 7, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_190_, 8, v_infoState_179_);
lean_ctor_set(v_reuseFailAlloc_190_, 9, v_snapshotTasks_180_);
v___x_187_ = v_reuseFailAlloc_190_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_st_ref_put(v___y_164_, v___x_187_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_184_);
return v___x_189_;
}
}
}
v___jp_192_:
{
lean_object* v_fileName_201_; lean_object* v_fileMap_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_218_; 
v_fileName_201_ = lean_ctor_get(v___y_198_, 0);
v_fileMap_202_ = lean_ctor_get(v___y_198_, 1);
v___x_203_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_147_);
v___x_204_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v___x_203_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_218_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_218_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_218_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc_ref_n(v_fileMap_202_, 2);
v___x_209_ = l_Lean_FileMap_toPosition(v_fileMap_202_, v___y_197_);
lean_dec(v___y_197_);
v___x_210_ = l_Lean_FileMap_toPosition(v_fileMap_202_, v___y_200_);
lean_dec(v___y_200_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0));
if (v___y_196_ == 0)
{
lean_del_object(v___x_207_);
lean_dec_ref(v___y_193_);
v___y_156_ = v___y_195_;
v___y_157_ = v___x_211_;
v___y_158_ = v___x_212_;
v___y_159_ = v_a_205_;
v___y_160_ = v___y_199_;
v___y_161_ = v_fileName_201_;
v___y_162_ = v___x_209_;
v_toCold_163_ = v___y_194_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
else
{
uint8_t v___x_213_; 
lean_inc(v_a_205_);
v___x_213_ = l_Lean_MessageData_hasTag(v___y_193_, v_a_205_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec_ref_known(v___x_211_, 1);
lean_dec_ref(v___x_209_);
lean_dec(v_a_205_);
v___x_214_ = lean_box(0);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_214_);
v___x_216_ = v___x_207_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
else
{
lean_del_object(v___x_207_);
v___y_156_ = v___y_195_;
v___y_157_ = v___x_211_;
v___y_158_ = v___x_212_;
v___y_159_ = v_a_205_;
v___y_160_ = v___y_199_;
v___y_161_ = v_fileName_201_;
v___y_162_ = v___x_209_;
v_toCold_163_ = v___y_194_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
}
}
}
v___jp_219_:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Syntax_getTailPos_x3f(v___y_225_, v___y_224_);
lean_dec(v___y_225_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_inc(v___y_226_);
v___y_193_ = v___y_220_;
v___y_194_ = v___y_222_;
v___y_195_ = v___y_223_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_226_;
v___y_198_ = v___y_222_;
v___y_199_ = v___y_224_;
v___y_200_ = v___y_226_;
goto v___jp_192_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_227_, 1);
v___y_193_ = v___y_220_;
v___y_194_ = v___y_222_;
v___y_195_ = v___y_223_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_226_;
v___y_198_ = v___y_222_;
v___y_199_ = v___y_224_;
v___y_200_ = v_val_228_;
goto v___jp_192_;
}
}
v___jp_229_:
{
lean_object* v_toCold_233_; lean_object* v_ref_234_; uint8_t v_suppressElabErrors_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v_ref_239_; lean_object* v___x_240_; 
v_toCold_233_ = lean_ctor_get(v___y_152_, 0);
v_ref_234_ = lean_ctor_get(v___y_152_, 2);
v_suppressElabErrors_235_ = lean_ctor_get_uint8(v___y_152_, sizeof(void*)*3 + 2);
v___x_236_ = lean_box(v_suppressElabErrors_235_);
v___x_237_ = lean_box(v___y_230_);
v___f_238_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_238_, 0, v___x_236_);
lean_closure_set(v___f_238_, 1, v___x_237_);
v_ref_239_ = l_Lean_replaceRef(v_ref_146_, v_ref_234_);
v___x_240_ = l_Lean_Syntax_getPos_x3f(v_ref_239_, v___y_231_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
v___y_220_ = v___f_238_;
v___y_221_ = v_suppressElabErrors_235_;
v___y_222_ = v_toCold_233_;
v___y_223_ = v___y_232_;
v___y_224_ = v___y_231_;
v___y_225_ = v_ref_239_;
v___y_226_ = v___x_241_;
goto v___jp_219_;
}
else
{
lean_object* v_val_242_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v___x_240_, 1);
v___y_220_ = v___f_238_;
v___y_221_ = v_suppressElabErrors_235_;
v___y_222_ = v_toCold_233_;
v___y_223_ = v___y_232_;
v___y_224_ = v___y_231_;
v___y_225_ = v_ref_239_;
v___y_226_ = v_val_242_;
goto v___jp_219_;
}
}
v___jp_244_:
{
if (v___y_247_ == 0)
{
v___y_230_ = v___y_245_;
v___y_231_ = v___y_246_;
v___y_232_ = v_severity_148_;
goto v___jp_229_;
}
else
{
v___y_230_ = v___y_245_;
v___y_231_ = v___y_246_;
v___y_232_ = v___x_243_;
goto v___jp_229_;
}
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
uint8_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 1;
v___x_251_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_250_);
if (v___x_251_ == 0)
{
v___y_245_ = v___y_249_;
v___y_246_ = v___y_249_;
v___y_247_ = v___x_251_;
goto v___jp_244_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_152_);
v___x_253_ = l_Lean_warningAsError;
v___x_254_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_252_, v___x_253_);
lean_dec_ref(v___x_252_);
v___y_245_ = v___y_249_;
v___y_246_ = v___y_249_;
v___y_247_ = v___x_254_;
goto v___jp_244_;
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v_msgData_147_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_259_, lean_object* v_msgData_260_, lean_object* v_severity_261_, lean_object* v_isSilent_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v_severity_boxed_268_; uint8_t v_isSilent_boxed_269_; lean_object* v_res_270_; 
v_severity_boxed_268_ = lean_unbox(v_severity_261_);
v_isSilent_boxed_269_ = lean_unbox(v_isSilent_262_);
v_res_270_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_259_, v_msgData_260_, v_severity_boxed_268_, v_isSilent_boxed_269_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v_ref_259_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_271_, lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
uint8_t v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = 1;
v___x_283_ = 0;
v___x_284_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_271_, v_msgData_272_, v___x_282_, v___x_283_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_285_, lean_object* v_msgData_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_285_, v_msgData_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v_ref_285_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_303_, lean_object* v_stx_304_, lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_name_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_333_; 
v_name_315_ = lean_ctor_get(v_linterOption_303_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_linterOption_303_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_linterOption_303_, 1);
lean_dec(v_unused_334_);
v___x_317_ = v_linterOption_303_;
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_name_315_);
lean_dec(v_linterOption_303_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_319_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_315_);
v___x_320_ = l_Lean_MessageData_ofName(v_name_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 7);
lean_ctor_set(v___x_317_, 1, v___x_320_);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_322_ = v___x_317_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_332_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_disable_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_323_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v_disable_325_ = l_Lean_MessageData_note(v___x_324_);
v___x_326_ = l_Lean_Linter_linterMessageTag;
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v_msg_305_);
lean_ctor_set(v___x_327_, 1, v_disable_325_);
v___x_328_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_329_, 0, v_name_315_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
lean_inc(v_stx_304_);
v___x_330_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_330_, 0, v_stx_304_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_304_, v___x_330_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v_stx_304_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_335_, lean_object* v_stx_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_335_, v_stx_336_, v_msg_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_347_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v_msg_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_350_ = l_Lean_stringToMessageData(v___x_349_);
return v_msg_350_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_358_ = l_Lean_MessageData_ofFormat(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_359_, lean_object* v_ref_360_, lean_object* v_replacement_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_msg_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v_msg_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_msg_383_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_384_ = lean_box(0);
lean_inc(v_replacement_361_);
v___x_385_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_359_, v_replacement_361_, v___x_384_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; uint8_t v___x_387_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = lean_unbox(v_a_386_);
lean_dec(v_a_386_);
if (v___x_387_ == 0)
{
lean_dec(v_replacement_361_);
v_msg_372_ = v_msg_383_;
v___y_373_ = v_a_362_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
v___y_376_ = v_a_365_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
v___y_379_ = v_a_368_;
v___y_380_ = v_a_369_;
goto v___jp_371_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v_replacement_361_);
v___x_390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_384_);
lean_ctor_set(v___x_390_, 2, v___x_384_);
lean_ctor_set(v___x_390_, 3, v___x_384_);
lean_ctor_set(v___x_390_, 4, v___x_384_);
lean_ctor_set(v___x_390_, 5, v___x_384_);
lean_inc(v_ref_360_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v_ref_360_);
v___x_392_ = 4;
lean_inc_ref(v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_393_, 0, v___x_390_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_ctor_set(v___x_393_, 2, v___x_384_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*3, v___x_392_);
v___x_394_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_mk_empty_array_with_capacity(v___x_395_);
v___x_397_ = lean_array_push(v___x_396_, v___x_393_);
v___x_398_ = 0;
v___x_399_ = l_Lean_MessageData_hint(v___x_394_, v___x_397_, v___x_391_, v___x_384_, v___x_398_, v_a_368_, v_a_369_);
lean_dec_ref(v___x_397_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_401_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v_msg_383_);
lean_ctor_set(v___x_401_, 1, v_a_400_);
v_msg_372_ = v___x_401_;
v___y_373_ = v_a_362_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
v___y_376_ = v_a_365_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
v___y_379_ = v_a_368_;
v___y_380_ = v_a_369_;
goto v___jp_371_;
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_ref_360_);
v_a_402_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_399_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_399_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_replacement_361_);
lean_dec(v_ref_360_);
v_a_410_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_385_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_385_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
v___jp_371_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = l_Lean_linter_unnecessarySimpa;
v___x_382_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_381_, v_ref_360_, v_msg_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_418_, lean_object* v_ref_419_, lean_object* v_replacement_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_418_, v_ref_419_, v_replacement_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_431_, lean_object* v_msgData_432_, uint8_t v_severity_433_, uint8_t v_isSilent_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_431_, v_msgData_432_, v_severity_433_, v_isSilent_434_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_445_, lean_object* v_msgData_446_, lean_object* v_severity_447_, lean_object* v_isSilent_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v_severity_boxed_458_; uint8_t v_isSilent_boxed_459_; lean_object* v_res_460_; 
v_severity_boxed_458_ = lean_unbox(v_severity_447_);
v_isSilent_boxed_459_ = lean_unbox(v_isSilent_448_);
v_res_460_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_445_, v_msgData_446_, v_severity_boxed_458_, v_isSilent_boxed_459_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v_ref_445_);
return v_res_460_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_box(0);
v___x_462_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(lean_object* v_x_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
lean_inc(v___y_495_);
lean_inc_ref(v___y_494_);
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
v___x_501_ = lean_apply_9(v_x_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, lean_box(0));
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed(lean_object* v_x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(v_x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(lean_object* v_mvarId_513_, lean_object* v_x_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___f_524_; lean_object* v___x_525_; 
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_524_, 0, v_x_514_);
lean_closure_set(v___f_524_, 1, v___y_515_);
lean_closure_set(v___f_524_, 2, v___y_516_);
lean_closure_set(v___f_524_, 3, v___y_517_);
lean_closure_set(v___f_524_, 4, v___y_518_);
v___x_525_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_513_, v___f_524_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_525_) == 0)
{
return v___x_525_;
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___boxed(lean_object* v_mvarId_534_, lean_object* v_x_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_534_, v_x_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v_00_u03b1_546_, lean_object* v_mvarId_547_, lean_object* v_x_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_547_, v_x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v_00_u03b1_559_, lean_object* v_mvarId_560_, lean_object* v_x_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v_00_u03b1_559_, v_mvarId_560_, v_x_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_571_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(32u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_575_ = ((size_t)5ULL);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_unsigned_to_nat(32u);
v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
v___x_579_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_580_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_576_);
lean_ctor_set(v___x_580_, 3, v___x_576_);
lean_ctor_set_usize(v___x_580_, 4, v___x_575_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v_infoState_584_; lean_object* v_trees_585_; lean_object* v___x_586_; lean_object* v_infoState_587_; lean_object* v_env_588_; lean_object* v_nextMacroScope_589_; lean_object* v_ngen_590_; lean_object* v_auxDeclNGen_591_; lean_object* v_traceState_592_; lean_object* v_cache_593_; lean_object* v_recordedDeps_594_; lean_object* v_messages_595_; lean_object* v_snapshotTasks_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_617_; 
v___x_583_ = lean_st_ref_get(v___y_581_);
v_infoState_584_ = lean_ctor_get(v___x_583_, 8);
lean_inc_ref(v_infoState_584_);
lean_dec(v___x_583_);
v_trees_585_ = lean_ctor_get(v_infoState_584_, 2);
lean_inc_ref(v_trees_585_);
lean_dec_ref(v_infoState_584_);
v___x_586_ = lean_st_ref_take(v___y_581_);
v_infoState_587_ = lean_ctor_get(v___x_586_, 8);
v_env_588_ = lean_ctor_get(v___x_586_, 0);
v_nextMacroScope_589_ = lean_ctor_get(v___x_586_, 1);
v_ngen_590_ = lean_ctor_get(v___x_586_, 2);
v_auxDeclNGen_591_ = lean_ctor_get(v___x_586_, 3);
v_traceState_592_ = lean_ctor_get(v___x_586_, 4);
v_cache_593_ = lean_ctor_get(v___x_586_, 5);
v_recordedDeps_594_ = lean_ctor_get(v___x_586_, 6);
v_messages_595_ = lean_ctor_get(v___x_586_, 7);
v_snapshotTasks_596_ = lean_ctor_get(v___x_586_, 9);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_617_ == 0)
{
v___x_598_ = v___x_586_;
v_isShared_599_ = v_isSharedCheck_617_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snapshotTasks_596_);
lean_inc(v_infoState_587_);
lean_inc(v_messages_595_);
lean_inc(v_recordedDeps_594_);
lean_inc(v_cache_593_);
lean_inc(v_traceState_592_);
lean_inc(v_auxDeclNGen_591_);
lean_inc(v_ngen_590_);
lean_inc(v_nextMacroScope_589_);
lean_inc(v_env_588_);
lean_dec(v___x_586_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_617_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v_enabled_600_; lean_object* v_assignment_601_; lean_object* v_lazyAssignment_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_615_; 
v_enabled_600_ = lean_ctor_get_uint8(v_infoState_587_, sizeof(void*)*3);
v_assignment_601_ = lean_ctor_get(v_infoState_587_, 0);
v_lazyAssignment_602_ = lean_ctor_get(v_infoState_587_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v_infoState_587_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_infoState_587_, 2);
lean_dec(v_unused_616_);
v___x_604_ = v_infoState_587_;
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_lazyAssignment_602_);
lean_inc(v_assignment_601_);
lean_dec(v_infoState_587_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_615_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_assignment_601_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_lazyAssignment_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___x_606_);
lean_ctor_set_uint8(v_reuseFailAlloc_614_, sizeof(void*)*3, v_enabled_600_);
v___x_608_ = v_reuseFailAlloc_614_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 8, v___x_608_);
v___x_610_ = v___x_598_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_env_588_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_nextMacroScope_589_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_ngen_590_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v_auxDeclNGen_591_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_traceState_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 5, v_cache_593_);
lean_ctor_set(v_reuseFailAlloc_613_, 6, v_recordedDeps_594_);
lean_ctor_set(v_reuseFailAlloc_613_, 7, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 8, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_613_, 9, v_snapshotTasks_596_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_st_ref_put(v___y_581_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_trees_585_);
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_618_);
lean_dec(v___y_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___f_652_; lean_object* v___x_83969__overap_653_; lean_object* v___x_654_; 
v___f_652_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_83969__overap_653_ = lean_panic_fn_borrowed(v___f_652_, v_msg_642_);
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
v___x_654_ = lean_apply_9(v___x_83969__overap_653_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, lean_box(0));
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_ref_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_ref_675_ = lean_ctor_get(v___y_672_, 2);
v___x_676_ = 0;
v___x_677_ = l_Lean_SourceInfo_fromRef(v_ref_675_, v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_688_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Array_mkArray0___redArg();
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_args_707_, lean_object* v_only_708_, uint8_t v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___y_713_, lean_object* v_unfold_714_, uint8_t v___x_715_, lean_object* v_squeeze_716_, lean_object* v_loc_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; uint8_t v___y_790_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; uint8_t v___y_865_; 
if (lean_obj_tag(v_squeeze_716_) == 0)
{
uint8_t v___x_878_; 
v___x_878_ = 0;
v___y_865_ = v___x_878_;
goto v___jp_864_;
}
else
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_1014_; 
v_isSharedCheck_1014_ = !lean_is_exclusive(v_squeeze_716_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v_squeeze_716_, 0);
lean_dec(v_unused_1015_);
v___x_880_ = v_squeeze_716_;
v_isShared_881_ = v_isSharedCheck_1014_;
goto v_resetjp_879_;
}
else
{
lean_dec(v_squeeze_716_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_1014_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
if (v___x_715_ == 0)
{
lean_del_object(v___x_880_);
v___y_865_ = v___x_715_;
goto v___jp_864_;
}
else
{
if (lean_obj_tag(v_unfold_714_) == 0)
{
lean_object* v_ref_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_933_; 
v_ref_882_ = lean_ctor_get(v___y_724_, 2);
v___x_883_ = 0;
v___x_884_ = l_Lean_SourceInfo_fromRef(v_ref_882_, v___x_883_);
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9));
lean_inc_ref_n(v___x_712_, 2);
lean_inc_ref_n(v___x_711_, 2);
lean_inc_ref_n(v___x_710_, 2);
v___x_886_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_885_);
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10));
lean_inc_n(v___x_884_, 2);
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_884_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_890_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
v___x_891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_891_, 0, v___x_884_);
lean_ctor_set(v___x_891_, 1, v___x_889_);
lean_ctor_set(v___x_891_, 2, v___x_890_);
v___x_892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_893_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_892_);
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_933_ = v___x_942_;
goto v___jp_932_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_val_943_ = lean_ctor_get(v___y_713_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v___y_713_, 1);
v___x_944_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_945_ = lean_array_push(v___x_944_, v_val_943_);
v___y_933_ = v___x_945_;
goto v___jp_932_;
}
v___jp_894_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_899_ = l_Array_append___redArg(v___x_890_, v___y_898_);
lean_dec_ref(v___y_898_);
lean_inc_n(v___x_884_, 2);
v___x_900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_900_, 0, v___x_884_);
lean_ctor_set(v___x_900_, 1, v___x_889_);
lean_ctor_set(v___x_900_, 2, v___x_899_);
v___x_901_ = l_Lean_Syntax_node5(v___x_884_, v___x_893_, v___x_705_, v___y_895_, v___y_896_, v___y_897_, v___x_900_);
v___x_902_ = l_Lean_Syntax_node3(v___x_884_, v___x_886_, v___x_888_, v___x_891_, v___x_901_);
if (v_isShared_881_ == 0)
{
lean_ctor_set_tag(v___x_880_, 0);
lean_ctor_set(v___x_880_, 0, v___x_902_);
v___x_904_ = v___x_880_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
v___jp_906_:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = l_Array_append___redArg(v___x_890_, v___y_909_);
lean_dec_ref(v___y_909_);
lean_inc(v___x_884_);
v___x_911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_911_, 0, v___x_884_);
lean_ctor_set(v___x_911_, 1, v___x_889_);
lean_ctor_set(v___x_911_, 2, v___x_910_);
if (lean_obj_tag(v_loc_717_) == 1)
{
lean_object* v_val_912_; lean_object* v___x_913_; 
v_val_912_ = lean_ctor_get(v_loc_717_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v_loc_717_, 1);
v___x_913_ = l_Array_mkArray1___redArg(v_val_912_);
v___y_895_ = v___y_907_;
v___y_896_ = v___y_908_;
v___y_897_ = v___x_911_;
v___y_898_ = v___x_913_;
goto v___jp_894_;
}
else
{
lean_object* v___x_914_; 
lean_dec(v_loc_717_);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_895_ = v___y_907_;
v___y_896_ = v___y_908_;
v___y_897_ = v___x_911_;
v___y_898_ = v___x_914_;
goto v___jp_894_;
}
}
v___jp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = l_Array_append___redArg(v___x_890_, v___y_917_);
lean_dec_ref(v___y_917_);
lean_inc(v___x_884_);
v___x_919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_919_, 0, v___x_884_);
lean_ctor_set(v___x_919_, 1, v___x_889_);
lean_ctor_set(v___x_919_, 2, v___x_918_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_val_920_ = lean_ctor_get(v_args_707_, 0);
v___x_921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_922_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_921_);
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_884_, 4);
v___x_924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_884_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Array_append___redArg(v___x_890_, v_val_920_);
v___x_926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_926_, 0, v___x_884_);
lean_ctor_set(v___x_926_, 1, v___x_889_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_928_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_884_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_Syntax_node3(v___x_884_, v___x_922_, v___x_924_, v___x_926_, v___x_928_);
v___x_930_ = l_Array_mkArray1___redArg(v___x_929_);
v___y_907_ = v___y_916_;
v___y_908_ = v___x_919_;
v___y_909_ = v___x_930_;
goto v___jp_906_;
}
else
{
lean_object* v___x_931_; 
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_710_);
v___x_931_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_907_ = v___y_916_;
v___y_908_ = v___x_919_;
v___y_909_ = v___x_931_;
goto v___jp_906_;
}
}
v___jp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = l_Array_append___redArg(v___x_890_, v___y_933_);
lean_dec_ref(v___y_933_);
lean_inc(v___x_884_);
v___x_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_935_, 0, v___x_884_);
lean_ctor_set(v___x_935_, 1, v___x_889_);
lean_ctor_set(v___x_935_, 2, v___x_934_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_val_936_ = lean_ctor_get(v_only_708_, 0);
v___x_937_ = l_Lean_SourceInfo_fromRef(v_val_936_, v___x_709_);
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Array_mkArray1___redArg(v___x_939_);
v___y_916_ = v___x_935_;
v___y_917_ = v___x_940_;
goto v___jp_915_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_916_ = v___x_935_;
v___y_917_ = v___x_941_;
goto v___jp_915_;
}
}
}
else
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1012_; 
lean_del_object(v___x_880_);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_unfold_714_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_unfold_714_, 0);
lean_dec(v_unused_1013_);
v___x_947_ = v_unfold_714_;
v_isShared_948_ = v_isSharedCheck_1012_;
goto v_resetjp_946_;
}
else
{
lean_dec(v_unfold_714_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1012_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_ref_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_999_; 
v_ref_949_ = lean_ctor_get(v___y_724_, 2);
v___x_950_ = 0;
v___x_951_ = l_Lean_SourceInfo_fromRef(v_ref_949_, v___x_950_);
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13));
lean_inc_ref_n(v___x_712_, 2);
lean_inc_ref_n(v___x_711_, 2);
lean_inc_ref_n(v___x_710_, 2);
v___x_953_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14));
lean_inc(v___x_951_);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_951_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_957_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_956_);
v___x_958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_959_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_999_ = v___x_1008_;
goto v___jp_998_;
}
else
{
lean_object* v_val_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_val_1009_ = lean_ctor_get(v___y_713_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v___y_713_, 1);
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_1011_ = lean_array_push(v___x_1010_, v_val_1009_);
v___y_999_ = v___x_1011_;
goto v___jp_998_;
}
v___jp_960_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_965_ = l_Array_append___redArg(v___x_959_, v___y_964_);
lean_dec_ref(v___y_964_);
lean_inc_n(v___x_951_, 2);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_951_);
lean_ctor_set(v___x_966_, 1, v___x_958_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
v___x_967_ = l_Lean_Syntax_node5(v___x_951_, v___x_957_, v___x_705_, v___y_963_, v___y_961_, v___y_962_, v___x_966_);
v___x_968_ = l_Lean_Syntax_node2(v___x_951_, v___x_953_, v___x_955_, v___x_967_);
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 0);
lean_ctor_set(v___x_947_, 0, v___x_968_);
v___x_970_ = v___x_947_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
v___jp_972_:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = l_Array_append___redArg(v___x_959_, v___y_975_);
lean_dec_ref(v___y_975_);
lean_inc(v___x_951_);
v___x_977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_977_, 0, v___x_951_);
lean_ctor_set(v___x_977_, 1, v___x_958_);
lean_ctor_set(v___x_977_, 2, v___x_976_);
if (lean_obj_tag(v_loc_717_) == 1)
{
lean_object* v_val_978_; lean_object* v___x_979_; 
v_val_978_ = lean_ctor_get(v_loc_717_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v_loc_717_, 1);
v___x_979_ = l_Array_mkArray1___redArg(v_val_978_);
v___y_961_ = v___y_973_;
v___y_962_ = v___x_977_;
v___y_963_ = v___y_974_;
v___y_964_ = v___x_979_;
goto v___jp_960_;
}
else
{
lean_object* v___x_980_; 
lean_dec(v_loc_717_);
v___x_980_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_961_ = v___y_973_;
v___y_962_ = v___x_977_;
v___y_963_ = v___y_974_;
v___y_964_ = v___x_980_;
goto v___jp_960_;
}
}
v___jp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = l_Array_append___redArg(v___x_959_, v___y_983_);
lean_dec_ref(v___y_983_);
lean_inc(v___x_951_);
v___x_985_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_985_, 0, v___x_951_);
lean_ctor_set(v___x_985_, 1, v___x_958_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_val_986_ = lean_ctor_get(v_args_707_, 0);
v___x_987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_988_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_987_);
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_951_, 4);
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_951_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Array_append___redArg(v___x_959_, v_val_986_);
v___x_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_951_);
lean_ctor_set(v___x_992_, 1, v___x_958_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_951_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_Syntax_node3(v___x_951_, v___x_988_, v___x_990_, v___x_992_, v___x_994_);
v___x_996_ = l_Array_mkArray1___redArg(v___x_995_);
v___y_973_ = v___x_985_;
v___y_974_ = v___y_982_;
v___y_975_ = v___x_996_;
goto v___jp_972_;
}
else
{
lean_object* v___x_997_; 
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_710_);
v___x_997_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_973_ = v___x_985_;
v___y_974_ = v___y_982_;
v___y_975_ = v___x_997_;
goto v___jp_972_;
}
}
v___jp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = l_Array_append___redArg(v___x_959_, v___y_999_);
lean_dec_ref(v___y_999_);
lean_inc(v___x_951_);
v___x_1001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1001_, 0, v___x_951_);
lean_ctor_set(v___x_1001_, 1, v___x_958_);
lean_ctor_set(v___x_1001_, 2, v___x_1000_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_val_1002_ = lean_ctor_get(v_only_708_, 0);
v___x_1003_ = l_Lean_SourceInfo_fromRef(v_val_1002_, v___x_709_);
v___x_1004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Array_mkArray1___redArg(v___x_1005_);
v___y_982_ = v___x_1001_;
v___y_983_ = v___x_1006_;
goto v___jp_981_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_982_ = v___x_1001_;
v___y_983_ = v___x_1007_;
goto v___jp_981_;
}
}
}
}
}
}
}
v___jp_727_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_inc_ref(v___y_728_);
v___x_737_ = l_Array_append___redArg(v___y_728_, v___y_736_);
lean_dec_ref(v___y_736_);
lean_inc(v___y_732_);
lean_inc(v___y_733_);
v___x_738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_738_, 0, v___y_733_);
lean_ctor_set(v___x_738_, 1, v___y_732_);
lean_ctor_set(v___x_738_, 2, v___x_737_);
v___x_739_ = l_Lean_Syntax_node6(v___y_733_, v___y_734_, v___y_735_, v___x_705_, v___y_731_, v___y_730_, v___y_729_, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
v___jp_741_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc_ref(v___y_742_);
v___x_750_ = l_Array_append___redArg(v___y_742_, v___y_749_);
lean_dec_ref(v___y_749_);
lean_inc(v___y_745_);
lean_inc(v___y_746_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___y_746_);
lean_ctor_set(v___x_751_, 1, v___y_745_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
if (lean_obj_tag(v_loc_717_) == 1)
{
lean_object* v_val_752_; lean_object* v___x_753_; 
v_val_752_ = lean_ctor_get(v_loc_717_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v_loc_717_, 1);
v___x_753_ = l_Array_mkArray1___redArg(v_val_752_);
v___y_728_ = v___y_742_;
v___y_729_ = v___x_751_;
v___y_730_ = v___y_743_;
v___y_731_ = v___y_744_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_746_;
v___y_734_ = v___y_747_;
v___y_735_ = v___y_748_;
v___y_736_ = v___x_753_;
goto v___jp_727_;
}
else
{
lean_object* v___x_754_; 
lean_dec(v_loc_717_);
v___x_754_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_728_ = v___y_742_;
v___y_729_ = v___x_751_;
v___y_730_ = v___y_743_;
v___y_731_ = v___y_744_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_746_;
v___y_734_ = v___y_747_;
v___y_735_ = v___y_748_;
v___y_736_ = v___x_754_;
goto v___jp_727_;
}
}
v___jp_755_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_inc_ref(v___y_756_);
v___x_763_ = l_Array_append___redArg(v___y_756_, v___y_762_);
lean_dec_ref(v___y_762_);
lean_inc(v___y_758_);
lean_inc(v___y_759_);
v___x_764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_764_, 0, v___y_759_);
lean_ctor_set(v___x_764_, 1, v___y_758_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_val_765_ = lean_ctor_get(v_args_707_, 0);
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_759_, 3);
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___y_759_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
lean_inc_ref(v___y_756_);
v___x_768_ = l_Array_append___redArg(v___y_756_, v_val_765_);
lean_inc(v___y_758_);
v___x_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_769_, 0, v___y_759_);
lean_ctor_set(v___x_769_, 1, v___y_758_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
v___x_770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___y_759_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Array_mkArray3___redArg(v___x_767_, v___x_769_, v___x_771_);
v___y_742_ = v___y_756_;
v___y_743_ = v___x_764_;
v___y_744_ = v___y_757_;
v___y_745_ = v___y_758_;
v___y_746_ = v___y_759_;
v___y_747_ = v___y_760_;
v___y_748_ = v___y_761_;
v___y_749_ = v___x_772_;
goto v___jp_741_;
}
else
{
lean_object* v___x_773_; 
v___x_773_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_742_ = v___y_756_;
v___y_743_ = v___x_764_;
v___y_744_ = v___y_757_;
v___y_745_ = v___y_758_;
v___y_746_ = v___y_759_;
v___y_747_ = v___y_760_;
v___y_748_ = v___y_761_;
v___y_749_ = v___x_773_;
goto v___jp_741_;
}
}
v___jp_774_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_inc_ref(v___y_775_);
v___x_781_ = l_Array_append___redArg(v___y_775_, v___y_780_);
lean_dec_ref(v___y_780_);
lean_inc(v___y_776_);
lean_inc(v___y_777_);
v___x_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_782_, 0, v___y_777_);
lean_ctor_set(v___x_782_, 1, v___y_776_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_val_783_ = lean_ctor_get(v_only_708_, 0);
v___x_784_ = l_Lean_SourceInfo_fromRef(v_val_783_, v___x_709_);
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Array_mkArray1___redArg(v___x_786_);
v___y_756_ = v___y_775_;
v___y_757_ = v___x_782_;
v___y_758_ = v___y_776_;
v___y_759_ = v___y_777_;
v___y_760_ = v___y_778_;
v___y_761_ = v___y_779_;
v___y_762_ = v___x_787_;
goto v___jp_755_;
}
else
{
lean_object* v___x_788_; 
v___x_788_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_756_ = v___y_775_;
v___y_757_ = v___x_782_;
v___y_758_ = v___y_776_;
v___y_759_ = v___y_777_;
v___y_760_ = v___y_778_;
v___y_761_ = v___y_779_;
v___y_762_ = v___x_788_;
goto v___jp_755_;
}
}
v___jp_789_:
{
lean_object* v_ref_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_ref_791_ = lean_ctor_get(v___y_724_, 2);
v___x_792_ = l_Lean_SourceInfo_fromRef(v_ref_791_, v___y_790_);
v___x_793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
v___x_794_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_793_);
lean_inc(v___x_792_);
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_792_);
lean_ctor_set(v___x_795_, 1, v___x_793_);
v___x_796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_797_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v___x_798_; 
v___x_798_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_775_ = v___x_797_;
v___y_776_ = v___x_796_;
v___y_777_ = v___x_792_;
v___y_778_ = v___x_794_;
v___y_779_ = v___x_795_;
v___y_780_ = v___x_798_;
goto v___jp_774_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_val_799_ = lean_ctor_get(v___y_713_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___y_713_, 1);
v___x_800_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_801_ = lean_array_push(v___x_800_, v_val_799_);
v___y_775_ = v___x_797_;
v___y_776_ = v___x_796_;
v___y_777_ = v___x_792_;
v___y_778_ = v___x_794_;
v___y_779_ = v___x_795_;
v___y_780_ = v___x_801_;
goto v___jp_774_;
}
}
v___jp_802_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_inc_ref(v___y_806_);
v___x_812_ = l_Array_append___redArg(v___y_806_, v___y_811_);
lean_dec_ref(v___y_811_);
lean_inc(v___y_804_);
lean_inc(v___y_805_);
v___x_813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_813_, 0, v___y_805_);
lean_ctor_set(v___x_813_, 1, v___y_804_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
v___x_814_ = l_Lean_Syntax_node6(v___y_805_, v___y_809_, v___y_803_, v___x_705_, v___y_808_, v___y_810_, v___y_807_, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
v___jp_816_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_inc_ref(v___y_820_);
v___x_825_ = l_Array_append___redArg(v___y_820_, v___y_824_);
lean_dec_ref(v___y_824_);
lean_inc(v___y_818_);
lean_inc(v___y_819_);
v___x_826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_826_, 0, v___y_819_);
lean_ctor_set(v___x_826_, 1, v___y_818_);
lean_ctor_set(v___x_826_, 2, v___x_825_);
if (lean_obj_tag(v_loc_717_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_828_; 
v_val_827_ = lean_ctor_get(v_loc_717_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v_loc_717_, 1);
v___x_828_ = l_Array_mkArray1___redArg(v_val_827_);
v___y_803_ = v___y_817_;
v___y_804_ = v___y_818_;
v___y_805_ = v___y_819_;
v___y_806_ = v___y_820_;
v___y_807_ = v___x_826_;
v___y_808_ = v___y_821_;
v___y_809_ = v___y_822_;
v___y_810_ = v___y_823_;
v___y_811_ = v___x_828_;
goto v___jp_802_;
}
else
{
lean_object* v___x_829_; 
lean_dec(v_loc_717_);
v___x_829_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_803_ = v___y_817_;
v___y_804_ = v___y_818_;
v___y_805_ = v___y_819_;
v___y_806_ = v___y_820_;
v___y_807_ = v___x_826_;
v___y_808_ = v___y_821_;
v___y_809_ = v___y_822_;
v___y_810_ = v___y_823_;
v___y_811_ = v___x_829_;
goto v___jp_802_;
}
}
v___jp_830_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_inc_ref(v___y_834_);
v___x_838_ = l_Array_append___redArg(v___y_834_, v___y_837_);
lean_dec_ref(v___y_837_);
lean_inc(v___y_832_);
lean_inc(v___y_833_);
v___x_839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_839_, 0, v___y_833_);
lean_ctor_set(v___x_839_, 1, v___y_832_);
lean_ctor_set(v___x_839_, 2, v___x_838_);
if (lean_obj_tag(v_args_707_) == 1)
{
lean_object* v_val_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_val_840_ = lean_ctor_get(v_args_707_, 0);
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_833_, 3);
v___x_842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_833_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_inc_ref(v___y_834_);
v___x_843_ = l_Array_append___redArg(v___y_834_, v_val_840_);
lean_inc(v___y_832_);
v___x_844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_844_, 0, v___y_833_);
lean_ctor_set(v___x_844_, 1, v___y_832_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
v___x_845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_846_, 0, v___y_833_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = l_Array_mkArray3___redArg(v___x_842_, v___x_844_, v___x_846_);
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v___y_819_ = v___y_833_;
v___y_820_ = v___y_834_;
v___y_821_ = v___y_835_;
v___y_822_ = v___y_836_;
v___y_823_ = v___x_839_;
v___y_824_ = v___x_847_;
goto v___jp_816_;
}
else
{
lean_object* v___x_848_; 
v___x_848_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_817_ = v___y_831_;
v___y_818_ = v___y_832_;
v___y_819_ = v___y_833_;
v___y_820_ = v___y_834_;
v___y_821_ = v___y_835_;
v___y_822_ = v___y_836_;
v___y_823_ = v___x_839_;
v___y_824_ = v___x_848_;
goto v___jp_816_;
}
}
v___jp_849_:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc_ref(v___y_853_);
v___x_856_ = l_Array_append___redArg(v___y_853_, v___y_855_);
lean_dec_ref(v___y_855_);
lean_inc(v___y_851_);
lean_inc(v___y_852_);
v___x_857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_857_, 0, v___y_852_);
lean_ctor_set(v___x_857_, 1, v___y_851_);
lean_ctor_set(v___x_857_, 2, v___x_856_);
if (lean_obj_tag(v_only_708_) == 1)
{
lean_object* v_val_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_val_858_ = lean_ctor_get(v_only_708_, 0);
v___x_859_ = l_Lean_SourceInfo_fromRef(v_val_858_, v___x_709_);
v___x_860_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Array_mkArray1___redArg(v___x_861_);
v___y_831_ = v___y_850_;
v___y_832_ = v___y_851_;
v___y_833_ = v___y_852_;
v___y_834_ = v___y_853_;
v___y_835_ = v___x_857_;
v___y_836_ = v___y_854_;
v___y_837_ = v___x_862_;
goto v___jp_830_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_831_ = v___y_850_;
v___y_832_ = v___y_851_;
v___y_833_ = v___y_852_;
v___y_834_ = v___y_853_;
v___y_835_ = v___x_857_;
v___y_836_ = v___y_854_;
v___y_837_ = v___x_863_;
goto v___jp_830_;
}
}
v___jp_864_:
{
if (lean_obj_tag(v_unfold_714_) == 0)
{
v___y_790_ = v___y_865_;
goto v___jp_789_;
}
else
{
lean_dec_ref_known(v_unfold_714_, 1);
if (v___x_715_ == 0)
{
v___y_790_ = v___x_715_;
goto v___jp_789_;
}
else
{
lean_object* v_ref_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_ref_866_ = lean_ctor_get(v___y_724_, 2);
v___x_867_ = l_Lean_SourceInfo_fromRef(v_ref_866_, v___y_865_);
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7));
v___x_869_ = l_Lean_Name_mkStr4(v___x_710_, v___x_711_, v___x_712_, v___x_868_);
v___x_870_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8));
lean_inc(v___x_867_);
v___x_871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_867_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_873_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v___x_874_; 
v___x_874_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___y_850_ = v___x_871_;
v___y_851_ = v___x_872_;
v___y_852_ = v___x_867_;
v___y_853_ = v___x_873_;
v___y_854_ = v___x_869_;
v___y_855_ = v___x_874_;
goto v___jp_849_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_val_875_ = lean_ctor_get(v___y_713_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___y_713_, 1);
v___x_876_ = lean_mk_empty_array_with_capacity(v___x_706_);
v___x_877_ = lean_array_push(v___x_876_, v_val_875_);
v___y_850_ = v___x_871_;
v___y_851_ = v___x_872_;
v___y_852_ = v___x_867_;
v___y_853_ = v___x_873_;
v___y_854_ = v___x_869_;
v___y_855_ = v___x_877_;
goto v___jp_849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_1016_ = _args[0];
lean_object* v___x_1017_ = _args[1];
lean_object* v_args_1018_ = _args[2];
lean_object* v_only_1019_ = _args[3];
lean_object* v___x_1020_ = _args[4];
lean_object* v___x_1021_ = _args[5];
lean_object* v___x_1022_ = _args[6];
lean_object* v___x_1023_ = _args[7];
lean_object* v___y_1024_ = _args[8];
lean_object* v_unfold_1025_ = _args[9];
lean_object* v___x_1026_ = _args[10];
lean_object* v_squeeze_1027_ = _args[11];
lean_object* v_loc_1028_ = _args[12];
lean_object* v___y_1029_ = _args[13];
lean_object* v___y_1030_ = _args[14];
lean_object* v___y_1031_ = _args[15];
lean_object* v___y_1032_ = _args[16];
lean_object* v___y_1033_ = _args[17];
lean_object* v___y_1034_ = _args[18];
lean_object* v___y_1035_ = _args[19];
lean_object* v___y_1036_ = _args[20];
lean_object* v___y_1037_ = _args[21];
_start:
{
uint8_t v___x_93223__boxed_1038_; uint8_t v___x_93228__boxed_1039_; lean_object* v_res_1040_; 
v___x_93223__boxed_1038_ = lean_unbox(v___x_1020_);
v___x_93228__boxed_1039_ = lean_unbox(v___x_1026_);
v_res_1040_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_1016_, v___x_1017_, v_args_1018_, v_only_1019_, v___x_93223__boxed_1038_, v___x_1021_, v___x_1022_, v___x_1023_, v___y_1024_, v_unfold_1025_, v___x_93228__boxed_1039_, v_squeeze_1027_, v_loc_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v_only_1019_);
lean_dec(v_args_1018_);
lean_dec(v___x_1017_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_1041_, lean_object* v_trees_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
v___x_1052_ = lean_apply_9(v_a_1041_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, lean_box(0));
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_a_1053_);
lean_ctor_set(v___x_1057_, 1, v_trees_1042_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_trees_1042_);
v_a_1062_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1052_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object* v_a_1070_, lean_object* v_trees_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1070_, v_trees_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v_res_1081_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1088_, lean_object* v_a_1089_, uint8_t v___x_1090_, lean_object* v_a_1091_, lean_object* v_mvarCounter_1092_, lean_object* v___x_1093_, uint8_t v___x_1094_, lean_object* v___x_1095_, uint8_t v_useReducible_1096_, uint8_t v___x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
lean_inc(v_a_1088_);
v___x_1107_ = l_Lean_MVarId_getType(v_a_1088_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc_n(v_a_1108_, 2);
lean_dec_ref_known(v___x_1107_, 1);
v___x_1109_ = l_Lean_mkIdent(v_a_1089_);
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_a_1108_);
v___x_1111_ = l_Lean_Elab_Term_elabTerm(v___x_1109_, v___x_1110_, v___x_1090_, v___x_1090_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___x_1146_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___x_1146_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1094_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1329_; 
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1330_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1329_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1329_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; 
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v_a_1112_);
v___x_1150_ = lean_infer_type(v_a_1112_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; uint8_t v_____do__lift_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1172_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
if (v_useReducible_1096_ == 0)
{
lean_object* v___x_1183_; uint8_t v_foApprox_1184_; uint8_t v_ctxApprox_1185_; uint8_t v_quasiPatternApprox_1186_; uint8_t v_constApprox_1187_; uint8_t v_isDefEqStuckEx_1188_; uint8_t v_unificationHints_1189_; uint8_t v_proofIrrelevance_1190_; uint8_t v_offsetCnstrs_1191_; uint8_t v_transparency_1192_; uint8_t v_etaStruct_1193_; uint8_t v_univApprox_1194_; uint8_t v_iota_1195_; uint8_t v_beta_1196_; uint8_t v_proj_1197_; uint8_t v_zeta_1198_; uint8_t v_zetaDelta_1199_; uint8_t v_zetaUnused_1200_; uint8_t v_zetaHave_1201_; uint8_t v_canUnfoldPredicateConfig_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1233_; 
v___x_1183_ = l_Lean_Meta_Context_config(v___y_1102_);
v_foApprox_1184_ = lean_ctor_get_uint8(v___x_1183_, 0);
v_ctxApprox_1185_ = lean_ctor_get_uint8(v___x_1183_, 1);
v_quasiPatternApprox_1186_ = lean_ctor_get_uint8(v___x_1183_, 2);
v_constApprox_1187_ = lean_ctor_get_uint8(v___x_1183_, 3);
v_isDefEqStuckEx_1188_ = lean_ctor_get_uint8(v___x_1183_, 4);
v_unificationHints_1189_ = lean_ctor_get_uint8(v___x_1183_, 5);
v_proofIrrelevance_1190_ = lean_ctor_get_uint8(v___x_1183_, 6);
v_offsetCnstrs_1191_ = lean_ctor_get_uint8(v___x_1183_, 8);
v_transparency_1192_ = lean_ctor_get_uint8(v___x_1183_, 9);
v_etaStruct_1193_ = lean_ctor_get_uint8(v___x_1183_, 10);
v_univApprox_1194_ = lean_ctor_get_uint8(v___x_1183_, 11);
v_iota_1195_ = lean_ctor_get_uint8(v___x_1183_, 12);
v_beta_1196_ = lean_ctor_get_uint8(v___x_1183_, 13);
v_proj_1197_ = lean_ctor_get_uint8(v___x_1183_, 14);
v_zeta_1198_ = lean_ctor_get_uint8(v___x_1183_, 15);
v_zetaDelta_1199_ = lean_ctor_get_uint8(v___x_1183_, 16);
v_zetaUnused_1200_ = lean_ctor_get_uint8(v___x_1183_, 17);
v_zetaHave_1201_ = lean_ctor_get_uint8(v___x_1183_, 18);
v_canUnfoldPredicateConfig_1202_ = lean_ctor_get_uint8(v___x_1183_, 19);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1204_ = v___x_1183_;
v_isShared_1205_ = v_isSharedCheck_1233_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v___x_1183_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1233_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
uint8_t v_trackZetaDelta_1206_; lean_object* v_zetaDeltaSet_1207_; lean_object* v_lctx_1208_; lean_object* v_localInstances_1209_; lean_object* v_defEqCtx_x3f_1210_; lean_object* v_synthPendingDepth_1211_; lean_object* v_customCanUnfoldPredicate_x3f_1212_; uint8_t v_univApprox_1213_; uint8_t v_inTypeClassResolution_1214_; uint8_t v_cacheInferType_1215_; lean_object* v___x_1217_; 
v_trackZetaDelta_1206_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7);
v_zetaDeltaSet_1207_ = lean_ctor_get(v___y_1102_, 1);
v_lctx_1208_ = lean_ctor_get(v___y_1102_, 2);
v_localInstances_1209_ = lean_ctor_get(v___y_1102_, 3);
v_defEqCtx_x3f_1210_ = lean_ctor_get(v___y_1102_, 4);
v_synthPendingDepth_1211_ = lean_ctor_get(v___y_1102_, 5);
v_customCanUnfoldPredicate_x3f_1212_ = lean_ctor_get(v___y_1102_, 6);
v_univApprox_1213_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1214_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 2);
v_cacheInferType_1215_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 3);
if (v_isShared_1205_ == 0)
{
v___x_1217_ = v___x_1204_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 0, v_foApprox_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 1, v_ctxApprox_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 2, v_quasiPatternApprox_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 3, v_constApprox_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 4, v_isDefEqStuckEx_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 5, v_unificationHints_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 6, v_proofIrrelevance_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 8, v_offsetCnstrs_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 9, v_transparency_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 10, v_etaStruct_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 11, v_univApprox_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 12, v_iota_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 13, v_beta_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 14, v_proj_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 15, v_zeta_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 16, v_zetaDelta_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 17, v_zetaUnused_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 18, v_zetaHave_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1232_, 19, v_canUnfoldPredicateConfig_1202_);
v___x_1217_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
uint64_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_ctor_set_uint8(v___x_1217_, 7, v___x_1097_);
v___x_1218_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set_uint64(v___x_1219_, sizeof(void*)*1, v___x_1218_);
lean_inc(v_customCanUnfoldPredicate_x3f_1212_);
lean_inc(v_synthPendingDepth_1211_);
lean_inc(v_defEqCtx_x3f_1210_);
lean_inc_ref(v_localInstances_1209_);
lean_inc_ref(v_lctx_1208_);
lean_inc(v_zetaDeltaSet_1207_);
v___x_1220_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v_zetaDeltaSet_1207_);
lean_ctor_set(v___x_1220_, 2, v_lctx_1208_);
lean_ctor_set(v___x_1220_, 3, v_localInstances_1209_);
lean_ctor_set(v___x_1220_, 4, v_defEqCtx_x3f_1210_);
lean_ctor_set(v___x_1220_, 5, v_synthPendingDepth_1211_);
lean_ctor_set(v___x_1220_, 6, v_customCanUnfoldPredicate_x3f_1212_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*7, v_trackZetaDelta_1206_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*7 + 1, v_univApprox_1213_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1214_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*7 + 3, v_cacheInferType_1215_);
lean_inc(v_a_1151_);
lean_inc(v_a_1108_);
v___x_1221_ = l_Lean_Meta_isExprDefEq(v_a_1108_, v_a_1151_, v___x_1220_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref_known(v___x_1220_, 7);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; uint8_t v___x_1223_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = lean_unbox(v_a_1222_);
lean_dec(v_a_1222_);
v_____do__lift_1153_ = v___x_1223_;
v___y_1154_ = v___y_1098_;
v___y_1155_ = v___y_1099_;
v___y_1156_ = v___y_1100_;
v___y_1157_ = v___y_1101_;
v___y_1158_ = v___y_1102_;
v___y_1159_ = v___y_1103_;
v___y_1160_ = v___y_1104_;
v___y_1161_ = v___y_1105_;
goto v___jp_1152_;
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1151_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1112_);
lean_dec(v_a_1108_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1088_);
v_a_1224_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1221_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1221_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
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
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
else
{
lean_object* v___x_1234_; uint8_t v_foApprox_1235_; uint8_t v_ctxApprox_1236_; uint8_t v_quasiPatternApprox_1237_; uint8_t v_constApprox_1238_; uint8_t v_isDefEqStuckEx_1239_; uint8_t v_unificationHints_1240_; uint8_t v_proofIrrelevance_1241_; uint8_t v_offsetCnstrs_1242_; uint8_t v_transparency_1243_; uint8_t v_etaStruct_1244_; uint8_t v_univApprox_1245_; uint8_t v_iota_1246_; uint8_t v_beta_1247_; uint8_t v_proj_1248_; uint8_t v_zeta_1249_; uint8_t v_zetaDelta_1250_; uint8_t v_zetaUnused_1251_; uint8_t v_zetaHave_1252_; uint8_t v_canUnfoldPredicateConfig_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1320_; 
v___x_1234_ = l_Lean_Meta_Context_config(v___y_1102_);
v_foApprox_1235_ = lean_ctor_get_uint8(v___x_1234_, 0);
v_ctxApprox_1236_ = lean_ctor_get_uint8(v___x_1234_, 1);
v_quasiPatternApprox_1237_ = lean_ctor_get_uint8(v___x_1234_, 2);
v_constApprox_1238_ = lean_ctor_get_uint8(v___x_1234_, 3);
v_isDefEqStuckEx_1239_ = lean_ctor_get_uint8(v___x_1234_, 4);
v_unificationHints_1240_ = lean_ctor_get_uint8(v___x_1234_, 5);
v_proofIrrelevance_1241_ = lean_ctor_get_uint8(v___x_1234_, 6);
v_offsetCnstrs_1242_ = lean_ctor_get_uint8(v___x_1234_, 8);
v_transparency_1243_ = lean_ctor_get_uint8(v___x_1234_, 9);
v_etaStruct_1244_ = lean_ctor_get_uint8(v___x_1234_, 10);
v_univApprox_1245_ = lean_ctor_get_uint8(v___x_1234_, 11);
v_iota_1246_ = lean_ctor_get_uint8(v___x_1234_, 12);
v_beta_1247_ = lean_ctor_get_uint8(v___x_1234_, 13);
v_proj_1248_ = lean_ctor_get_uint8(v___x_1234_, 14);
v_zeta_1249_ = lean_ctor_get_uint8(v___x_1234_, 15);
v_zetaDelta_1250_ = lean_ctor_get_uint8(v___x_1234_, 16);
v_zetaUnused_1251_ = lean_ctor_get_uint8(v___x_1234_, 17);
v_zetaHave_1252_ = lean_ctor_get_uint8(v___x_1234_, 18);
v_canUnfoldPredicateConfig_1253_ = lean_ctor_get_uint8(v___x_1234_, 19);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1255_ = v___x_1234_;
v_isShared_1256_ = v_isSharedCheck_1320_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v___x_1234_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1320_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
uint8_t v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = 2;
v___x_1258_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1243_, v___x_1257_);
if (v___x_1258_ == 0)
{
lean_object* v_keyedConfig_1259_; uint8_t v_trackZetaDelta_1260_; lean_object* v_zetaDeltaSet_1261_; lean_object* v_lctx_1262_; lean_object* v_localInstances_1263_; lean_object* v_defEqCtx_x3f_1264_; lean_object* v_synthPendingDepth_1265_; lean_object* v_customCanUnfoldPredicate_x3f_1266_; uint8_t v_univApprox_1267_; uint8_t v_inTypeClassResolution_1268_; uint8_t v_cacheInferType_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v_foApprox_1273_; uint8_t v_ctxApprox_1274_; uint8_t v_quasiPatternApprox_1275_; uint8_t v_constApprox_1276_; uint8_t v_isDefEqStuckEx_1277_; uint8_t v_unificationHints_1278_; uint8_t v_proofIrrelevance_1279_; uint8_t v_offsetCnstrs_1280_; uint8_t v_transparency_1281_; uint8_t v_etaStruct_1282_; uint8_t v_univApprox_1283_; uint8_t v_iota_1284_; uint8_t v_beta_1285_; uint8_t v_proj_1286_; uint8_t v_zeta_1287_; uint8_t v_zetaDelta_1288_; uint8_t v_zetaUnused_1289_; uint8_t v_zetaHave_1290_; uint8_t v_canUnfoldPredicateConfig_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1302_; 
lean_del_object(v___x_1255_);
v_keyedConfig_1259_ = lean_ctor_get(v___y_1102_, 0);
v_trackZetaDelta_1260_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7);
v_zetaDeltaSet_1261_ = lean_ctor_get(v___y_1102_, 1);
v_lctx_1262_ = lean_ctor_get(v___y_1102_, 2);
v_localInstances_1263_ = lean_ctor_get(v___y_1102_, 3);
v_defEqCtx_x3f_1264_ = lean_ctor_get(v___y_1102_, 4);
v_synthPendingDepth_1265_ = lean_ctor_get(v___y_1102_, 5);
v_customCanUnfoldPredicate_x3f_1266_ = lean_ctor_get(v___y_1102_, 6);
v_univApprox_1267_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1268_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 2);
v_cacheInferType_1269_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1259_);
v___x_1270_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1257_, v_keyedConfig_1259_);
lean_inc(v_customCanUnfoldPredicate_x3f_1266_);
lean_inc(v_synthPendingDepth_1265_);
lean_inc(v_defEqCtx_x3f_1264_);
lean_inc_ref(v_localInstances_1263_);
lean_inc_ref(v_lctx_1262_);
lean_inc(v_zetaDeltaSet_1261_);
v___x_1271_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_zetaDeltaSet_1261_);
lean_ctor_set(v___x_1271_, 2, v_lctx_1262_);
lean_ctor_set(v___x_1271_, 3, v_localInstances_1263_);
lean_ctor_set(v___x_1271_, 4, v_defEqCtx_x3f_1264_);
lean_ctor_set(v___x_1271_, 5, v_synthPendingDepth_1265_);
lean_ctor_set(v___x_1271_, 6, v_customCanUnfoldPredicate_x3f_1266_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*7, v_trackZetaDelta_1260_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*7 + 1, v_univApprox_1267_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1268_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*7 + 3, v_cacheInferType_1269_);
v___x_1272_ = l_Lean_Meta_Context_config(v___x_1271_);
lean_dec_ref_known(v___x_1271_, 7);
v_foApprox_1273_ = lean_ctor_get_uint8(v___x_1272_, 0);
v_ctxApprox_1274_ = lean_ctor_get_uint8(v___x_1272_, 1);
v_quasiPatternApprox_1275_ = lean_ctor_get_uint8(v___x_1272_, 2);
v_constApprox_1276_ = lean_ctor_get_uint8(v___x_1272_, 3);
v_isDefEqStuckEx_1277_ = lean_ctor_get_uint8(v___x_1272_, 4);
v_unificationHints_1278_ = lean_ctor_get_uint8(v___x_1272_, 5);
v_proofIrrelevance_1279_ = lean_ctor_get_uint8(v___x_1272_, 6);
v_offsetCnstrs_1280_ = lean_ctor_get_uint8(v___x_1272_, 8);
v_transparency_1281_ = lean_ctor_get_uint8(v___x_1272_, 9);
v_etaStruct_1282_ = lean_ctor_get_uint8(v___x_1272_, 10);
v_univApprox_1283_ = lean_ctor_get_uint8(v___x_1272_, 11);
v_iota_1284_ = lean_ctor_get_uint8(v___x_1272_, 12);
v_beta_1285_ = lean_ctor_get_uint8(v___x_1272_, 13);
v_proj_1286_ = lean_ctor_get_uint8(v___x_1272_, 14);
v_zeta_1287_ = lean_ctor_get_uint8(v___x_1272_, 15);
v_zetaDelta_1288_ = lean_ctor_get_uint8(v___x_1272_, 16);
v_zetaUnused_1289_ = lean_ctor_get_uint8(v___x_1272_, 17);
v_zetaHave_1290_ = lean_ctor_get_uint8(v___x_1272_, 18);
v_canUnfoldPredicateConfig_1291_ = lean_ctor_get_uint8(v___x_1272_, 19);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1293_ = v___x_1272_;
v_isShared_1294_ = v_isSharedCheck_1302_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v___x_1272_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1302_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 0, v_foApprox_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 1, v_ctxApprox_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 2, v_quasiPatternApprox_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 3, v_constApprox_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 4, v_isDefEqStuckEx_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 5, v_unificationHints_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 6, v_proofIrrelevance_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 8, v_offsetCnstrs_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 9, v_transparency_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 10, v_etaStruct_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 11, v_univApprox_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 12, v_iota_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 13, v_beta_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 14, v_proj_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 15, v_zeta_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 16, v_zetaDelta_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 17, v_zetaUnused_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 18, v_zetaHave_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1301_, 19, v_canUnfoldPredicateConfig_1291_);
v___x_1296_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
uint64_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_ctor_set_uint8(v___x_1296_, 7, v___x_1097_);
v___x_1297_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1296_);
v___x_1298_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set_uint64(v___x_1298_, sizeof(void*)*1, v___x_1297_);
lean_inc(v_customCanUnfoldPredicate_x3f_1266_);
lean_inc(v_synthPendingDepth_1265_);
lean_inc(v_defEqCtx_x3f_1264_);
lean_inc_ref(v_localInstances_1263_);
lean_inc_ref(v_lctx_1262_);
lean_inc(v_zetaDeltaSet_1261_);
v___x_1299_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_zetaDeltaSet_1261_);
lean_ctor_set(v___x_1299_, 2, v_lctx_1262_);
lean_ctor_set(v___x_1299_, 3, v_localInstances_1263_);
lean_ctor_set(v___x_1299_, 4, v_defEqCtx_x3f_1264_);
lean_ctor_set(v___x_1299_, 5, v_synthPendingDepth_1265_);
lean_ctor_set(v___x_1299_, 6, v_customCanUnfoldPredicate_x3f_1266_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*7, v_trackZetaDelta_1260_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*7 + 1, v_univApprox_1267_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1268_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*7 + 3, v_cacheInferType_1269_);
lean_inc(v_a_1151_);
lean_inc(v_a_1108_);
v___x_1300_ = l_Lean_Meta_isExprDefEq(v_a_1108_, v_a_1151_, v___x_1299_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref_known(v___x_1299_, 7);
v___y_1172_ = v___x_1300_;
goto v___jp_1171_;
}
}
}
else
{
uint8_t v_trackZetaDelta_1303_; lean_object* v_zetaDeltaSet_1304_; lean_object* v_lctx_1305_; lean_object* v_localInstances_1306_; lean_object* v_defEqCtx_x3f_1307_; lean_object* v_synthPendingDepth_1308_; lean_object* v_customCanUnfoldPredicate_x3f_1309_; uint8_t v_univApprox_1310_; uint8_t v_inTypeClassResolution_1311_; uint8_t v_cacheInferType_1312_; lean_object* v___x_1314_; 
v_trackZetaDelta_1303_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7);
v_zetaDeltaSet_1304_ = lean_ctor_get(v___y_1102_, 1);
v_lctx_1305_ = lean_ctor_get(v___y_1102_, 2);
v_localInstances_1306_ = lean_ctor_get(v___y_1102_, 3);
v_defEqCtx_x3f_1307_ = lean_ctor_get(v___y_1102_, 4);
v_synthPendingDepth_1308_ = lean_ctor_get(v___y_1102_, 5);
v_customCanUnfoldPredicate_x3f_1309_ = lean_ctor_get(v___y_1102_, 6);
v_univApprox_1310_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1311_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 2);
v_cacheInferType_1312_ = lean_ctor_get_uint8(v___y_1102_, sizeof(void*)*7 + 3);
if (v_isShared_1256_ == 0)
{
v___x_1314_ = v___x_1255_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 0, v_foApprox_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 1, v_ctxApprox_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 2, v_quasiPatternApprox_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 3, v_constApprox_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 4, v_isDefEqStuckEx_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 5, v_unificationHints_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 6, v_proofIrrelevance_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 8, v_offsetCnstrs_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 9, v_transparency_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 10, v_etaStruct_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 11, v_univApprox_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 12, v_iota_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 13, v_beta_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 14, v_proj_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 15, v_zeta_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 16, v_zetaDelta_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 17, v_zetaUnused_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 18, v_zetaHave_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, 19, v_canUnfoldPredicateConfig_1253_);
v___x_1314_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
uint64_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_ctor_set_uint8(v___x_1314_, 7, v___x_1097_);
v___x_1315_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1314_);
v___x_1316_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set_uint64(v___x_1316_, sizeof(void*)*1, v___x_1315_);
lean_inc(v_customCanUnfoldPredicate_x3f_1309_);
lean_inc(v_synthPendingDepth_1308_);
lean_inc(v_defEqCtx_x3f_1307_);
lean_inc_ref(v_localInstances_1306_);
lean_inc_ref(v_lctx_1305_);
lean_inc(v_zetaDeltaSet_1304_);
v___x_1317_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v_zetaDeltaSet_1304_);
lean_ctor_set(v___x_1317_, 2, v_lctx_1305_);
lean_ctor_set(v___x_1317_, 3, v_localInstances_1306_);
lean_ctor_set(v___x_1317_, 4, v_defEqCtx_x3f_1307_);
lean_ctor_set(v___x_1317_, 5, v_synthPendingDepth_1308_);
lean_ctor_set(v___x_1317_, 6, v_customCanUnfoldPredicate_x3f_1309_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*7, v_trackZetaDelta_1303_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*7 + 1, v_univApprox_1310_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1311_);
lean_ctor_set_uint8(v___x_1317_, sizeof(void*)*7 + 3, v_cacheInferType_1312_);
lean_inc(v_a_1151_);
lean_inc(v_a_1108_);
v___x_1318_ = l_Lean_Meta_isExprDefEq(v_a_1108_, v_a_1151_, v___x_1317_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref_known(v___x_1317_, 7);
v___y_1172_ = v___x_1318_;
goto v___jp_1171_;
}
}
}
}
v___jp_1152_:
{
if (v_____do__lift_1153_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1);
lean_inc_ref(v_a_1091_);
v___x_1163_ = l_Lean_indentExpr(v_a_1091_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 1);
lean_ctor_set(v___x_1148_, 0, v___x_1166_);
v___x_1168_ = v___x_1148_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; 
lean_inc(v_a_1112_);
v___x_1169_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1168_, v_a_1108_, v_a_1151_, v_a_1112_, v___x_1095_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec_ref(v___x_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_dec_ref_known(v___x_1169_, 1);
v___y_1114_ = v___y_1154_;
v___y_1115_ = v___y_1155_;
v___y_1116_ = v___y_1156_;
v___y_1117_ = v___y_1157_;
v___y_1118_ = v___y_1158_;
v___y_1119_ = v___y_1159_;
v___y_1120_ = v___y_1160_;
v___y_1121_ = v___y_1161_;
goto v___jp_1113_;
}
else
{
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v_a_1112_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1088_);
return v___x_1169_;
}
}
}
else
{
lean_dec(v_a_1151_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1108_);
lean_dec(v___x_1095_);
v___y_1114_ = v___y_1154_;
v___y_1115_ = v___y_1155_;
v___y_1116_ = v___y_1156_;
v___y_1117_ = v___y_1157_;
v___y_1118_ = v___y_1158_;
v___y_1119_ = v___y_1159_;
v___y_1120_ = v___y_1160_;
v___y_1121_ = v___y_1161_;
goto v___jp_1113_;
}
}
v___jp_1171_:
{
if (lean_obj_tag(v___y_1172_) == 0)
{
lean_object* v_a_1173_; uint8_t v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___y_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___y_1172_, 1);
v___x_1174_ = lean_unbox(v_a_1173_);
lean_dec(v_a_1173_);
v_____do__lift_1153_ = v___x_1174_;
v___y_1154_ = v___y_1098_;
v___y_1155_ = v___y_1099_;
v___y_1156_ = v___y_1100_;
v___y_1157_ = v___y_1101_;
v___y_1158_ = v___y_1102_;
v___y_1159_ = v___y_1103_;
v___y_1160_ = v___y_1104_;
v___y_1161_ = v___y_1105_;
goto v___jp_1152_;
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_a_1151_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1112_);
lean_dec(v_a_1108_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1088_);
v_a_1175_ = lean_ctor_get(v___y_1172_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___y_1172_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___y_1172_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___y_1172_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_del_object(v___x_1148_);
lean_dec(v_a_1112_);
lean_dec(v_a_1108_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1088_);
v_a_1321_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1150_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1150_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
else
{
lean_dec(v_a_1112_);
lean_dec(v_a_1108_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1088_);
return v___x_1146_;
}
v___jp_1113_:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Meta_getMVars(v_a_1091_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1123_, v_mvarCounter_1092_, v___y_1119_);
lean_dec(v_a_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1126_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___x_1126_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1125_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v_a_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1126_, 1);
v___x_1127_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_1088_, v___y_1115_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec_ref_known(v___x_1127_, 1);
v___x_1128_ = l_Lean_Name_mkStr1(v___x_1093_);
v___x_1129_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1128_, v_a_1112_, v___x_1094_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v___x_1129_;
}
else
{
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v_a_1112_);
lean_dec_ref(v___x_1093_);
return v___x_1127_;
}
}
else
{
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v_a_1112_);
lean_dec_ref(v___x_1093_);
lean_dec(v_a_1088_);
return v___x_1126_;
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v_a_1112_);
lean_dec_ref(v___x_1093_);
lean_dec(v_a_1088_);
v_a_1130_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1124_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1124_);
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
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v_a_1112_);
lean_dec_ref(v___x_1093_);
lean_dec(v_a_1088_);
v_a_1138_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1122_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1122_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_a_1108_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1088_);
v_a_1331_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1111_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1111_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___x_1095_);
lean_dec_ref(v___x_1093_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1089_);
lean_dec(v_a_1088_);
v_a_1339_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1107_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1107_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object** _args){
lean_object* v_a_1347_ = _args[0];
lean_object* v_a_1348_ = _args[1];
lean_object* v___x_1349_ = _args[2];
lean_object* v_a_1350_ = _args[3];
lean_object* v_mvarCounter_1351_ = _args[4];
lean_object* v___x_1352_ = _args[5];
lean_object* v___x_1353_ = _args[6];
lean_object* v___x_1354_ = _args[7];
lean_object* v_useReducible_1355_ = _args[8];
lean_object* v___x_1356_ = _args[9];
lean_object* v___y_1357_ = _args[10];
lean_object* v___y_1358_ = _args[11];
lean_object* v___y_1359_ = _args[12];
lean_object* v___y_1360_ = _args[13];
lean_object* v___y_1361_ = _args[14];
lean_object* v___y_1362_ = _args[15];
lean_object* v___y_1363_ = _args[16];
lean_object* v___y_1364_ = _args[17];
lean_object* v___y_1365_ = _args[18];
_start:
{
uint8_t v___x_93938__boxed_1366_; uint8_t v___x_93941__boxed_1367_; uint8_t v_useReducible_boxed_1368_; uint8_t v___x_93943__boxed_1369_; lean_object* v_res_1370_; 
v___x_93938__boxed_1366_ = lean_unbox(v___x_1349_);
v___x_93941__boxed_1367_ = lean_unbox(v___x_1353_);
v_useReducible_boxed_1368_ = lean_unbox(v_useReducible_1355_);
v___x_93943__boxed_1369_ = lean_unbox(v___x_1356_);
v_res_1370_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1347_, v_a_1348_, v___x_93938__boxed_1366_, v_a_1350_, v_mvarCounter_1351_, v___x_1352_, v___x_93941__boxed_1367_, v___x_1354_, v_useReducible_boxed_1368_, v___x_93943__boxed_1369_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v_mvarCounter_1351_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_infoState_1382_; lean_object* v_env_1383_; lean_object* v_nextMacroScope_1384_; lean_object* v_ngen_1385_; lean_object* v_auxDeclNGen_1386_; lean_object* v_traceState_1387_; lean_object* v_cache_1388_; lean_object* v_recordedDeps_1389_; lean_object* v_messages_1390_; lean_object* v_snapshotTasks_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1412_; 
v___x_1381_ = lean_st_ref_take(v___y_1379_);
v_infoState_1382_ = lean_ctor_get(v___x_1381_, 8);
v_env_1383_ = lean_ctor_get(v___x_1381_, 0);
v_nextMacroScope_1384_ = lean_ctor_get(v___x_1381_, 1);
v_ngen_1385_ = lean_ctor_get(v___x_1381_, 2);
v_auxDeclNGen_1386_ = lean_ctor_get(v___x_1381_, 3);
v_traceState_1387_ = lean_ctor_get(v___x_1381_, 4);
v_cache_1388_ = lean_ctor_get(v___x_1381_, 5);
v_recordedDeps_1389_ = lean_ctor_get(v___x_1381_, 6);
v_messages_1390_ = lean_ctor_get(v___x_1381_, 7);
v_snapshotTasks_1391_ = lean_ctor_get(v___x_1381_, 9);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1393_ = v___x_1381_;
v_isShared_1394_ = v_isSharedCheck_1412_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_snapshotTasks_1391_);
lean_inc(v_infoState_1382_);
lean_inc(v_messages_1390_);
lean_inc(v_recordedDeps_1389_);
lean_inc(v_cache_1388_);
lean_inc(v_traceState_1387_);
lean_inc(v_auxDeclNGen_1386_);
lean_inc(v_ngen_1385_);
lean_inc(v_nextMacroScope_1384_);
lean_inc(v_env_1383_);
lean_dec(v___x_1381_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1412_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v_enabled_1395_; lean_object* v_assignment_1396_; lean_object* v_lazyAssignment_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1410_; 
v_enabled_1395_ = lean_ctor_get_uint8(v_infoState_1382_, sizeof(void*)*3);
v_assignment_1396_ = lean_ctor_get(v_infoState_1382_, 0);
v_lazyAssignment_1397_ = lean_ctor_get(v_infoState_1382_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_infoState_1382_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v_infoState_1382_, 2);
lean_dec(v_unused_1411_);
v___x_1399_ = v_infoState_1382_;
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_lazyAssignment_1397_);
lean_inc(v_assignment_1396_);
lean_dec(v_infoState_1382_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1401_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 2, v_a_1371_);
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_assignment_1396_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_lazyAssignment_1397_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_a_1371_);
lean_ctor_set_uint8(v_reuseFailAlloc_1409_, sizeof(void*)*3, v_enabled_1395_);
v___x_1403_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 8, v___x_1403_);
v___x_1405_ = v___x_1393_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_env_1383_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_nextMacroScope_1384_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_ngen_1385_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_auxDeclNGen_1386_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_traceState_1387_);
lean_ctor_set(v_reuseFailAlloc_1408_, 5, v_cache_1388_);
lean_ctor_set(v_reuseFailAlloc_1408_, 6, v_recordedDeps_1389_);
lean_ctor_set(v_reuseFailAlloc_1408_, 7, v_messages_1390_);
lean_ctor_set(v_reuseFailAlloc_1408_, 8, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1408_, 9, v_snapshotTasks_1391_);
v___x_1405_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_st_ref_put(v___y_1379_, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1401_);
return v___x_1407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1424_, lean_object* v_mkInfoTree_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v_a_1433_, lean_object* v_a_x3f_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v_infoState_1437_; lean_object* v_trees_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_st_ref_get(v___y_1424_);
v_infoState_1437_ = lean_ctor_get(v___x_1436_, 8);
lean_inc_ref(v_infoState_1437_);
lean_dec(v___x_1436_);
v_trees_1438_ = lean_ctor_get(v_infoState_1437_, 2);
lean_inc_ref(v_trees_1438_);
lean_dec_ref(v_infoState_1437_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1432_);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
v___x_1439_ = lean_apply_10(v_mkInfoTree_1425_, v_trees_1438_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1424_, lean_box(0));
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1479_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1479_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1479_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v_infoState_1445_; lean_object* v_env_1446_; lean_object* v_nextMacroScope_1447_; lean_object* v_ngen_1448_; lean_object* v_auxDeclNGen_1449_; lean_object* v_traceState_1450_; lean_object* v_cache_1451_; lean_object* v_recordedDeps_1452_; lean_object* v_messages_1453_; lean_object* v_snapshotTasks_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1478_; 
v___x_1444_ = lean_st_ref_take(v___y_1424_);
v_infoState_1445_ = lean_ctor_get(v___x_1444_, 8);
v_env_1446_ = lean_ctor_get(v___x_1444_, 0);
v_nextMacroScope_1447_ = lean_ctor_get(v___x_1444_, 1);
v_ngen_1448_ = lean_ctor_get(v___x_1444_, 2);
v_auxDeclNGen_1449_ = lean_ctor_get(v___x_1444_, 3);
v_traceState_1450_ = lean_ctor_get(v___x_1444_, 4);
v_cache_1451_ = lean_ctor_get(v___x_1444_, 5);
v_recordedDeps_1452_ = lean_ctor_get(v___x_1444_, 6);
v_messages_1453_ = lean_ctor_get(v___x_1444_, 7);
v_snapshotTasks_1454_ = lean_ctor_get(v___x_1444_, 9);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1456_ = v___x_1444_;
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_snapshotTasks_1454_);
lean_inc(v_infoState_1445_);
lean_inc(v_messages_1453_);
lean_inc(v_recordedDeps_1452_);
lean_inc(v_cache_1451_);
lean_inc(v_traceState_1450_);
lean_inc(v_auxDeclNGen_1449_);
lean_inc(v_ngen_1448_);
lean_inc(v_nextMacroScope_1447_);
lean_inc(v_env_1446_);
lean_dec(v___x_1444_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1478_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
uint8_t v_enabled_1458_; lean_object* v_assignment_1459_; lean_object* v_lazyAssignment_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1476_; 
v_enabled_1458_ = lean_ctor_get_uint8(v_infoState_1445_, sizeof(void*)*3);
v_assignment_1459_ = lean_ctor_get(v_infoState_1445_, 0);
v_lazyAssignment_1460_ = lean_ctor_get(v_infoState_1445_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_infoState_1445_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_infoState_1445_, 2);
lean_dec(v_unused_1477_);
v___x_1462_ = v_infoState_1445_;
v_isShared_1463_ = v_isSharedCheck_1476_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_lazyAssignment_1460_);
lean_inc(v_assignment_1459_);
lean_dec(v_infoState_1445_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1476_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1464_ = lean_box(0);
v___x_1465_ = l_Lean_PersistentArray_push___redArg(v_a_1433_, v_a_1440_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 2, v___x_1465_);
v___x_1467_ = v___x_1462_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_assignment_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_lazyAssignment_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v___x_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*3, v_enabled_1458_);
v___x_1467_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 8, v___x_1467_);
v___x_1469_ = v___x_1456_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_env_1446_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_nextMacroScope_1447_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_ngen_1448_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_auxDeclNGen_1449_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v_traceState_1450_);
lean_ctor_set(v_reuseFailAlloc_1474_, 5, v_cache_1451_);
lean_ctor_set(v_reuseFailAlloc_1474_, 6, v_recordedDeps_1452_);
lean_ctor_set(v_reuseFailAlloc_1474_, 7, v_messages_1453_);
lean_ctor_set(v_reuseFailAlloc_1474_, 8, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1474_, 9, v_snapshotTasks_1454_);
v___x_1469_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_st_ref_put(v___y_1424_, v___x_1469_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1464_);
v___x_1472_ = v___x_1442_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1464_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_a_1433_);
v_a_1480_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1439_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1439_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1488_, lean_object* v_mkInfoTree_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v_a_1497_, lean_object* v_a_x3f_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1488_, v_mkInfoTree_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v_a_1497_, v_a_x3f_1498_);
lean_dec(v_a_x3f_1498_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1488_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1501_, lean_object* v_mkInfoTree_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v_infoState_1513_; uint8_t v_enabled_1514_; 
v___x_1512_ = lean_st_ref_get(v___y_1510_);
v_infoState_1513_ = lean_ctor_get(v___x_1512_, 8);
lean_inc_ref(v_infoState_1513_);
lean_dec(v___x_1512_);
v_enabled_1514_ = lean_ctor_get_uint8(v_infoState_1513_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1513_);
if (v_enabled_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_dec_ref(v_mkInfoTree_1502_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
v___x_1515_ = lean_apply_9(v_x_1501_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, lean_box(0));
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; lean_object* v_a_1517_; lean_object* v_r_1518_; 
v___x_1516_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1510_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
v_r_1518_ = lean_apply_9(v_x_1501_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, lean_box(0));
if (lean_obj_tag(v_r_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1543_; 
v_a_1519_ = lean_ctor_get(v_r_1518_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_r_1518_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1521_ = v_r_1518_;
v_isShared_1522_ = v_isSharedCheck_1543_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v_r_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1543_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
lean_inc(v_a_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set_tag(v___x_1521_, 1);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1510_, v_mkInfoTree_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v_a_1517_, v___x_1524_);
lean_dec_ref(v___x_1524_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v___x_1525_, 0);
lean_dec(v_unused_1533_);
v___x_1527_ = v___x_1525_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v___x_1525_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v_a_1519_);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1519_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_a_1519_);
v_a_1534_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1525_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1525_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_a_1544_ = lean_ctor_get(v_r_1518_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v_r_1518_, 1);
v___x_1545_ = lean_box(0);
v___x_1546_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1510_, v_mkInfoTree_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v_a_1517_, v___x_1545_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v___x_1546_, 0);
lean_dec(v_unused_1554_);
v___x_1548_ = v___x_1546_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v___x_1546_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 1);
lean_ctor_set(v___x_1548_, 0, v_a_1544_);
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1544_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_a_1544_);
v_a_1555_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1546_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1546_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1563_, lean_object* v_mkInfoTree_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1563_, v_mkInfoTree_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_ref_1581_; lean_object* v___x_1582_; lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1591_; 
v_ref_1581_ = lean_ctor_get(v___y_1578_, 2);
v___x_1582_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_inc(v_ref_1581_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_ref_1581_);
lean_ctor_set(v___x_1587_, 1, v_a_1583_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 1);
lean_ctor_set(v___x_1585_, 0, v___x_1587_);
v___x_1589_ = v___x_1585_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(lean_object* v_a_1599_, lean_object* v_x_1600_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 0)
{
uint8_t v___x_1601_; 
v___x_1601_ = 0;
return v___x_1601_;
}
else
{
lean_object* v_key_1602_; lean_object* v_tail_1603_; uint8_t v___x_1604_; 
v_key_1602_ = lean_ctor_get(v_x_1600_, 0);
v_tail_1603_ = lean_ctor_get(v_x_1600_, 2);
v___x_1604_ = lean_expr_eqv(v_key_1602_, v_a_1599_);
if (v___x_1604_ == 0)
{
v_x_1600_ = v_tail_1603_;
goto _start;
}
else
{
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_a_1606_, lean_object* v_x_1607_){
_start:
{
uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_res_1608_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1606_, v_x_1607_);
lean_dec(v_x_1607_);
lean_dec_ref(v_a_1606_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
if (lean_obj_tag(v_x_1611_) == 0)
{
return v_x_1610_;
}
else
{
lean_object* v_key_1612_; lean_object* v_value_1613_; lean_object* v_tail_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1637_; 
v_key_1612_ = lean_ctor_get(v_x_1611_, 0);
v_value_1613_ = lean_ctor_get(v_x_1611_, 1);
v_tail_1614_ = lean_ctor_get(v_x_1611_, 2);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_x_1611_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1616_ = v_x_1611_;
v_isShared_1617_ = v_isSharedCheck_1637_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_tail_1614_);
lean_inc(v_value_1613_);
lean_inc(v_key_1612_);
lean_dec(v_x_1611_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1637_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; uint64_t v___x_1619_; uint64_t v___x_1620_; uint64_t v___x_1621_; uint64_t v_fold_1622_; uint64_t v___x_1623_; uint64_t v___x_1624_; uint64_t v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1618_ = lean_array_get_size(v_x_1610_);
v___x_1619_ = l_Lean_Expr_hash(v_key_1612_);
v___x_1620_ = 32ULL;
v___x_1621_ = lean_uint64_shift_right(v___x_1619_, v___x_1620_);
v_fold_1622_ = lean_uint64_xor(v___x_1619_, v___x_1621_);
v___x_1623_ = 16ULL;
v___x_1624_ = lean_uint64_shift_right(v_fold_1622_, v___x_1623_);
v___x_1625_ = lean_uint64_xor(v_fold_1622_, v___x_1624_);
v___x_1626_ = lean_uint64_to_usize(v___x_1625_);
v___x_1627_ = lean_usize_of_nat(v___x_1618_);
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_sub(v___x_1627_, v___x_1628_);
v___x_1630_ = lean_usize_land(v___x_1626_, v___x_1629_);
v___x_1631_ = lean_array_uget_borrowed(v_x_1610_, v___x_1630_);
lean_inc(v___x_1631_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 2, v___x_1631_);
v___x_1633_ = v___x_1616_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_key_1612_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_value_1613_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_array_uset(v_x_1610_, v___x_1630_, v___x_1633_);
v_x_1610_ = v___x_1634_;
v_x_1611_ = v_tail_1614_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(lean_object* v_i_1638_, lean_object* v_source_1639_, lean_object* v_target_1640_){
_start:
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = lean_array_get_size(v_source_1639_);
v___x_1642_ = lean_nat_dec_lt(v_i_1638_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_dec_ref(v_source_1639_);
lean_dec(v_i_1638_);
return v_target_1640_;
}
else
{
lean_object* v_es_1643_; lean_object* v___x_1644_; lean_object* v_source_1645_; lean_object* v_target_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_es_1643_ = lean_array_fget(v_source_1639_, v_i_1638_);
v___x_1644_ = lean_box(0);
v_source_1645_ = lean_array_fset(v_source_1639_, v_i_1638_, v___x_1644_);
v_target_1646_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_target_1640_, v_es_1643_);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_add(v_i_1638_, v___x_1647_);
lean_dec(v_i_1638_);
v_i_1638_ = v___x_1648_;
v_source_1639_ = v_source_1645_;
v_target_1640_ = v_target_1646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(lean_object* v_data_1650_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_nbuckets_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1651_ = lean_array_get_size(v_data_1650_);
v___x_1652_ = lean_unsigned_to_nat(2u);
v_nbuckets_1653_ = lean_nat_mul(v___x_1651_, v___x_1652_);
v___x_1654_ = lean_unsigned_to_nat(0u);
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_mk_array(v_nbuckets_1653_, v___x_1655_);
v___x_1657_ = lean_array_propagate_mark(v_data_1650_, v___x_1656_);
v___x_1658_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v___x_1654_, v_data_1650_, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(lean_object* v_m_1659_, lean_object* v_a_1660_, lean_object* v_b_1661_){
_start:
{
lean_object* v_size_1662_; lean_object* v_buckets_1663_; lean_object* v___x_1664_; uint64_t v___x_1665_; uint64_t v___x_1666_; uint64_t v___x_1667_; uint64_t v_fold_1668_; uint64_t v___x_1669_; uint64_t v___x_1670_; uint64_t v___x_1671_; size_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; lean_object* v_bkt_1677_; uint8_t v___x_1678_; 
v_size_1662_ = lean_ctor_get(v_m_1659_, 0);
v_buckets_1663_ = lean_ctor_get(v_m_1659_, 1);
v___x_1664_ = lean_array_get_size(v_buckets_1663_);
v___x_1665_ = l_Lean_Expr_hash(v_a_1660_);
v___x_1666_ = 32ULL;
v___x_1667_ = lean_uint64_shift_right(v___x_1665_, v___x_1666_);
v_fold_1668_ = lean_uint64_xor(v___x_1665_, v___x_1667_);
v___x_1669_ = 16ULL;
v___x_1670_ = lean_uint64_shift_right(v_fold_1668_, v___x_1669_);
v___x_1671_ = lean_uint64_xor(v_fold_1668_, v___x_1670_);
v___x_1672_ = lean_uint64_to_usize(v___x_1671_);
v___x_1673_ = lean_usize_of_nat(v___x_1664_);
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_sub(v___x_1673_, v___x_1674_);
v___x_1676_ = lean_usize_land(v___x_1672_, v___x_1675_);
v_bkt_1677_ = lean_array_uget_borrowed(v_buckets_1663_, v___x_1676_);
v___x_1678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1660_, v_bkt_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1699_; 
lean_inc_ref(v_buckets_1663_);
lean_inc(v_size_1662_);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_m_1659_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1700_ = lean_ctor_get(v_m_1659_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_m_1659_, 0);
lean_dec(v_unused_1701_);
v___x_1680_ = v_m_1659_;
v_isShared_1681_ = v_isSharedCheck_1699_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v_m_1659_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1699_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v_size_x27_1683_; lean_object* v___x_1684_; lean_object* v_buckets_x27_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1682_ = lean_unsigned_to_nat(1u);
v_size_x27_1683_ = lean_nat_add(v_size_1662_, v___x_1682_);
lean_dec(v_size_1662_);
lean_inc(v_bkt_1677_);
v___x_1684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1684_, 0, v_a_1660_);
lean_ctor_set(v___x_1684_, 1, v_b_1661_);
lean_ctor_set(v___x_1684_, 2, v_bkt_1677_);
v_buckets_x27_1685_ = lean_array_uset(v_buckets_1663_, v___x_1676_, v___x_1684_);
v___x_1686_ = lean_unsigned_to_nat(4u);
v___x_1687_ = lean_nat_mul(v_size_x27_1683_, v___x_1686_);
v___x_1688_ = lean_unsigned_to_nat(3u);
v___x_1689_ = lean_nat_div(v___x_1687_, v___x_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_array_get_size(v_buckets_x27_1685_);
v___x_1691_ = lean_nat_dec_le(v___x_1689_, v___x_1690_);
lean_dec(v___x_1689_);
if (v___x_1691_ == 0)
{
lean_object* v_val_1692_; lean_object* v___x_1694_; 
v_val_1692_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_buckets_x27_1685_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_val_1692_);
lean_ctor_set(v___x_1680_, 0, v_size_x27_1683_);
v___x_1694_ = v___x_1680_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_size_x27_1683_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_val_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
else
{
lean_object* v___x_1697_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_buckets_x27_1685_);
lean_ctor_set(v___x_1680_, 0, v_size_x27_1683_);
v___x_1697_ = v___x_1680_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_size_x27_1683_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_buckets_x27_1685_);
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
else
{
lean_dec(v_b_1661_);
lean_dec_ref(v_a_1660_);
return v_m_1659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(lean_object* v_mvarId_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v_mctx_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1706_ = lean_st_ref_get(v___y_1704_);
v_mctx_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc_ref(v_mctx_1707_);
lean_dec(v___x_1706_);
v___x_1708_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1707_, v_mvarId_1702_);
lean_dec_ref(v_mctx_1707_);
v___x_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___y_1703_);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_mvarId_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec(v_mvarId_1712_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(lean_object* v_mvarId_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v_mctx_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1721_ = lean_st_ref_get(v___y_1719_);
v_mctx_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc_ref(v_mctx_1722_);
lean_dec(v___x_1721_);
v___x_1723_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1722_, v_mvarId_1717_);
lean_dec_ref(v_mctx_1722_);
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set(v___x_1725_, 1, v___y_1718_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg___boxed(lean_object* v_mvarId_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec(v_mvarId_1727_);
return v_res_1731_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(lean_object* v_m_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_buckets_1734_; lean_object* v___x_1735_; uint64_t v___x_1736_; uint64_t v___x_1737_; uint64_t v___x_1738_; uint64_t v_fold_1739_; uint64_t v___x_1740_; uint64_t v___x_1741_; uint64_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_buckets_1734_ = lean_ctor_get(v_m_1732_, 1);
v___x_1735_ = lean_array_get_size(v_buckets_1734_);
v___x_1736_ = l_Lean_Expr_hash(v_a_1733_);
v___x_1737_ = 32ULL;
v___x_1738_ = lean_uint64_shift_right(v___x_1736_, v___x_1737_);
v_fold_1739_ = lean_uint64_xor(v___x_1736_, v___x_1738_);
v___x_1740_ = 16ULL;
v___x_1741_ = lean_uint64_shift_right(v_fold_1739_, v___x_1740_);
v___x_1742_ = lean_uint64_xor(v_fold_1739_, v___x_1741_);
v___x_1743_ = lean_uint64_to_usize(v___x_1742_);
v___x_1744_ = lean_usize_of_nat(v___x_1735_);
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_sub(v___x_1744_, v___x_1745_);
v___x_1747_ = lean_usize_land(v___x_1743_, v___x_1746_);
v___x_1748_ = lean_array_uget_borrowed(v_buckets_1734_, v___x_1747_);
v___x_1749_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1733_, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_m_1750_, lean_object* v_a_1751_){
_start:
{
uint8_t v_res_1752_; lean_object* v_r_1753_; 
v_res_1752_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_1750_, v_a_1751_);
lean_dec_ref(v_a_1751_);
lean_dec_ref(v_m_1750_);
v_r_1753_ = lean_box(v_res_1752_);
return v_r_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(lean_object* v_mvarId_1758_, lean_object* v_e_1759_, lean_object* v_a_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_d_1771_; lean_object* v_b_1772_; lean_object* v___y_1773_; uint8_t v___x_1779_; 
v___x_1779_ = l_Lean_Expr_hasExprMVar(v_e_1759_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v_e_1759_);
v___x_1780_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v_a_1760_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
else
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_a_1760_, v_e_1759_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_box(0);
lean_inc_ref(v_e_1759_);
v___x_1785_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_a_1760_, v_e_1759_, v___x_1784_);
switch(lean_obj_tag(v_e_1759_))
{
case 11:
{
lean_object* v_struct_1786_; 
v_struct_1786_ = lean_ctor_get(v_e_1759_, 2);
lean_inc_ref(v_struct_1786_);
lean_dec_ref_known(v_e_1759_, 3);
v_e_1759_ = v_struct_1786_;
v_a_1760_ = v___x_1785_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1788_; lean_object* v_body_1789_; 
v_binderType_1788_ = lean_ctor_get(v_e_1759_, 1);
lean_inc_ref(v_binderType_1788_);
v_body_1789_ = lean_ctor_get(v_e_1759_, 2);
lean_inc_ref(v_body_1789_);
lean_dec_ref_known(v_e_1759_, 3);
v_d_1771_ = v_binderType_1788_;
v_b_1772_ = v_body_1789_;
v___y_1773_ = v___x_1785_;
goto v___jp_1770_;
}
case 6:
{
lean_object* v_binderType_1790_; lean_object* v_body_1791_; 
v_binderType_1790_ = lean_ctor_get(v_e_1759_, 1);
lean_inc_ref(v_binderType_1790_);
v_body_1791_ = lean_ctor_get(v_e_1759_, 2);
lean_inc_ref(v_body_1791_);
lean_dec_ref_known(v_e_1759_, 3);
v_d_1771_ = v_binderType_1790_;
v_b_1772_ = v_body_1791_;
v___y_1773_ = v___x_1785_;
goto v___jp_1770_;
}
case 8:
{
lean_object* v_type_1792_; lean_object* v_value_1793_; lean_object* v_body_1794_; lean_object* v___x_1795_; 
v_type_1792_ = lean_ctor_get(v_e_1759_, 1);
lean_inc_ref(v_type_1792_);
v_value_1793_ = lean_ctor_get(v_e_1759_, 2);
lean_inc_ref(v_value_1793_);
v_body_1794_ = lean_ctor_get(v_e_1759_, 3);
lean_inc_ref(v_body_1794_);
lean_dec_ref_known(v_e_1759_, 4);
v___x_1795_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1758_, v_type_1792_, v___x_1785_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v_fst_1797_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_fst_1797_ = lean_ctor_get(v_a_1796_, 0);
if (lean_obj_tag(v_fst_1797_) == 0)
{
lean_dec_ref(v_body_1794_);
lean_dec_ref(v_value_1793_);
return v___x_1795_;
}
else
{
lean_object* v_snd_1798_; lean_object* v___x_1799_; 
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v_snd_1798_ = lean_ctor_get(v_a_1796_, 1);
lean_inc(v_snd_1798_);
lean_dec(v_a_1796_);
v___x_1799_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1758_, v_value_1793_, v_snd_1798_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v_fst_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_fst_1801_ = lean_ctor_get(v_a_1800_, 0);
if (lean_obj_tag(v_fst_1801_) == 0)
{
lean_dec_ref(v_body_1794_);
return v___x_1799_;
}
else
{
lean_object* v_snd_1802_; 
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v_snd_1802_ = lean_ctor_get(v_a_1800_, 1);
lean_inc(v_snd_1802_);
lean_dec(v_a_1800_);
v_e_1759_ = v_body_1794_;
v_a_1760_ = v_snd_1802_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1794_);
return v___x_1799_;
}
}
}
else
{
lean_dec_ref(v_body_1794_);
lean_dec_ref(v_value_1793_);
return v___x_1795_;
}
}
case 10:
{
lean_object* v_expr_1804_; 
v_expr_1804_ = lean_ctor_get(v_e_1759_, 1);
lean_inc_ref(v_expr_1804_);
lean_dec_ref_known(v_e_1759_, 2);
v_e_1759_ = v_expr_1804_;
v_a_1760_ = v___x_1785_;
goto _start;
}
case 5:
{
lean_object* v_fn_1806_; lean_object* v_arg_1807_; lean_object* v___x_1808_; 
v_fn_1806_ = lean_ctor_get(v_e_1759_, 0);
lean_inc_ref(v_fn_1806_);
v_arg_1807_ = lean_ctor_get(v_e_1759_, 1);
lean_inc_ref(v_arg_1807_);
lean_dec_ref_known(v_e_1759_, 2);
v___x_1808_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1758_, v_fn_1806_, v___x_1785_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v_fst_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_fst_1810_ = lean_ctor_get(v_a_1809_, 0);
if (lean_obj_tag(v_fst_1810_) == 0)
{
lean_dec_ref(v_arg_1807_);
return v___x_1808_;
}
else
{
lean_object* v_snd_1811_; 
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v_snd_1811_ = lean_ctor_get(v_a_1809_, 1);
lean_inc(v_snd_1811_);
lean_dec(v_a_1809_);
v_e_1759_ = v_arg_1807_;
v_a_1760_ = v_snd_1811_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1807_);
return v___x_1808_;
}
}
case 2:
{
lean_object* v_mvarId_1813_; lean_object* v___x_1814_; 
v_mvarId_1813_ = lean_ctor_get(v_e_1759_, 0);
lean_inc(v_mvarId_1813_);
lean_dec_ref_known(v_e_1759_, 1);
v___x_1814_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1758_, v_mvarId_1813_, v___x_1785_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1814_;
}
default: 
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec_ref(v_e_1759_);
v___x_1815_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v___x_1785_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref(v_e_1759_);
v___x_1818_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v_a_1760_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
v___jp_1770_:
{
lean_object* v___x_1774_; 
v___x_1774_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1758_, v_d_1771_, v___y_1773_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v_fst_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_fst_1776_ = lean_ctor_get(v_a_1775_, 0);
if (lean_obj_tag(v_fst_1776_) == 0)
{
lean_dec_ref(v_b_1772_);
return v___x_1774_;
}
else
{
lean_object* v_snd_1777_; 
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v_snd_1777_ = lean_ctor_get(v_a_1775_, 1);
lean_inc(v_snd_1777_);
lean_dec(v_a_1775_);
v_e_1759_ = v_b_1772_;
v_a_1760_ = v_snd_1777_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1772_);
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(lean_object* v_mvarId_1821_, lean_object* v_mvarId_x27_1822_, lean_object* v_a_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Lean_instBEqMVarId_beq(v_mvarId_1821_, v_mvarId_x27_1822_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_x27_1822_, v_a_1823_, v___y_1829_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1918_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1918_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1918_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_fst_1839_; 
v_fst_1839_ = lean_ctor_get(v_a_1835_, 0);
lean_inc(v_fst_1839_);
if (lean_obj_tag(v_fst_1839_) == 0)
{
lean_object* v_snd_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_mvarId_x27_1822_);
v_snd_1840_ = lean_ctor_get(v_a_1835_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_a_1835_, 0);
lean_dec(v_unused_1859_);
v___x_1842_ = v_a_1835_;
v_isShared_1843_ = v_isSharedCheck_1858_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_snd_1840_);
lean_dec(v_a_1835_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1858_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1857_; 
v_a_1844_ = lean_ctor_get(v_fst_1839_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_fst_1839_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1846_ = v_fst_1839_;
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v_fst_1839_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1857_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1849_);
v___x_1851_ = v___x_1842_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_snd_1840_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1851_);
v___x_1853_ = v___x_1837_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
else
{
lean_object* v_a_1860_; 
lean_del_object(v___x_1837_);
v_a_1860_ = lean_ctor_get(v_fst_1839_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v_fst_1839_, 1);
if (lean_obj_tag(v_a_1860_) == 0)
{
lean_object* v_snd_1861_; lean_object* v___x_1862_; 
v_snd_1861_ = lean_ctor_get(v_a_1835_, 1);
lean_inc(v_snd_1861_);
lean_dec(v_a_1835_);
v___x_1862_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_x27_1822_, v_snd_1861_, v___y_1829_);
lean_dec(v_mvarId_x27_1822_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1906_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1906_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1906_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_fst_1867_; 
v_fst_1867_ = lean_ctor_get(v_a_1863_, 0);
lean_inc(v_fst_1867_);
if (lean_obj_tag(v_fst_1867_) == 0)
{
lean_object* v_snd_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1886_; 
v_snd_1868_ = lean_ctor_get(v_a_1863_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_a_1863_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v_a_1863_, 0);
lean_dec(v_unused_1887_);
v___x_1870_ = v_a_1863_;
v_isShared_1871_ = v_isSharedCheck_1886_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snd_1868_);
lean_dec(v_a_1863_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1886_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1885_; 
v_a_1872_ = lean_ctor_get(v_fst_1867_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_fst_1867_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1874_ = v_fst_1867_;
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v_fst_1867_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1879_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1877_);
v___x_1879_ = v___x_1870_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_snd_1868_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1879_);
v___x_1881_ = v___x_1865_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
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
}
}
else
{
lean_object* v_a_1888_; 
v_a_1888_ = lean_ctor_get(v_fst_1867_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v_fst_1867_, 1);
if (lean_obj_tag(v_a_1888_) == 0)
{
lean_object* v_snd_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1900_; 
v_snd_1889_ = lean_ctor_get(v_a_1863_, 1);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_a_1863_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v_a_1863_, 0);
lean_dec(v_unused_1901_);
v___x_1891_ = v_a_1863_;
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snd_1889_);
lean_dec(v_a_1863_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_snd_1889_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1895_);
v___x_1897_ = v___x_1865_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
else
{
lean_object* v_val_1902_; lean_object* v_snd_1903_; lean_object* v_mvarIdPending_1904_; 
lean_del_object(v___x_1865_);
v_val_1902_ = lean_ctor_get(v_a_1888_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_a_1888_, 1);
v_snd_1903_ = lean_ctor_get(v_a_1863_, 1);
lean_inc(v_snd_1903_);
lean_dec(v_a_1863_);
v_mvarIdPending_1904_ = lean_ctor_get(v_val_1902_, 1);
lean_inc(v_mvarIdPending_1904_);
lean_dec(v_val_1902_);
v_mvarId_x27_1822_ = v_mvarIdPending_1904_;
v_a_1823_ = v_snd_1903_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1862_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1862_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_snd_1915_; lean_object* v_val_1916_; lean_object* v___x_1917_; 
lean_dec(v_mvarId_x27_1822_);
v_snd_1915_ = lean_ctor_get(v_a_1835_, 1);
lean_inc(v_snd_1915_);
lean_dec(v_a_1835_);
v_val_1916_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_a_1860_, 1);
v___x_1917_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1821_, v_val_1916_, v_snd_1915_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_mvarId_x27_1822_);
v_a_1919_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1834_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1834_);
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
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_dec(v_mvarId_x27_1822_);
v___x_1927_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1));
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
lean_ctor_set(v___x_1928_, 1, v_a_1823_);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___boxed(lean_object* v_mvarId_1930_, lean_object* v_mvarId_x27_1931_, lean_object* v_a_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1930_, v_mvarId_x27_1931_, v_a_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v_mvarId_1930_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6___boxed(lean_object* v_mvarId_1943_, lean_object* v_e_1944_, lean_object* v_a_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1943_, v_e_1944_, v_a_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v_mvarId_1943_);
return v_res_1955_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_unsigned_to_nat(16u);
v___x_1958_ = lean_mk_array(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0);
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___x_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_mvarId_1962_, lean_object* v_e_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
uint8_t v___x_1973_; 
v___x_1973_ = l_Lean_Expr_hasExprMVar(v_e_1963_);
if (v___x_1973_ == 0)
{
uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec_ref(v_e_1963_);
v___x_1974_ = 1;
v___x_1975_ = lean_box(v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
return v___x_1976_;
}
else
{
uint8_t v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = 0;
v___x_1978_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
v___x_1979_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1962_, v_e_1963_, v___x_1978_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1993_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1993_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1993_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_fst_1984_; 
v_fst_1984_ = lean_ctor_get(v_a_1980_, 0);
lean_inc(v_fst_1984_);
lean_dec(v_a_1980_);
if (lean_obj_tag(v_fst_1984_) == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
lean_dec_ref_known(v_fst_1984_, 1);
v___x_1985_ = lean_box(v___x_1977_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1985_);
v___x_1987_ = v___x_1982_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec_ref_known(v_fst_1984_, 1);
v___x_1989_ = lean_box(v___x_1973_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1989_);
v___x_1991_ = v___x_1982_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1979_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1979_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_mvarId_2002_, lean_object* v_e_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_mvarId_2002_, v_e_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v_mvarId_2002_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(lean_object* v_x_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v_ks_2018_; lean_object* v_vs_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2043_; 
v_ks_2018_ = lean_ctor_get(v_x_2014_, 0);
v_vs_2019_ = lean_ctor_get(v_x_2014_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_x_2014_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2021_ = v_x_2014_;
v_isShared_2022_ = v_isSharedCheck_2043_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_vs_2019_);
lean_inc(v_ks_2018_);
lean_dec(v_x_2014_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2043_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = lean_array_get_size(v_ks_2018_);
v___x_2024_ = lean_nat_dec_lt(v_x_2015_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_dec(v_x_2015_);
v___x_2025_ = lean_array_push(v_ks_2018_, v_x_2016_);
v___x_2026_ = lean_array_push(v_vs_2019_, v_x_2017_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 1, v___x_2026_);
lean_ctor_set(v___x_2021_, 0, v___x_2025_);
v___x_2028_ = v___x_2021_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
else
{
lean_object* v_k_x27_2030_; uint8_t v___x_2031_; 
v_k_x27_2030_ = lean_array_fget_borrowed(v_ks_2018_, v_x_2015_);
v___x_2031_ = l_Lean_instBEqMVarId_beq(v_x_2016_, v_k_x27_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2033_; 
if (v_isShared_2022_ == 0)
{
v___x_2033_ = v___x_2021_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_ks_2018_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_vs_2019_);
v___x_2033_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_x_2015_, v___x_2034_);
lean_dec(v_x_2015_);
v_x_2014_ = v___x_2033_;
v_x_2015_ = v___x_2035_;
goto _start;
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = lean_array_fset(v_ks_2018_, v_x_2015_, v_x_2016_);
v___x_2039_ = lean_array_fset(v_vs_2019_, v_x_2015_, v_x_2017_);
lean_dec(v_x_2015_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 1, v___x_2039_);
lean_ctor_set(v___x_2021_, 0, v___x_2038_);
v___x_2041_ = v___x_2021_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2039_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_n_2044_, lean_object* v_k_2045_, lean_object* v_v_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_n_2044_, v___x_2047_, v_k_2045_, v_v_2046_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_x_2050_, size_t v_x_2051_, size_t v_x_2052_, lean_object* v_x_2053_, lean_object* v_x_2054_){
_start:
{
if (lean_obj_tag(v_x_2050_) == 0)
{
lean_object* v_es_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v_j_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_es_2055_ = lean_ctor_get(v_x_2050_, 0);
v___x_2056_ = ((size_t)31ULL);
v___x_2057_ = lean_usize_land(v_x_2051_, v___x_2056_);
v_j_2058_ = lean_usize_to_nat(v___x_2057_);
v___x_2059_ = lean_array_get_size(v_es_2055_);
v___x_2060_ = lean_nat_dec_lt(v_j_2058_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec(v_j_2058_);
lean_dec(v_x_2054_);
lean_dec(v_x_2053_);
return v_x_2050_;
}
else
{
lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2099_; 
lean_inc_ref(v_es_2055_);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_x_2050_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v_x_2050_, 0);
lean_dec(v_unused_2100_);
v___x_2062_ = v_x_2050_;
v_isShared_2063_ = v_isSharedCheck_2099_;
goto v_resetjp_2061_;
}
else
{
lean_dec(v_x_2050_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2099_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_v_2064_; lean_object* v___x_2065_; lean_object* v_xs_x27_2066_; lean_object* v___y_2068_; 
v_v_2064_ = lean_array_fget(v_es_2055_, v_j_2058_);
v___x_2065_ = lean_box(0);
v_xs_x27_2066_ = lean_array_fset(v_es_2055_, v_j_2058_, v___x_2065_);
switch(lean_obj_tag(v_v_2064_))
{
case 0:
{
lean_object* v_key_2073_; lean_object* v_val_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2084_; 
v_key_2073_ = lean_ctor_get(v_v_2064_, 0);
v_val_2074_ = lean_ctor_get(v_v_2064_, 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_v_2064_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2076_ = v_v_2064_;
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_val_2074_);
lean_inc(v_key_2073_);
lean_dec(v_v_2064_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Lean_instBEqMVarId_beq(v_x_2053_, v_key_2073_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_del_object(v___x_2076_);
v___x_2079_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2073_, v_val_2074_, v_x_2053_, v_x_2054_);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
v___y_2068_ = v___x_2080_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2082_; 
lean_dec(v_val_2074_);
lean_dec(v_key_2073_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v_x_2054_);
lean_ctor_set(v___x_2076_, 0, v_x_2053_);
v___x_2082_ = v___x_2076_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_x_2053_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_x_2054_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v___y_2068_ = v___x_2082_;
goto v___jp_2067_;
}
}
}
}
case 1:
{
lean_object* v_node_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2097_; 
v_node_2085_ = lean_ctor_get(v_v_2064_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_v_2064_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2087_ = v_v_2064_;
v_isShared_2088_ = v_isSharedCheck_2097_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_node_2085_);
lean_dec(v_v_2064_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2097_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
size_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2089_ = ((size_t)5ULL);
v___x_2090_ = lean_usize_shift_right(v_x_2051_, v___x_2089_);
v___x_2091_ = ((size_t)1ULL);
v___x_2092_ = lean_usize_add(v_x_2052_, v___x_2091_);
v___x_2093_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_node_2085_, v___x_2090_, v___x_2092_, v_x_2053_, v_x_2054_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2093_);
v___x_2095_ = v___x_2087_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
v___y_2068_ = v___x_2095_;
goto v___jp_2067_;
}
}
}
default: 
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v_x_2053_);
lean_ctor_set(v___x_2098_, 1, v_x_2054_);
v___y_2068_ = v___x_2098_;
goto v___jp_2067_;
}
}
v___jp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = lean_array_fset(v_xs_x27_2066_, v_j_2058_, v___y_2068_);
lean_dec(v_j_2058_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2069_);
v___x_2071_ = v___x_2062_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v_ks_2101_; lean_object* v_vs_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2120_; 
v_ks_2101_ = lean_ctor_get(v_x_2050_, 0);
v_vs_2102_ = lean_ctor_get(v_x_2050_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_x_2050_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2104_ = v_x_2050_;
v_isShared_2105_ = v_isSharedCheck_2120_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_vs_2102_);
lean_inc(v_ks_2101_);
lean_dec(v_x_2050_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2120_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_ks_2101_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_vs_2102_);
v___x_2107_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v_newNode_2108_; size_t v___x_2109_; uint8_t v___x_2110_; 
v_newNode_2108_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v___x_2107_, v_x_2053_, v_x_2054_);
v___x_2109_ = ((size_t)7ULL);
v___x_2110_ = lean_usize_dec_le(v___x_2109_, v_x_2052_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2108_);
v___x_2112_ = lean_unsigned_to_nat(4u);
v___x_2113_ = lean_nat_dec_lt(v___x_2111_, v___x_2112_);
lean_dec(v___x_2111_);
if (v___x_2113_ == 0)
{
lean_object* v_ks_2114_; lean_object* v_vs_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_ks_2114_ = lean_ctor_get(v_newNode_2108_, 0);
lean_inc_ref(v_ks_2114_);
v_vs_2115_ = lean_ctor_get(v_newNode_2108_, 1);
lean_inc_ref(v_vs_2115_);
lean_dec_ref(v_newNode_2108_);
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0);
v___x_2118_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_x_2052_, v_ks_2114_, v_vs_2115_, v___x_2116_, v___x_2117_);
lean_dec_ref(v_vs_2115_);
lean_dec_ref(v_ks_2114_);
return v___x_2118_;
}
else
{
return v_newNode_2108_;
}
}
else
{
return v_newNode_2108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(size_t v_depth_2121_, lean_object* v_keys_2122_, lean_object* v_vals_2123_, lean_object* v_i_2124_, lean_object* v_entries_2125_){
_start:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_array_get_size(v_keys_2122_);
v___x_2127_ = lean_nat_dec_lt(v_i_2124_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_dec(v_i_2124_);
return v_entries_2125_;
}
else
{
lean_object* v_k_2128_; lean_object* v_v_2129_; uint64_t v___x_2130_; size_t v_h_2131_; size_t v___x_2132_; lean_object* v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v_h_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_k_2128_ = lean_array_fget_borrowed(v_keys_2122_, v_i_2124_);
v_v_2129_ = lean_array_fget_borrowed(v_vals_2123_, v_i_2124_);
v___x_2130_ = l_Lean_instHashableMVarId_hash(v_k_2128_);
v_h_2131_ = lean_uint64_to_usize(v___x_2130_);
v___x_2132_ = ((size_t)5ULL);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_sub(v_depth_2121_, v___x_2134_);
v___x_2136_ = lean_usize_mul(v___x_2132_, v___x_2135_);
v_h_2137_ = lean_usize_shift_right(v_h_2131_, v___x_2136_);
v___x_2138_ = lean_nat_add(v_i_2124_, v___x_2133_);
lean_dec(v_i_2124_);
lean_inc(v_v_2129_);
lean_inc(v_k_2128_);
v___x_2139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_entries_2125_, v_h_2137_, v_depth_2121_, v_k_2128_, v_v_2129_);
v_i_2124_ = v___x_2138_;
v_entries_2125_ = v___x_2139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_depth_2141_, lean_object* v_keys_2142_, lean_object* v_vals_2143_, lean_object* v_i_2144_, lean_object* v_entries_2145_){
_start:
{
size_t v_depth_boxed_2146_; lean_object* v_res_2147_; 
v_depth_boxed_2146_ = lean_unbox_usize(v_depth_2141_);
lean_dec(v_depth_2141_);
v_res_2147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_boxed_2146_, v_keys_2142_, v_vals_2143_, v_i_2144_, v_entries_2145_);
lean_dec_ref(v_vals_2143_);
lean_dec_ref(v_keys_2142_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
size_t v_x_95447__boxed_2153_; size_t v_x_95448__boxed_2154_; lean_object* v_res_2155_; 
v_x_95447__boxed_2153_ = lean_unbox_usize(v_x_2149_);
lean_dec(v_x_2149_);
v_x_95448__boxed_2154_ = lean_unbox_usize(v_x_2150_);
lean_dec(v_x_2150_);
v_res_2155_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2148_, v_x_95447__boxed_2153_, v_x_95448__boxed_2154_, v_x_2151_, v_x_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
uint64_t v___x_2159_; size_t v___x_2160_; size_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2159_ = l_Lean_instHashableMVarId_hash(v_x_2157_);
v___x_2160_ = lean_uint64_to_usize(v___x_2159_);
v___x_2161_ = ((size_t)1ULL);
v___x_2162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2156_, v___x_2160_, v___x_2161_, v_x_2157_, v_x_2158_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(lean_object* v_mvarId_2163_, lean_object* v_val_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; lean_object* v_mctx_2168_; lean_object* v_cache_2169_; lean_object* v_zetaDeltaFVarIds_2170_; lean_object* v_postponed_2171_; lean_object* v_diag_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2201_; 
v___x_2167_ = lean_st_ref_take(v___y_2165_);
v_mctx_2168_ = lean_ctor_get(v___x_2167_, 0);
v_cache_2169_ = lean_ctor_get(v___x_2167_, 1);
v_zetaDeltaFVarIds_2170_ = lean_ctor_get(v___x_2167_, 2);
v_postponed_2171_ = lean_ctor_get(v___x_2167_, 3);
v_diag_2172_ = lean_ctor_get(v___x_2167_, 4);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2174_ = v___x_2167_;
v_isShared_2175_ = v_isSharedCheck_2201_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_diag_2172_);
lean_inc(v_postponed_2171_);
lean_inc(v_zetaDeltaFVarIds_2170_);
lean_inc(v_cache_2169_);
lean_inc(v_mctx_2168_);
lean_dec(v___x_2167_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2201_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_depth_2176_; lean_object* v_levelAssignDepth_2177_; lean_object* v_lmvarCounter_2178_; lean_object* v_mvarCounter_2179_; lean_object* v_lDecls_2180_; lean_object* v_decls_2181_; lean_object* v_userNames_2182_; lean_object* v_lAssignment_2183_; lean_object* v_eAssignment_2184_; lean_object* v_dAssignment_2185_; lean_object* v_instanceTypedMVars_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2200_; 
v_depth_2176_ = lean_ctor_get(v_mctx_2168_, 0);
v_levelAssignDepth_2177_ = lean_ctor_get(v_mctx_2168_, 1);
v_lmvarCounter_2178_ = lean_ctor_get(v_mctx_2168_, 2);
v_mvarCounter_2179_ = lean_ctor_get(v_mctx_2168_, 3);
v_lDecls_2180_ = lean_ctor_get(v_mctx_2168_, 4);
v_decls_2181_ = lean_ctor_get(v_mctx_2168_, 5);
v_userNames_2182_ = lean_ctor_get(v_mctx_2168_, 6);
v_lAssignment_2183_ = lean_ctor_get(v_mctx_2168_, 7);
v_eAssignment_2184_ = lean_ctor_get(v_mctx_2168_, 8);
v_dAssignment_2185_ = lean_ctor_get(v_mctx_2168_, 9);
v_instanceTypedMVars_2186_ = lean_ctor_get(v_mctx_2168_, 10);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_mctx_2168_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2188_ = v_mctx_2168_;
v_isShared_2189_ = v_isSharedCheck_2200_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_instanceTypedMVars_2186_);
lean_inc(v_dAssignment_2185_);
lean_inc(v_eAssignment_2184_);
lean_inc(v_lAssignment_2183_);
lean_inc(v_userNames_2182_);
lean_inc(v_decls_2181_);
lean_inc(v_lDecls_2180_);
lean_inc(v_mvarCounter_2179_);
lean_inc(v_lmvarCounter_2178_);
lean_inc(v_levelAssignDepth_2177_);
lean_inc(v_depth_2176_);
lean_dec(v_mctx_2168_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2200_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2190_ = lean_box(0);
v___x_2191_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_eAssignment_2184_, v_mvarId_2163_, v_val_2164_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 8, v___x_2191_);
v___x_2193_ = v___x_2188_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_depth_2176_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_levelAssignDepth_2177_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_lmvarCounter_2178_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_mvarCounter_2179_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_lDecls_2180_);
lean_ctor_set(v_reuseFailAlloc_2199_, 5, v_decls_2181_);
lean_ctor_set(v_reuseFailAlloc_2199_, 6, v_userNames_2182_);
lean_ctor_set(v_reuseFailAlloc_2199_, 7, v_lAssignment_2183_);
lean_ctor_set(v_reuseFailAlloc_2199_, 8, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2199_, 9, v_dAssignment_2185_);
lean_ctor_set(v_reuseFailAlloc_2199_, 10, v_instanceTypedMVars_2186_);
v___x_2193_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2195_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2193_);
v___x_2195_ = v___x_2174_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_cache_2169_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_zetaDeltaFVarIds_2170_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_postponed_2171_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_diag_2172_);
v___x_2195_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_st_ref_put(v___y_2165_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2190_);
return v___x_2197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg___boxed(lean_object* v_mvarId_2202_, lean_object* v_val_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_2202_, v_val_2203_, v___y_2204_);
lean_dec(v___y_2204_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_o_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_env_2212_; lean_object* v___x_2213_; lean_object* v_toEnvExtension_2214_; lean_object* v_asyncMode_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; lean_object* v_merged_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2227_; 
v___x_2210_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2211_ = lean_st_ref_get(v___y_2208_);
v_env_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc_ref(v_env_2212_);
lean_dec(v___x_2211_);
v___x_2213_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2214_ = lean_ctor_get(v___x_2213_, 0);
v_asyncMode_2215_ = lean_ctor_get(v_toEnvExtension_2214_, 2);
v___x_2216_ = lean_box(0);
v___x_2217_ = 0;
v___x_2218_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2210_, v___x_2213_, v_env_2212_, v_asyncMode_2215_, v___x_2216_, v___x_2217_);
v_merged_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v___x_2218_, 1);
lean_dec(v_unused_2228_);
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_merged_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2227_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v_merged_2219_);
lean_ctor_set(v___x_2221_, 0, v_o_2207_);
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_o_2207_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_merged_2219_);
v___x_2224_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg___boxed(lean_object* v_o_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_2229_, v___y_2230_);
lean_dec(v___y_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2239_);
v___x_2243_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v___x_2242_, v___y_2240_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2253_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2269_, lean_object* v_snd_2270_, uint8_t v___x_2271_, lean_object* v___x_2272_, uint8_t v___x_2273_, uint8_t v_useReducible_2274_, uint8_t v___x_2275_, lean_object* v___x_2276_, lean_object* v___x_2277_, lean_object* v_simprocs_2278_, lean_object* v_discharge_x3f_2279_, lean_object* v_snd_2280_, lean_object* v___f_2281_, lean_object* v___x_2282_, lean_object* v___x_2283_, lean_object* v___x_2284_, lean_object* v___x_2285_, lean_object* v___f_2286_, lean_object* v_a_2287_, lean_object* v___x_2288_, lean_object* v___f_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; 
if (lean_obj_tag(v_usingArg_2269_) == 1)
{
lean_object* v_val_2512_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___x_2564_; lean_object* v_infoState_2565_; uint8_t v_enabled_2566_; 
v_val_2512_ = lean_ctor_get(v_usingArg_2269_, 0);
lean_inc(v_val_2512_);
lean_dec_ref_known(v_usingArg_2269_, 1);
v___x_2564_ = lean_st_ref_get(v___y_2297_);
v_infoState_2565_ = lean_ctor_get(v___x_2564_, 8);
lean_inc_ref(v_infoState_2565_);
lean_dec(v___x_2564_);
v_enabled_2566_ = lean_ctor_get_uint8(v_infoState_2565_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2565_);
if (v_enabled_2566_ == 0)
{
lean_dec_ref(v___f_2289_);
v___y_2514_ = v___y_2290_;
v___y_2515_ = v___y_2291_;
v___y_2516_ = v___y_2292_;
v___y_2517_ = v___y_2293_;
v___y_2518_ = v___y_2294_;
v___y_2519_ = v___y_2295_;
v___y_2520_ = v___y_2296_;
v___y_2521_ = v___y_2297_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2567_; lean_object* v_a_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; 
v___x_2567_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2297_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___x_2567_);
v___f_2569_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2569_, 0, v_a_2568_);
v___x_2570_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2569_, v___f_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_dec_ref_known(v___x_2570_, 1);
v___y_2514_ = v___y_2290_;
v___y_2515_ = v___y_2291_;
v___y_2516_ = v___y_2292_;
v___y_2517_ = v___y_2293_;
v___y_2518_ = v___y_2294_;
v___y_2519_ = v___y_2295_;
v___y_2520_ = v___y_2296_;
v___y_2521_ = v___y_2297_;
goto v___jp_2513_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_val_2512_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
v___jp_2513_:
{
lean_object* v___x_2522_; lean_object* v_mctx_2523_; lean_object* v_mvarCounter_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2522_ = lean_st_ref_get(v___y_2519_);
v_mctx_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_ref(v_mctx_2523_);
lean_dec(v___x_2522_);
v_mvarCounter_2524_ = lean_ctor_get(v_mctx_2523_, 3);
lean_inc(v_mvarCounter_2524_);
lean_dec_ref(v_mctx_2523_);
v___x_2525_ = lean_box(0);
v___x_2526_ = l_Lean_Elab_Tactic_elabTerm(v_val_2512_, v___x_2525_, v___x_2271_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2528_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc_n(v_a_2527_, 2);
lean_dec_ref_known(v___x_2526_, 1);
v___x_2528_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_snd_2270_, v_a_2527_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; uint8_t v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = lean_unbox(v_a_2529_);
lean_dec(v_a_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_mvarCounter_2524_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
v___x_2531_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2532_ = l_Lean_indentExpr(v_a_2527_);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = l_Lean_Expr_mvar___override(v_snd_2270_);
v___x_2537_ = l_Lean_MessageData_ofExpr(v___x_2536_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2535_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2538_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
v___y_2364_ = v___x_2525_;
v___y_2365_ = v_mvarCounter_2524_;
v___y_2366_ = v_a_2527_;
v___y_2367_ = v___x_2525_;
v___y_2368_ = v___y_2514_;
v___y_2369_ = v___y_2515_;
v___y_2370_ = v___y_2516_;
v___y_2371_ = v___y_2517_;
v___y_2372_ = v___y_2518_;
v___y_2373_ = v___y_2519_;
v___y_2374_ = v___y_2520_;
v___y_2375_ = v___y_2521_;
goto v___jp_2363_;
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_a_2527_);
lean_dec(v_mvarCounter_2524_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2548_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2528_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2528_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_mvarCounter_2524_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2556_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2526_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2526_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
else
{
lean_object* v_lctx_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref(v___f_2289_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v___x_2272_);
lean_dec(v_usingArg_2269_);
v_lctx_2579_ = lean_ctor_get(v___y_2294_, 2);
v___x_2580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10));
v___x_2581_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2579_, v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 1)
{
lean_object* v_val_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_val_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_val_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = l_Lean_LocalDecl_fvarId(v_val_2582_);
lean_dec(v_val_2582_);
v___x_2584_ = lean_mk_empty_array_with_capacity(v___x_2276_);
v___x_2585_ = lean_array_push(v___x_2584_, v___x_2583_);
lean_inc_ref(v_snd_2280_);
v___x_2586_ = l_Lean_Meta_simpGoal(v_snd_2270_, v___x_2277_, v_simprocs_2278_, v_discharge_x3f_2279_, v___x_2273_, v___x_2585_, v_snd_2280_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2615_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2615_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2615_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_fst_2591_; 
v_fst_2591_ = lean_ctor_get(v_a_2587_, 0);
if (lean_obj_tag(v_fst_2591_) == 1)
{
lean_object* v_val_2592_; lean_object* v_snd_2593_; lean_object* v_snd_2594_; lean_object* v___x_2595_; 
lean_del_object(v___x_2589_);
lean_dec_ref(v_snd_2280_);
v_val_2592_ = lean_ctor_get(v_fst_2591_, 0);
lean_inc(v_val_2592_);
v_snd_2593_ = lean_ctor_get(v_a_2587_, 1);
lean_inc(v_snd_2593_);
lean_dec(v_a_2587_);
v_snd_2594_ = lean_ctor_get(v_val_2592_, 1);
lean_inc(v_snd_2594_);
lean_dec(v_val_2592_);
v___x_2595_ = l_Lean_MVarId_assumption(v_snd_2594_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v___x_2595_, 0);
lean_dec(v_unused_2603_);
v___x_2597_ = v___x_2595_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_dec(v___x_2595_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v_snd_2593_);
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_snd_2593_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_snd_2593_);
v_a_2604_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2595_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2595_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2587_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_snd_2280_);
v___x_2613_ = v___x_2589_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_snd_2280_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_snd_2280_);
v_a_2616_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2586_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2586_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v___x_2624_; 
lean_dec(v___x_2581_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
v___x_2624_ = l_Lean_MVarId_assumption(v_snd_2270_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v___x_2624_, 0);
lean_dec(v_unused_2632_);
v___x_2626_ = v___x_2624_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_dec(v___x_2624_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v_snd_2280_);
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_snd_2280_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v_snd_2280_);
v_a_2633_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2624_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2624_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
v___jp_2299_:
{
lean_object* v___x_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v___x_2303_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_snd_2270_, v___y_2300_, v___y_2302_);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v___x_2303_, 0);
lean_dec(v_unused_2311_);
v___x_2305_ = v___x_2303_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v___x_2303_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___y_2301_);
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___y_2301_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
v___jp_2312_:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Core_mkFreshUserName(v___y_2319_, v___y_2318_, v___y_2320_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc_n(v_a_2330_, 2);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = l_Lean_MVarId_rename(v___y_2324_, v___y_2328_, v_a_2330_, v___y_2322_, v___y_2327_, v___y_2318_, v___y_2320_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc_n(v_a_2332_, 2);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = lean_box(v___x_2271_);
v___x_2334_ = lean_box(v___x_2273_);
v___x_2335_ = lean_box(v_useReducible_2274_);
v___x_2336_ = lean_box(v___x_2275_);
v___f_2337_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2337_, 0, v_a_2332_);
lean_closure_set(v___f_2337_, 1, v_a_2330_);
lean_closure_set(v___f_2337_, 2, v___x_2333_);
lean_closure_set(v___f_2337_, 3, v___y_2315_);
lean_closure_set(v___f_2337_, 4, v___y_2314_);
lean_closure_set(v___f_2337_, 5, v___x_2272_);
lean_closure_set(v___f_2337_, 6, v___x_2334_);
lean_closure_set(v___f_2337_, 7, v___y_2313_);
lean_closure_set(v___f_2337_, 8, v___x_2335_);
lean_closure_set(v___f_2337_, 9, v___x_2336_);
v___x_2338_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_a_2332_, v___f_2337_, v___y_2325_, v___y_2326_, v___y_2321_, v___y_2316_, v___y_2322_, v___y_2327_, v___y_2318_, v___y_2320_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_dec_ref_known(v___x_2338_, 1);
v___y_2300_ = v___y_2317_;
v___y_2301_ = v___y_2323_;
v___y_2302_ = v___y_2327_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec_ref(v___y_2323_);
lean_dec_ref(v___y_2317_);
lean_dec(v_snd_2270_);
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_a_2330_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v___y_2317_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2347_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2331_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2331_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v___y_2328_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v___y_2317_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2355_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2329_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2329_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
v___jp_2363_:
{
lean_object* v___x_2376_; 
lean_inc(v_snd_2270_);
v___x_2376_ = l_Lean_MVarId_getType(v_snd_2270_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
lean_inc(v_snd_2270_);
v___x_2378_ = l_Lean_MVarId_getTag(v_snd_2270_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2377_, v_a_2379_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_Expr_mvarId_x21(v_a_2381_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1));
lean_inc_ref(v___y_2366_);
v___x_2384_ = l_Lean_MVarId_note(v___x_2382_, v___x_2383_, v___y_2366_, v___y_2367_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v_fst_2386_; lean_object* v_snd_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v_fst_2386_ = lean_ctor_get(v_a_2385_, 0);
lean_inc_n(v_fst_2386_, 2);
v_snd_2387_ = lean_ctor_get(v_a_2385_, 1);
lean_inc(v_snd_2387_);
lean_dec(v_a_2385_);
v___x_2388_ = lean_mk_empty_array_with_capacity(v___x_2276_);
v___x_2389_ = lean_array_push(v___x_2388_, v_fst_2386_);
v___x_2390_ = l_Lean_Meta_simpGoal(v_snd_2387_, v___x_2277_, v_simprocs_2278_, v_discharge_x3f_2279_, v___x_2273_, v___x_2389_, v_snd_2280_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v_fst_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v_fst_2392_ = lean_ctor_get(v_a_2391_, 0);
if (lean_obj_tag(v_fst_2392_) == 0)
{
lean_object* v_snd_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_fst_2386_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___x_2272_);
v_snd_2393_ = lean_ctor_get(v_a_2391_, 1);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_a_2391_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v_a_2391_, 0);
lean_dec(v_unused_2464_);
v___x_2395_ = v_a_2391_;
v_isShared_2396_ = v_isSharedCheck_2463_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_snd_2393_);
lean_dec(v_a_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2463_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v_a_2398_; uint8_t v___x_2399_; 
v___x_2397_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2398_);
lean_dec(v_a_2398_);
if (v___x_2399_ == 0)
{
lean_del_object(v___x_2395_);
lean_dec_ref(v___y_2366_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
v___y_2300_ = v_a_2381_;
v___y_2301_ = v_snd_2393_;
v___y_2302_ = v___y_2373_;
goto v___jp_2299_;
}
else
{
if (lean_obj_tag(v___y_2366_) == 1)
{
lean_object* v_fvarId_2400_; lean_object* v_lctx_2401_; lean_object* v___x_2402_; 
v_fvarId_2400_ = lean_ctor_get(v___y_2366_, 0);
lean_inc(v_fvarId_2400_);
lean_dec_ref_known(v___y_2366_, 1);
v_lctx_2401_ = lean_ctor_get(v___y_2372_, 2);
lean_inc_ref(v_lctx_2401_);
v___x_2402_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2401_, v_fvarId_2400_);
if (lean_obj_tag(v___x_2402_) == 1)
{
lean_object* v_val_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2462_; 
v_val_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2462_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_val_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2462_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = l_Lean_mkIdent(v_val_2403_);
lean_inc_ref(v___f_2281_);
lean_inc(v___y_2375_);
lean_inc_ref(v___y_2374_);
lean_inc(v___y_2373_);
lean_inc_ref(v___y_2372_);
lean_inc(v___y_2371_);
lean_inc_ref(v___y_2370_);
lean_inc(v___y_2369_);
lean_inc_ref(v___y_2368_);
v___x_2408_ = lean_apply_9(v___f_2281_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, lean_box(0));
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc_n(v_a_2409_, 2);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2284_);
lean_inc_ref(v___x_2283_);
lean_inc_ref(v___x_2282_);
v___x_2411_ = l_Lean_Name_mkStr4(v___x_2282_, v___x_2283_, v___x_2284_, v___x_2410_);
v___x_2412_ = l_Lean_Syntax_node1(v_a_2409_, v___x_2285_, v___x_2407_);
v___x_2413_ = l_Lean_Syntax_node1(v_a_2409_, v___x_2411_, v___x_2412_);
lean_inc(v___y_2375_);
lean_inc_ref(v___y_2374_);
lean_inc(v___y_2373_);
lean_inc_ref(v___y_2372_);
lean_inc(v___y_2371_);
lean_inc_ref(v___y_2370_);
lean_inc(v___y_2369_);
lean_inc_ref(v___y_2368_);
v___x_2414_ = lean_apply_9(v___f_2281_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, lean_box(0));
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v_ref_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_n(v_a_2415_, 2);
lean_dec_ref_known(v___x_2414_, 1);
v_ref_2416_ = lean_ctor_get(v___y_2374_, 2);
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2396_ == 0)
{
lean_ctor_set_tag(v___x_2395_, 2);
lean_ctor_set(v___x_2395_, 1, v___x_2417_);
lean_ctor_set(v___x_2395_, 0, v_a_2415_);
v___x_2419_ = v___x_2395_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2421_ = l_Lean_Name_mkStr4(v___x_2282_, v___x_2283_, v___x_2284_, v___x_2420_);
v___x_2422_ = l_Lean_Syntax_node2(v_a_2415_, v___x_2421_, v___x_2419_, v___x_2413_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2422_);
v___x_2424_ = v___x_2405_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; 
lean_inc(v___y_2375_);
lean_inc_ref(v___y_2374_);
lean_inc(v___y_2373_);
lean_inc_ref(v___y_2372_);
lean_inc(v___y_2371_);
lean_inc_ref(v___y_2370_);
lean_inc(v___y_2369_);
lean_inc_ref(v___y_2368_);
v___x_2425_ = lean_apply_10(v___f_2286_, v___x_2424_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, lean_box(0));
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
lean_inc(v_ref_2416_);
v___x_2427_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2287_, v_ref_2416_, v_a_2426_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_dec_ref_known(v___x_2427_, 1);
v___y_2300_ = v_a_2381_;
v___y_2301_ = v_snd_2393_;
v___y_2302_ = v___y_2373_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_snd_2393_);
lean_dec(v_a_2381_);
lean_dec(v_snd_2270_);
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
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
lean_dec(v_snd_2393_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2287_);
lean_dec(v_snd_2270_);
v_a_2436_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2425_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2425_);
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
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v___x_2413_);
lean_del_object(v___x_2405_);
lean_del_object(v___x_2395_);
lean_dec(v_snd_2393_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec(v_snd_2270_);
v_a_2446_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2414_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2414_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v___x_2407_);
lean_del_object(v___x_2405_);
lean_del_object(v___x_2395_);
lean_dec(v_snd_2393_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec(v_snd_2270_);
v_a_2454_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2408_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2408_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
else
{
lean_dec(v___x_2402_);
lean_del_object(v___x_2395_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
v___y_2300_ = v_a_2381_;
v___y_2301_ = v_snd_2393_;
v___y_2302_ = v___y_2373_;
goto v___jp_2299_;
}
}
else
{
lean_del_object(v___x_2395_);
lean_dec_ref(v___y_2366_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
v___y_2300_ = v_a_2381_;
v___y_2301_ = v_snd_2393_;
v___y_2302_ = v___y_2373_;
goto v___jp_2299_;
}
}
}
}
else
{
lean_object* v_val_2465_; lean_object* v_snd_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
v_val_2465_ = lean_ctor_get(v_fst_2392_, 0);
lean_inc(v_val_2465_);
v_snd_2466_ = lean_ctor_get(v_a_2391_, 1);
lean_inc(v_snd_2466_);
lean_dec(v_a_2391_);
v_fst_2467_ = lean_ctor_get(v_val_2465_, 0);
lean_inc(v_fst_2467_);
v_snd_2468_ = lean_ctor_get(v_val_2465_, 1);
lean_inc(v_snd_2468_);
lean_dec(v_val_2465_);
v___x_2469_ = lean_array_get_size(v_fst_2467_);
v___x_2470_ = lean_nat_dec_lt(v___x_2288_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec(v_fst_2467_);
v___y_2313_ = v___y_2364_;
v___y_2314_ = v___y_2365_;
v___y_2315_ = v___y_2366_;
v___y_2316_ = v___y_2371_;
v___y_2317_ = v_a_2381_;
v___y_2318_ = v___y_2374_;
v___y_2319_ = v___x_2383_;
v___y_2320_ = v___y_2375_;
v___y_2321_ = v___y_2370_;
v___y_2322_ = v___y_2372_;
v___y_2323_ = v_snd_2466_;
v___y_2324_ = v_snd_2468_;
v___y_2325_ = v___y_2368_;
v___y_2326_ = v___y_2369_;
v___y_2327_ = v___y_2373_;
v___y_2328_ = v_fst_2386_;
goto v___jp_2312_;
}
else
{
lean_object* v___x_2471_; 
lean_dec(v_fst_2386_);
v___x_2471_ = lean_array_fget(v_fst_2467_, v___x_2288_);
lean_dec(v_fst_2467_);
v___y_2313_ = v___y_2364_;
v___y_2314_ = v___y_2365_;
v___y_2315_ = v___y_2366_;
v___y_2316_ = v___y_2371_;
v___y_2317_ = v_a_2381_;
v___y_2318_ = v___y_2374_;
v___y_2319_ = v___x_2383_;
v___y_2320_ = v___y_2375_;
v___y_2321_ = v___y_2370_;
v___y_2322_ = v___y_2372_;
v___y_2323_ = v_snd_2466_;
v___y_2324_ = v_snd_2468_;
v___y_2325_ = v___y_2368_;
v___y_2326_ = v___y_2369_;
v___y_2327_ = v___y_2373_;
v___y_2328_ = v___x_2471_;
goto v___jp_2312_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v_fst_2386_);
lean_dec(v_a_2381_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2472_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2390_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2390_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_a_2381_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2480_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2384_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2384_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2488_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2380_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2380_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_a_2377_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2496_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2378_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2378_);
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
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v___x_2285_);
lean_dec_ref(v___x_2284_);
lean_dec_ref(v___x_2283_);
lean_dec_ref(v___x_2282_);
lean_dec_ref(v___f_2281_);
lean_dec_ref(v_snd_2280_);
lean_dec(v_discharge_x3f_2279_);
lean_dec_ref(v_simprocs_2278_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_snd_2270_);
v_a_2504_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2376_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2376_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v_usingArg_2641_ = _args[0];
lean_object* v_snd_2642_ = _args[1];
lean_object* v___x_2643_ = _args[2];
lean_object* v___x_2644_ = _args[3];
lean_object* v___x_2645_ = _args[4];
lean_object* v_useReducible_2646_ = _args[5];
lean_object* v___x_2647_ = _args[6];
lean_object* v___x_2648_ = _args[7];
lean_object* v___x_2649_ = _args[8];
lean_object* v_simprocs_2650_ = _args[9];
lean_object* v_discharge_x3f_2651_ = _args[10];
lean_object* v_snd_2652_ = _args[11];
lean_object* v___f_2653_ = _args[12];
lean_object* v___x_2654_ = _args[13];
lean_object* v___x_2655_ = _args[14];
lean_object* v___x_2656_ = _args[15];
lean_object* v___x_2657_ = _args[16];
lean_object* v___f_2658_ = _args[17];
lean_object* v_a_2659_ = _args[18];
lean_object* v___x_2660_ = _args[19];
lean_object* v___f_2661_ = _args[20];
lean_object* v___y_2662_ = _args[21];
lean_object* v___y_2663_ = _args[22];
lean_object* v___y_2664_ = _args[23];
lean_object* v___y_2665_ = _args[24];
lean_object* v___y_2666_ = _args[25];
lean_object* v___y_2667_ = _args[26];
lean_object* v___y_2668_ = _args[27];
lean_object* v___y_2669_ = _args[28];
lean_object* v___y_2670_ = _args[29];
_start:
{
uint8_t v___x_95760__boxed_2671_; uint8_t v___x_95762__boxed_2672_; uint8_t v_useReducible_boxed_2673_; uint8_t v___x_95763__boxed_2674_; lean_object* v_res_2675_; 
v___x_95760__boxed_2671_ = lean_unbox(v___x_2643_);
v___x_95762__boxed_2672_ = lean_unbox(v___x_2645_);
v_useReducible_boxed_2673_ = lean_unbox(v_useReducible_2646_);
v___x_95763__boxed_2674_ = lean_unbox(v___x_2647_);
v_res_2675_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2641_, v_snd_2642_, v___x_95760__boxed_2671_, v___x_2644_, v___x_95762__boxed_2672_, v_useReducible_boxed_2673_, v___x_95763__boxed_2674_, v___x_2648_, v___x_2649_, v_simprocs_2650_, v_discharge_x3f_2651_, v_snd_2652_, v___f_2653_, v___x_2654_, v___x_2655_, v___x_2656_, v___x_2657_, v___f_2658_, v_a_2659_, v___x_2660_, v___f_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___x_2660_);
lean_dec(v___x_2648_);
return v_res_2675_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0(void){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_unsigned_to_nat(32u);
v___x_2680_ = lean_mk_empty_array_with_capacity(v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2682_, lean_object* v_tk_2683_, lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v___x_2686_, lean_object* v_simprocs_2687_, uint8_t v___x_2688_, lean_object* v_usingArg_2689_, lean_object* v___x_2690_, uint8_t v___x_2691_, uint8_t v_useReducible_2692_, uint8_t v___x_2693_, lean_object* v___x_2694_, lean_object* v___f_2695_, lean_object* v___x_2696_, lean_object* v___x_2697_, lean_object* v___x_2698_, lean_object* v___f_2699_, lean_object* v_a_2700_, lean_object* v_usingTk_x3f_2701_, lean_object* v_discharge_x3f_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___y_2713_; 
if (lean_obj_tag(v_usingTk_x3f_2701_) == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = lean_box(0);
v___y_2713_ = v___x_2827_;
goto v___jp_2712_;
}
else
{
lean_object* v_val_2828_; 
v_val_2828_ = lean_ctor_get(v_usingTk_x3f_2701_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v_usingTk_x3f_2701_, 1);
v___y_2713_ = v_val_2828_;
goto v___jp_2712_;
}
v___jp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2714_ = lean_mk_empty_array_with_capacity(v___x_2682_);
v___x_2715_ = lean_array_push(v___x_2714_, v_tk_2683_);
v___x_2716_ = lean_array_push(v___x_2715_, v___y_2713_);
v___x_2717_ = lean_box(2);
lean_inc(v___x_2684_);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v___x_2684_);
lean_ctor_set(v___x_2718_, 2, v___x_2716_);
v___x_2719_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2718_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___f_2721_; lean_object* v___x_2722_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___f_2721_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2721_, 0, v_a_2720_);
v___x_2722_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2704_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; size_t v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = lean_mk_empty_array_with_capacity(v___x_2685_);
v___x_2725_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2685_, 3);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
lean_ctor_set(v___x_2726_, 1, v___x_2685_);
v___x_2727_ = lean_unsigned_to_nat(32u);
v___x_2728_ = lean_mk_empty_array_with_capacity(v___x_2727_);
v___x_2729_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2730_ = ((size_t)5ULL);
v___x_2731_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2728_);
lean_ctor_set(v___x_2731_, 2, v___x_2685_);
lean_ctor_set(v___x_2731_, 3, v___x_2685_);
lean_ctor_set_usize(v___x_2731_, 4, v___x_2730_);
v___x_2732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2725_);
lean_ctor_set(v___x_2732_, 1, v___x_2725_);
lean_ctor_set(v___x_2732_, 2, v___x_2725_);
lean_ctor_set(v___x_2732_, 3, v___x_2731_);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2726_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
lean_inc_ref(v___x_2733_);
lean_inc(v_discharge_x3f_2702_);
lean_inc_ref(v_simprocs_2687_);
lean_inc_ref(v___x_2686_);
v___x_2734_ = l_Lean_Meta_simpGoal(v_a_2723_, v___x_2686_, v_simprocs_2687_, v_discharge_x3f_2702_, v___x_2688_, v___x_2724_, v___x_2733_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v_fst_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v_fst_2736_ = lean_ctor_get(v_a_2735_, 0);
if (lean_obj_tag(v_fst_2736_) == 1)
{
lean_object* v_val_2737_; lean_object* v_snd_2738_; lean_object* v_snd_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref_known(v___x_2733_, 2);
v_val_2737_ = lean_ctor_get(v_fst_2736_, 0);
lean_inc(v_val_2737_);
v_snd_2738_ = lean_ctor_get(v_a_2735_, 1);
lean_inc(v_snd_2738_);
lean_dec(v_a_2735_);
v_snd_2739_ = lean_ctor_get(v_val_2737_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_val_2737_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v_val_2737_, 0);
lean_dec(v_unused_2763_);
v___x_2741_ = v_val_2737_;
v_isShared_2742_ = v_isSharedCheck_2762_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_snd_2739_);
lean_dec(v_val_2737_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2762_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___y_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2743_ = lean_box(v___x_2688_);
v___x_2744_ = lean_box(v___x_2691_);
v___x_2745_ = lean_box(v_useReducible_2692_);
v___x_2746_ = lean_box(v___x_2693_);
lean_inc_n(v_snd_2739_, 2);
v___y_2747_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2747_, 0, v_usingArg_2689_);
lean_closure_set(v___y_2747_, 1, v_snd_2739_);
lean_closure_set(v___y_2747_, 2, v___x_2743_);
lean_closure_set(v___y_2747_, 3, v___x_2690_);
lean_closure_set(v___y_2747_, 4, v___x_2744_);
lean_closure_set(v___y_2747_, 5, v___x_2745_);
lean_closure_set(v___y_2747_, 6, v___x_2746_);
lean_closure_set(v___y_2747_, 7, v___x_2694_);
lean_closure_set(v___y_2747_, 8, v___x_2686_);
lean_closure_set(v___y_2747_, 9, v_simprocs_2687_);
lean_closure_set(v___y_2747_, 10, v_discharge_x3f_2702_);
lean_closure_set(v___y_2747_, 11, v_snd_2738_);
lean_closure_set(v___y_2747_, 12, v___f_2695_);
lean_closure_set(v___y_2747_, 13, v___x_2696_);
lean_closure_set(v___y_2747_, 14, v___x_2697_);
lean_closure_set(v___y_2747_, 15, v___x_2698_);
lean_closure_set(v___y_2747_, 16, v___x_2684_);
lean_closure_set(v___y_2747_, 17, v___f_2699_);
lean_closure_set(v___y_2747_, 18, v_a_2700_);
lean_closure_set(v___y_2747_, 19, v___x_2685_);
lean_closure_set(v___y_2747_, 20, v___f_2721_);
v___x_2748_ = lean_box(0);
if (v_isShared_2742_ == 0)
{
lean_ctor_set_tag(v___x_2741_, 1);
lean_ctor_set(v___x_2741_, 1, v___x_2748_);
lean_ctor_set(v___x_2741_, 0, v_snd_2739_);
v___x_2750_ = v___x_2741_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_snd_2739_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2750_, v___y_2704_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v___x_2752_; 
lean_dec_ref_known(v___x_2751_, 1);
v___x_2752_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_snd_2739_, v___y_2747_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
return v___x_2752_;
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec_ref(v___y_2747_);
lean_dec(v_snd_2739_);
v_a_2753_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2751_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2751_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
}
else
{
lean_object* v___x_2764_; lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2735_);
lean_dec_ref(v___f_2721_);
lean_dec(v_discharge_x3f_2702_);
lean_dec_ref(v___x_2698_);
lean_dec_ref(v___x_2697_);
lean_dec_ref(v___x_2696_);
lean_dec_ref(v___f_2695_);
lean_dec(v___x_2694_);
lean_dec_ref(v___x_2690_);
lean_dec(v_usingArg_2689_);
lean_dec_ref(v_simprocs_2687_);
lean_dec_ref(v___x_2686_);
lean_dec(v___x_2685_);
lean_dec(v___x_2684_);
v___x_2764_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2802_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2802_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2765_);
lean_dec(v_a_2765_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2771_; 
lean_dec_ref(v_a_2700_);
lean_dec_ref(v___f_2699_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2733_);
v___x_2771_ = v___x_2767_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2733_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
else
{
lean_object* v_ref_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_del_object(v___x_2767_);
v_ref_2773_ = lean_ctor_get(v___y_2709_, 2);
v___x_2774_ = lean_box(0);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc(v___y_2708_);
lean_inc_ref(v___y_2707_);
lean_inc(v___y_2706_);
lean_inc_ref(v___y_2705_);
lean_inc(v___y_2704_);
lean_inc_ref(v___y_2703_);
v___x_2775_ = lean_apply_10(v___f_2699_, v___x_2774_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, lean_box(0));
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
lean_inc(v_ref_2773_);
v___x_2777_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2700_, v_ref_2773_, v_a_2776_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2784_ == 0)
{
lean_object* v_unused_2785_; 
v_unused_2785_ = lean_ctor_get(v___x_2777_, 0);
lean_dec(v_unused_2785_);
v___x_2779_ = v___x_2777_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_dec(v___x_2777_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2733_);
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2733_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref_known(v___x_2733_, 2);
v_a_2786_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2777_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2777_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref_known(v___x_2733_, 2);
lean_dec_ref(v_a_2700_);
v_a_2794_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2775_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2775_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref_known(v___x_2733_, 2);
lean_dec_ref(v___f_2721_);
lean_dec(v_discharge_x3f_2702_);
lean_dec_ref(v_a_2700_);
lean_dec_ref(v___f_2699_);
lean_dec_ref(v___x_2698_);
lean_dec_ref(v___x_2697_);
lean_dec_ref(v___x_2696_);
lean_dec_ref(v___f_2695_);
lean_dec(v___x_2694_);
lean_dec_ref(v___x_2690_);
lean_dec(v_usingArg_2689_);
lean_dec_ref(v_simprocs_2687_);
lean_dec_ref(v___x_2686_);
lean_dec(v___x_2685_);
lean_dec(v___x_2684_);
v_a_2803_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2734_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2734_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec_ref(v___f_2721_);
lean_dec(v_discharge_x3f_2702_);
lean_dec_ref(v_a_2700_);
lean_dec_ref(v___f_2699_);
lean_dec_ref(v___x_2698_);
lean_dec_ref(v___x_2697_);
lean_dec_ref(v___x_2696_);
lean_dec_ref(v___f_2695_);
lean_dec(v___x_2694_);
lean_dec_ref(v___x_2690_);
lean_dec(v_usingArg_2689_);
lean_dec_ref(v_simprocs_2687_);
lean_dec_ref(v___x_2686_);
lean_dec(v___x_2685_);
lean_dec(v___x_2684_);
v_a_2811_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2722_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2722_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_discharge_x3f_2702_);
lean_dec_ref(v_a_2700_);
lean_dec_ref(v___f_2699_);
lean_dec_ref(v___x_2698_);
lean_dec_ref(v___x_2697_);
lean_dec_ref(v___x_2696_);
lean_dec_ref(v___f_2695_);
lean_dec(v___x_2694_);
lean_dec_ref(v___x_2690_);
lean_dec(v_usingArg_2689_);
lean_dec_ref(v_simprocs_2687_);
lean_dec_ref(v___x_2686_);
lean_dec(v___x_2685_);
lean_dec(v___x_2684_);
v_a_2819_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2719_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2719_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v___x_2829_ = _args[0];
lean_object* v_tk_2830_ = _args[1];
lean_object* v___x_2831_ = _args[2];
lean_object* v___x_2832_ = _args[3];
lean_object* v___x_2833_ = _args[4];
lean_object* v_simprocs_2834_ = _args[5];
lean_object* v___x_2835_ = _args[6];
lean_object* v_usingArg_2836_ = _args[7];
lean_object* v___x_2837_ = _args[8];
lean_object* v___x_2838_ = _args[9];
lean_object* v_useReducible_2839_ = _args[10];
lean_object* v___x_2840_ = _args[11];
lean_object* v___x_2841_ = _args[12];
lean_object* v___f_2842_ = _args[13];
lean_object* v___x_2843_ = _args[14];
lean_object* v___x_2844_ = _args[15];
lean_object* v___x_2845_ = _args[16];
lean_object* v___f_2846_ = _args[17];
lean_object* v_a_2847_ = _args[18];
lean_object* v_usingTk_x3f_2848_ = _args[19];
lean_object* v_discharge_x3f_2849_ = _args[20];
lean_object* v___y_2850_ = _args[21];
lean_object* v___y_2851_ = _args[22];
lean_object* v___y_2852_ = _args[23];
lean_object* v___y_2853_ = _args[24];
lean_object* v___y_2854_ = _args[25];
lean_object* v___y_2855_ = _args[26];
lean_object* v___y_2856_ = _args[27];
lean_object* v___y_2857_ = _args[28];
lean_object* v___y_2858_ = _args[29];
_start:
{
uint8_t v___x_96553__boxed_2859_; uint8_t v___x_96555__boxed_2860_; uint8_t v_useReducible_boxed_2861_; uint8_t v___x_96556__boxed_2862_; lean_object* v_res_2863_; 
v___x_96553__boxed_2859_ = lean_unbox(v___x_2835_);
v___x_96555__boxed_2860_ = lean_unbox(v___x_2838_);
v_useReducible_boxed_2861_ = lean_unbox(v_useReducible_2839_);
v___x_96556__boxed_2862_ = lean_unbox(v___x_2840_);
v_res_2863_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2829_, v_tk_2830_, v___x_2831_, v___x_2832_, v___x_2833_, v_simprocs_2834_, v___x_96553__boxed_2859_, v_usingArg_2836_, v___x_2837_, v___x_96555__boxed_2860_, v_useReducible_boxed_2861_, v___x_96556__boxed_2862_, v___x_2841_, v___f_2842_, v___x_2843_, v___x_2844_, v___x_2845_, v___f_2846_, v_a_2847_, v_usingTk_x3f_2848_, v_discharge_x3f_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___x_2829_);
return v_res_2863_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2869_ = lean_unsigned_to_nat(38u);
v___x_2870_ = lean_unsigned_to_nat(159u);
v___x_2871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2873_ = l_mkPanicMessageWithDecl(v___x_2872_, v___x_2871_, v___x_2870_, v___x_2869_, v___x_2868_);
return v___x_2873_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2882_ = lean_unsigned_to_nat(15u);
v___x_2883_ = lean_unsigned_to_nat(160u);
v___x_2884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2886_ = l_mkPanicMessageWithDecl(v___x_2885_, v___x_2884_, v___x_2883_, v___x_2882_, v___x_2881_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object* v_tk_2888_, lean_object* v___x_2889_, lean_object* v___x_2890_, lean_object* v___x_2891_, lean_object* v___x_2892_, uint8_t v___x_2893_, lean_object* v___x_2894_, lean_object* v___x_2895_, uint8_t v_useReducible_2896_, lean_object* v___f_2897_, lean_object* v___x_2898_, lean_object* v___x_2899_, lean_object* v___x_2900_, lean_object* v___x_2901_, lean_object* v___x_2902_, lean_object* v___x_2903_, lean_object* v_usingArg_2904_, lean_object* v___x_2905_, uint8_t v___x_2906_, lean_object* v___f_2907_, lean_object* v_usingTk_x3f_2908_, lean_object* v_squeeze_2909_, lean_object* v_unfold_2910_, lean_object* v_args_2911_, lean_object* v_only_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___y_2924_; lean_object* v___y_2928_; lean_object* v_stx_2929_; lean_object* v___y_2930_; lean_object* v_ref_2931_; lean_object* v___y_2932_; lean_object* v___y_2951_; lean_object* v_stx_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2915_, v___y_2917_, v___y_2919_, v___y_2921_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v_ref_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3293_; lean_object* v___y_3294_; uint8_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v_args_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3429_; lean_object* v___y_3430_; uint8_t v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v_only_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3463_; uint8_t v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3523_; uint8_t v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3536_; uint8_t v___y_3537_; lean_object* v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3541_; lean_object* v___y_3542_; uint8_t v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3614_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v_ref_2979_ = lean_ctor_get(v___y_2920_, 2);
v___x_2980_ = 0;
v___x_2981_ = l_Lean_SourceInfo_fromRef(v_ref_2979_, v___x_2980_);
v___x_2982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
lean_inc_ref(v___x_2891_);
lean_inc_ref(v___x_2890_);
lean_inc_ref(v___x_2889_);
v___x_2983_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_2982_);
lean_inc(v___x_2981_);
v___x_2984_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2981_);
lean_ctor_set(v___x_2984_, 1, v___x_2982_);
v___x_2985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_2986_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_2913_) == 0)
{
lean_object* v___x_3623_; 
v___x_3623_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3614_ = v___x_3623_;
goto v___jp_3613_;
}
else
{
lean_object* v_val_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_val_3624_ = lean_ctor_get(v___y_2913_, 0);
lean_inc(v_val_3624_);
lean_dec_ref_known(v___y_2913_, 1);
v___x_3625_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_3626_ = lean_array_push(v___x_3625_, v_val_3624_);
v___y_3614_ = v___x_3626_;
goto v___jp_3613_;
}
v___jp_2987_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2999_ = l_Array_append___redArg(v___x_2986_, v___y_2998_);
lean_dec_ref(v___y_2998_);
lean_inc_n(v___y_2990_, 2);
v___x_3000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3000_, 0, v___y_2990_);
lean_ctor_set(v___x_3000_, 1, v___x_2985_);
lean_ctor_set(v___x_3000_, 2, v___x_2999_);
v___x_3001_ = l_Lean_Syntax_node5(v___y_2990_, v___x_2894_, v___y_2995_, v___y_2994_, v___y_2997_, v___y_2996_, v___x_3000_);
v___x_3002_ = l_Lean_Syntax_node2(v___y_2990_, v___y_2988_, v___y_2993_, v___x_3001_);
v___y_2951_ = v___y_2989_;
v_stx_2952_ = v___x_3002_;
v___y_2953_ = v___y_2991_;
v___y_2954_ = v___y_2992_;
goto v___jp_2950_;
}
v___jp_3003_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = l_Array_append___redArg(v___x_2986_, v___y_3014_);
lean_dec_ref(v___y_3014_);
lean_inc(v___y_3006_);
v___x_3016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3016_, 0, v___y_3006_);
lean_ctor_set(v___x_3016_, 1, v___x_2985_);
lean_ctor_set(v___x_3016_, 2, v___x_3015_);
if (lean_obj_tag(v___y_3007_) == 1)
{
lean_object* v_val_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec(v___x_2892_);
v_val_3017_ = lean_ctor_get(v___y_3007_, 0);
lean_inc(v_val_3017_);
lean_dec_ref_known(v___y_3007_, 1);
v___x_3018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3006_);
v___x_3019_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___y_3006_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = l_Array_mkArray2___redArg(v___x_3019_, v_val_3017_);
v___y_2988_ = v___y_3004_;
v___y_2989_ = v___y_3005_;
v___y_2990_ = v___y_3006_;
v___y_2991_ = v___y_3008_;
v___y_2992_ = v___y_3009_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___y_3012_;
v___y_2996_ = v___x_3016_;
v___y_2997_ = v___y_3013_;
v___y_2998_ = v___x_3020_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3021_; 
lean_dec(v___y_3007_);
v___x_3021_ = lean_mk_empty_array_with_capacity(v___x_2892_);
lean_dec(v___x_2892_);
v___y_2988_ = v___y_3004_;
v___y_2989_ = v___y_3005_;
v___y_2990_ = v___y_3006_;
v___y_2991_ = v___y_3008_;
v___y_2992_ = v___y_3009_;
v___y_2993_ = v___y_3011_;
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___y_3012_;
v___y_2996_ = v___x_3016_;
v___y_2997_ = v___y_3013_;
v___y_2998_ = v___x_3021_;
goto v___jp_2987_;
}
}
v___jp_3022_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = l_Array_append___redArg(v___x_2986_, v___y_3033_);
lean_dec_ref(v___y_3033_);
lean_inc(v___y_3025_);
v___x_3035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3035_, 0, v___y_3025_);
lean_ctor_set(v___x_3035_, 1, v___x_2985_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
if (lean_obj_tag(v___y_3032_) == 1)
{
lean_object* v_val_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_val_3036_ = lean_ctor_get(v___y_3032_, 0);
lean_inc(v_val_3036_);
lean_dec_ref_known(v___y_3032_, 1);
v___x_3037_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3038_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3037_);
v___x_3039_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3025_, 4);
v___x_3040_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3025_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = l_Array_append___redArg(v___x_2986_, v_val_3036_);
lean_dec(v_val_3036_);
v___x_3042_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3042_, 0, v___y_3025_);
lean_ctor_set(v___x_3042_, 1, v___x_2985_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
v___x_3043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___y_3025_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_Lean_Syntax_node3(v___y_3025_, v___x_3038_, v___x_3040_, v___x_3042_, v___x_3044_);
v___x_3046_ = l_Array_mkArray1___redArg(v___x_3045_);
v___y_3004_ = v___y_3023_;
v___y_3005_ = v___y_3024_;
v___y_3006_ = v___y_3025_;
v___y_3007_ = v___y_3027_;
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___y_3030_;
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3031_;
v___y_3013_ = v___x_3035_;
v___y_3014_ = v___x_3046_;
goto v___jp_3003_;
}
else
{
lean_object* v___x_3047_; 
lean_dec(v___y_3032_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3047_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3004_ = v___y_3023_;
v___y_3005_ = v___y_3024_;
v___y_3006_ = v___y_3025_;
v___y_3007_ = v___y_3027_;
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___y_3030_;
v___y_3011_ = v___y_3029_;
v___y_3012_ = v___y_3031_;
v___y_3013_ = v___x_3035_;
v___y_3014_ = v___x_3047_;
goto v___jp_3003_;
}
}
v___jp_3048_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = l_Array_append___redArg(v___x_2986_, v___y_3059_);
lean_dec_ref(v___y_3059_);
lean_inc(v___y_3051_);
v___x_3061_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3061_, 0, v___y_3051_);
lean_ctor_set(v___x_3061_, 1, v___x_2985_);
lean_ctor_set(v___x_3061_, 2, v___x_3060_);
if (lean_obj_tag(v___y_3057_) == 1)
{
lean_object* v_val_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_val_3062_ = lean_ctor_get(v___y_3057_, 0);
lean_inc(v_val_3062_);
lean_dec_ref_known(v___y_3057_, 1);
v___x_3063_ = l_Lean_SourceInfo_fromRef(v_val_3062_, v___x_2893_);
lean_dec(v_val_3062_);
v___x_3064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l_Array_mkArray1___redArg(v___x_3065_);
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3051_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___y_3052_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___x_3061_;
v___y_3031_ = v___y_3056_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___x_3066_;
goto v___jp_3022_;
}
else
{
lean_object* v___x_3067_; 
lean_dec(v___y_3057_);
v___x_3067_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3051_;
v___y_3026_ = v___y_3053_;
v___y_3027_ = v___y_3052_;
v___y_3028_ = v___y_3054_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___x_3061_;
v___y_3031_ = v___y_3056_;
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___x_3067_;
goto v___jp_3022_;
}
}
v___jp_3068_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3083_ = l_Array_append___redArg(v___x_2986_, v___y_3082_);
lean_dec_ref(v___y_3082_);
lean_inc_n(v___y_3073_, 3);
v___x_3084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3073_);
lean_ctor_set(v___x_3084_, 1, v___x_2985_);
lean_ctor_set(v___x_3084_, 2, v___x_3083_);
v___x_3085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___y_3073_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = l_Lean_Syntax_node6(v___y_3073_, v___y_3074_, v___y_3072_, v___y_3080_, v___y_3081_, v___x_3084_, v___x_3086_, v___y_3077_);
v___x_3088_ = l_Lean_Syntax_node4(v___y_3073_, v___y_3078_, v___y_3069_, v___y_3079_, v___y_3076_, v___x_3087_);
v___y_2951_ = v___y_3075_;
v_stx_2952_ = v___x_3088_;
v___y_2953_ = v___y_3070_;
v___y_2954_ = v___y_3071_;
goto v___jp_2950_;
}
v___jp_3089_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = l_Array_append___redArg(v___x_2986_, v___y_3103_);
lean_dec_ref(v___y_3103_);
lean_inc(v___y_3094_);
v___x_3105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3094_);
lean_ctor_set(v___x_3105_, 1, v___x_2985_);
lean_ctor_set(v___x_3105_, 2, v___x_3104_);
if (lean_obj_tag(v___y_3095_) == 1)
{
lean_object* v_val_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec(v___x_2892_);
v_val_3106_ = lean_ctor_get(v___y_3095_, 0);
lean_inc(v_val_3106_);
lean_dec_ref_known(v___y_3095_, 1);
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3108_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3107_);
v___x_3109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3094_, 4);
v___x_3110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___y_3094_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = l_Array_append___redArg(v___x_2986_, v_val_3106_);
lean_dec(v_val_3106_);
v___x_3112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3112_, 0, v___y_3094_);
lean_ctor_set(v___x_3112_, 1, v___x_2985_);
lean_ctor_set(v___x_3112_, 2, v___x_3111_);
v___x_3113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___y_3094_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = l_Lean_Syntax_node3(v___y_3094_, v___x_3108_, v___x_3110_, v___x_3112_, v___x_3114_);
v___x_3116_ = l_Array_mkArray1___redArg(v___x_3115_);
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v___y_3092_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3096_;
v___y_3075_ = v___y_3097_;
v___y_3076_ = v___y_3098_;
v___y_3077_ = v___y_3099_;
v___y_3078_ = v___y_3100_;
v___y_3079_ = v___y_3101_;
v___y_3080_ = v___y_3102_;
v___y_3081_ = v___x_3105_;
v___y_3082_ = v___x_3116_;
goto v___jp_3068_;
}
else
{
lean_object* v___x_3117_; 
lean_dec(v___y_3095_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3117_ = lean_mk_empty_array_with_capacity(v___x_2892_);
lean_dec(v___x_2892_);
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v___y_3092_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3096_;
v___y_3075_ = v___y_3097_;
v___y_3076_ = v___y_3098_;
v___y_3077_ = v___y_3099_;
v___y_3078_ = v___y_3100_;
v___y_3079_ = v___y_3101_;
v___y_3080_ = v___y_3102_;
v___y_3081_ = v___x_3105_;
v___y_3082_ = v___x_3117_;
goto v___jp_3068_;
}
}
v___jp_3118_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = l_Array_append___redArg(v___x_2986_, v___y_3132_);
lean_dec_ref(v___y_3132_);
lean_inc(v___y_3124_);
v___x_3134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3134_, 0, v___y_3124_);
lean_ctor_set(v___x_3134_, 1, v___x_2985_);
lean_ctor_set(v___x_3134_, 2, v___x_3133_);
if (lean_obj_tag(v___y_3123_) == 1)
{
lean_object* v_val_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v_val_3135_ = lean_ctor_get(v___y_3123_, 0);
lean_inc(v_val_3135_);
lean_dec_ref_known(v___y_3123_, 1);
v___x_3136_ = l_Lean_SourceInfo_fromRef(v_val_3135_, v___x_2893_);
lean_dec(v_val_3135_);
v___x_3137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = l_Array_mkArray1___redArg(v___x_3138_);
v___y_3090_ = v___y_3119_;
v___y_3091_ = v___y_3120_;
v___y_3092_ = v___y_3121_;
v___y_3093_ = v___y_3122_;
v___y_3094_ = v___y_3124_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3127_;
v___y_3098_ = v___y_3128_;
v___y_3099_ = v___y_3129_;
v___y_3100_ = v___y_3130_;
v___y_3101_ = v___y_3131_;
v___y_3102_ = v___x_3134_;
v___y_3103_ = v___x_3139_;
goto v___jp_3089_;
}
else
{
lean_object* v___x_3140_; 
lean_dec(v___y_3123_);
v___x_3140_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3090_ = v___y_3119_;
v___y_3091_ = v___y_3120_;
v___y_3092_ = v___y_3121_;
v___y_3093_ = v___y_3122_;
v___y_3094_ = v___y_3124_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3127_;
v___y_3098_ = v___y_3128_;
v___y_3099_ = v___y_3129_;
v___y_3100_ = v___y_3130_;
v___y_3101_ = v___y_3131_;
v___y_3102_ = v___x_3134_;
v___y_3103_ = v___x_3140_;
goto v___jp_3089_;
}
}
v___jp_3141_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3153_ = l_Array_append___redArg(v___x_2986_, v___y_3152_);
lean_dec_ref(v___y_3152_);
lean_inc_n(v___y_3148_, 2);
v___x_3154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3154_, 0, v___y_3148_);
lean_ctor_set(v___x_3154_, 1, v___x_2985_);
lean_ctor_set(v___x_3154_, 2, v___x_3153_);
v___x_3155_ = l_Lean_Syntax_node5(v___y_3148_, v___x_2894_, v___y_3149_, v___y_3151_, v___y_3142_, v___y_3150_, v___x_3154_);
lean_inc(v___y_3147_);
v___x_3156_ = l_Lean_Syntax_node4(v___y_3148_, v___x_2895_, v___y_3146_, v___y_3147_, v___y_3147_, v___x_3155_);
v___y_2951_ = v___y_3143_;
v_stx_2952_ = v___x_3156_;
v___y_2953_ = v___y_3144_;
v___y_2954_ = v___y_3145_;
goto v___jp_2950_;
}
v___jp_3157_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = l_Array_append___redArg(v___x_2986_, v___y_3168_);
lean_dec_ref(v___y_3168_);
lean_inc(v___y_3165_);
v___x_3170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3170_, 0, v___y_3165_);
lean_ctor_set(v___x_3170_, 1, v___x_2985_);
lean_ctor_set(v___x_3170_, 2, v___x_3169_);
if (lean_obj_tag(v___y_3160_) == 1)
{
lean_object* v_val_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v___x_2892_);
v_val_3171_ = lean_ctor_get(v___y_3160_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v___y_3160_, 1);
v___x_3172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3165_);
v___x_3173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___y_3165_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = l_Array_mkArray2___redArg(v___x_3173_, v_val_3171_);
v___y_3142_ = v___y_3158_;
v___y_3143_ = v___y_3159_;
v___y_3144_ = v___y_3161_;
v___y_3145_ = v___y_3162_;
v___y_3146_ = v___y_3163_;
v___y_3147_ = v___y_3164_;
v___y_3148_ = v___y_3165_;
v___y_3149_ = v___y_3166_;
v___y_3150_ = v___x_3170_;
v___y_3151_ = v___y_3167_;
v___y_3152_ = v___x_3174_;
goto v___jp_3141_;
}
else
{
lean_object* v___x_3175_; 
lean_dec(v___y_3160_);
v___x_3175_ = lean_mk_empty_array_with_capacity(v___x_2892_);
lean_dec(v___x_2892_);
v___y_3142_ = v___y_3158_;
v___y_3143_ = v___y_3159_;
v___y_3144_ = v___y_3161_;
v___y_3145_ = v___y_3162_;
v___y_3146_ = v___y_3163_;
v___y_3147_ = v___y_3164_;
v___y_3148_ = v___y_3165_;
v___y_3149_ = v___y_3166_;
v___y_3150_ = v___x_3170_;
v___y_3151_ = v___y_3167_;
v___y_3152_ = v___x_3175_;
goto v___jp_3141_;
}
}
v___jp_3176_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = l_Array_append___redArg(v___x_2986_, v___y_3187_);
lean_dec_ref(v___y_3187_);
lean_inc(v___y_3183_);
v___x_3189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3189_, 0, v___y_3183_);
lean_ctor_set(v___x_3189_, 1, v___x_2985_);
lean_ctor_set(v___x_3189_, 2, v___x_3188_);
if (lean_obj_tag(v___y_3185_) == 1)
{
lean_object* v_val_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_val_3190_ = lean_ctor_get(v___y_3185_, 0);
lean_inc(v_val_3190_);
lean_dec_ref_known(v___y_3185_, 1);
v___x_3191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3192_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3191_);
v___x_3193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3183_, 4);
v___x_3194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___y_3183_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = l_Array_append___redArg(v___x_2986_, v_val_3190_);
lean_dec(v_val_3190_);
v___x_3196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3196_, 0, v___y_3183_);
lean_ctor_set(v___x_3196_, 1, v___x_2985_);
lean_ctor_set(v___x_3196_, 2, v___x_3195_);
v___x_3197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___y_3183_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = l_Lean_Syntax_node3(v___y_3183_, v___x_3192_, v___x_3194_, v___x_3196_, v___x_3198_);
v___x_3200_ = l_Array_mkArray1___redArg(v___x_3199_);
v___y_3158_ = v___x_3189_;
v___y_3159_ = v___y_3177_;
v___y_3160_ = v___y_3179_;
v___y_3161_ = v___y_3178_;
v___y_3162_ = v___y_3180_;
v___y_3163_ = v___y_3181_;
v___y_3164_ = v___y_3182_;
v___y_3165_ = v___y_3183_;
v___y_3166_ = v___y_3184_;
v___y_3167_ = v___y_3186_;
v___y_3168_ = v___x_3200_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3201_; 
lean_dec(v___y_3185_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3201_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3158_ = v___x_3189_;
v___y_3159_ = v___y_3177_;
v___y_3160_ = v___y_3179_;
v___y_3161_ = v___y_3178_;
v___y_3162_ = v___y_3180_;
v___y_3163_ = v___y_3181_;
v___y_3164_ = v___y_3182_;
v___y_3165_ = v___y_3183_;
v___y_3166_ = v___y_3184_;
v___y_3167_ = v___y_3186_;
v___y_3168_ = v___x_3201_;
goto v___jp_3157_;
}
}
v___jp_3202_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = l_Array_append___redArg(v___x_2986_, v___y_3213_);
lean_dec_ref(v___y_3213_);
lean_inc(v___y_3209_);
v___x_3215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3215_, 0, v___y_3209_);
lean_ctor_set(v___x_3215_, 1, v___x_2985_);
lean_ctor_set(v___x_3215_, 2, v___x_3214_);
if (lean_obj_tag(v___y_3211_) == 1)
{
lean_object* v_val_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v_val_3216_ = lean_ctor_get(v___y_3211_, 0);
lean_inc(v_val_3216_);
lean_dec_ref_known(v___y_3211_, 1);
v___x_3217_ = l_Lean_SourceInfo_fromRef(v_val_3216_, v___x_2893_);
lean_dec(v_val_3216_);
v___x_3218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3217_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = l_Array_mkArray1___redArg(v___x_3219_);
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3204_;
v___y_3180_ = v___y_3206_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3208_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3210_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___x_3215_;
v___y_3187_ = v___x_3220_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3221_; 
lean_dec(v___y_3211_);
v___x_3221_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3177_ = v___y_3203_;
v___y_3178_ = v___y_3205_;
v___y_3179_ = v___y_3204_;
v___y_3180_ = v___y_3206_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3208_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___y_3210_;
v___y_3185_ = v___y_3212_;
v___y_3186_ = v___x_3215_;
v___y_3187_ = v___x_3221_;
goto v___jp_3176_;
}
}
v___jp_3222_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3236_ = l_Array_append___redArg(v___x_2986_, v___y_3235_);
lean_dec_ref(v___y_3235_);
lean_inc_n(v___y_3233_, 3);
v___x_3237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3237_, 0, v___y_3233_);
lean_ctor_set(v___x_3237_, 1, v___x_2985_);
lean_ctor_set(v___x_3237_, 2, v___x_3236_);
v___x_3238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___y_3233_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l_Lean_Syntax_node6(v___y_3233_, v___y_3223_, v___y_3228_, v___y_3229_, v___y_3225_, v___x_3237_, v___x_3239_, v___y_3227_);
lean_inc(v___y_3232_);
v___x_3241_ = l_Lean_Syntax_node4(v___y_3233_, v___y_3234_, v___y_3230_, v___y_3232_, v___y_3232_, v___x_3240_);
v___y_2951_ = v___y_3231_;
v_stx_2952_ = v___x_3241_;
v___y_2953_ = v___y_3224_;
v___y_2954_ = v___y_3226_;
goto v___jp_2950_;
}
v___jp_3242_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = l_Array_append___redArg(v___x_2986_, v___y_3255_);
lean_dec_ref(v___y_3255_);
lean_inc(v___y_3253_);
v___x_3257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3257_, 0, v___y_3253_);
lean_ctor_set(v___x_3257_, 1, v___x_2985_);
lean_ctor_set(v___x_3257_, 2, v___x_3256_);
if (lean_obj_tag(v___y_3249_) == 1)
{
lean_object* v_val_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec(v___x_2892_);
v_val_3258_ = lean_ctor_get(v___y_3249_, 0);
lean_inc(v_val_3258_);
lean_dec_ref_known(v___y_3249_, 1);
v___x_3259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3260_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3259_);
v___x_3261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3253_, 4);
v___x_3262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___y_3253_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = l_Array_append___redArg(v___x_2986_, v_val_3258_);
lean_dec(v_val_3258_);
v___x_3264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3264_, 0, v___y_3253_);
lean_ctor_set(v___x_3264_, 1, v___x_2985_);
lean_ctor_set(v___x_3264_, 2, v___x_3263_);
v___x_3265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___y_3253_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = l_Lean_Syntax_node3(v___y_3253_, v___x_3260_, v___x_3262_, v___x_3264_, v___x_3266_);
v___x_3268_ = l_Array_mkArray1___redArg(v___x_3267_);
v___y_3223_ = v___y_3243_;
v___y_3224_ = v___y_3244_;
v___y_3225_ = v___x_3257_;
v___y_3226_ = v___y_3245_;
v___y_3227_ = v___y_3246_;
v___y_3228_ = v___y_3247_;
v___y_3229_ = v___y_3248_;
v___y_3230_ = v___y_3250_;
v___y_3231_ = v___y_3251_;
v___y_3232_ = v___y_3252_;
v___y_3233_ = v___y_3253_;
v___y_3234_ = v___y_3254_;
v___y_3235_ = v___x_3268_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3269_; 
lean_dec(v___y_3249_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3269_ = lean_mk_empty_array_with_capacity(v___x_2892_);
lean_dec(v___x_2892_);
v___y_3223_ = v___y_3243_;
v___y_3224_ = v___y_3244_;
v___y_3225_ = v___x_3257_;
v___y_3226_ = v___y_3245_;
v___y_3227_ = v___y_3246_;
v___y_3228_ = v___y_3247_;
v___y_3229_ = v___y_3248_;
v___y_3230_ = v___y_3250_;
v___y_3231_ = v___y_3251_;
v___y_3232_ = v___y_3252_;
v___y_3233_ = v___y_3253_;
v___y_3234_ = v___y_3254_;
v___y_3235_ = v___x_3269_;
goto v___jp_3222_;
}
}
v___jp_3270_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = l_Array_append___redArg(v___x_2986_, v___y_3283_);
lean_dec_ref(v___y_3283_);
lean_inc(v___y_3281_);
v___x_3285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3285_, 0, v___y_3281_);
lean_ctor_set(v___x_3285_, 1, v___x_2985_);
lean_ctor_set(v___x_3285_, 2, v___x_3284_);
if (lean_obj_tag(v___y_3276_) == 1)
{
lean_object* v_val_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_val_3286_ = lean_ctor_get(v___y_3276_, 0);
lean_inc(v_val_3286_);
lean_dec_ref_known(v___y_3276_, 1);
v___x_3287_ = l_Lean_SourceInfo_fromRef(v_val_3286_, v___x_2893_);
lean_dec(v_val_3286_);
v___x_3288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l_Array_mkArray1___redArg(v___x_3289_);
v___y_3243_ = v___y_3271_;
v___y_3244_ = v___y_3272_;
v___y_3245_ = v___y_3273_;
v___y_3246_ = v___y_3274_;
v___y_3247_ = v___y_3275_;
v___y_3248_ = v___x_3285_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___x_3290_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3291_; 
lean_dec(v___y_3276_);
v___x_3291_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3243_ = v___y_3271_;
v___y_3244_ = v___y_3272_;
v___y_3245_ = v___y_3273_;
v___y_3246_ = v___y_3274_;
v___y_3247_ = v___y_3275_;
v___y_3248_ = v___x_3285_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___y_3280_;
v___y_3253_ = v___y_3281_;
v___y_3254_ = v___y_3282_;
v___y_3255_ = v___x_3291_;
goto v___jp_3242_;
}
}
v___jp_3292_:
{
if (v___y_3295_ == 0)
{
if (v_useReducible_2896_ == 0)
{
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_dec(v___y_3307_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___y_2957_ = v___y_3303_;
v___y_2958_ = v___y_3305_;
v___y_2959_ = v___y_3297_;
v___y_2960_ = v___y_3293_;
v___y_2961_ = v___y_3306_;
v___y_2962_ = v___y_3294_;
v___y_2963_ = v___y_3300_;
v___y_2964_ = v___y_3296_;
v___y_2965_ = v___y_3298_;
goto v___jp_2956_;
}
else
{
lean_object* v_val_3308_; lean_object* v___x_3309_; 
v_val_3308_ = lean_ctor_get(v___y_3304_, 0);
lean_inc(v_val_3308_);
lean_dec_ref_known(v___y_3304_, 1);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3296_);
v___x_3309_ = lean_apply_9(v___f_2897_, v___y_3305_, v___y_3297_, v___y_3293_, v___y_3306_, v___y_3294_, v___y_3300_, v___y_3296_, v___y_3298_, lean_box(0));
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc_n(v_a_3310_, 3);
lean_dec_ref_known(v___x_3309_, 1);
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2891_, 2);
lean_inc_ref_n(v___x_2890_, 2);
lean_inc_ref_n(v___x_2889_, 2);
v___x_3312_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_a_3310_);
lean_ctor_set(v___x_3313_, 1, v___x_2898_);
v___x_3314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3314_, 0, v_a_3310_);
lean_ctor_set(v___x_3314_, 1, v___x_2985_);
lean_ctor_set(v___x_3314_, 2, v___x_2986_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3316_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3315_);
if (lean_obj_tag(v___y_3307_) == 0)
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3271_ = v___x_3316_;
v___y_3272_ = v___y_3296_;
v___y_3273_ = v___y_3298_;
v___y_3274_ = v_val_3308_;
v___y_3275_ = v___y_3299_;
v___y_3276_ = v___y_3301_;
v___y_3277_ = v___y_3302_;
v___y_3278_ = v___x_3313_;
v___y_3279_ = v___y_3303_;
v___y_3280_ = v___x_3314_;
v___y_3281_ = v_a_3310_;
v___y_3282_ = v___x_3312_;
v___y_3283_ = v___x_3317_;
goto v___jp_3270_;
}
else
{
lean_object* v_val_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_val_3318_ = lean_ctor_get(v___y_3307_, 0);
lean_inc(v_val_3318_);
lean_dec_ref_known(v___y_3307_, 1);
v___x_3319_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_3320_ = lean_array_push(v___x_3319_, v_val_3318_);
v___y_3271_ = v___x_3316_;
v___y_3272_ = v___y_3296_;
v___y_3273_ = v___y_3298_;
v___y_3274_ = v_val_3308_;
v___y_3275_ = v___y_3299_;
v___y_3276_ = v___y_3301_;
v___y_3277_ = v___y_3302_;
v___y_3278_ = v___x_3313_;
v___y_3279_ = v___y_3303_;
v___y_3280_ = v___x_3314_;
v___y_3281_ = v_a_3310_;
v___y_3282_ = v___x_3312_;
v___y_3283_ = v___x_3320_;
goto v___jp_3270_;
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v_val_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_2898_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3321_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3309_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3309_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
else
{
lean_object* v___x_3329_; 
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3296_);
v___x_3329_ = lean_apply_9(v___f_2897_, v___y_3305_, v___y_3297_, v___y_3293_, v___y_3306_, v___y_3294_, v___y_3300_, v___y_3296_, v___y_3298_, lean_box(0));
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc_n(v_a_3330_, 3);
lean_dec_ref_known(v___x_3329_, 1);
v___x_3331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_a_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_2898_);
v___x_3332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3332_, 0, v_a_3330_);
lean_ctor_set(v___x_3332_, 1, v___x_2985_);
lean_ctor_set(v___x_3332_, 2, v___x_2986_);
if (lean_obj_tag(v___y_3307_) == 0)
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3203_ = v___y_3303_;
v___y_3204_ = v___y_3304_;
v___y_3205_ = v___y_3296_;
v___y_3206_ = v___y_3298_;
v___y_3207_ = v___x_3331_;
v___y_3208_ = v___x_3332_;
v___y_3209_ = v_a_3330_;
v___y_3210_ = v___y_3299_;
v___y_3211_ = v___y_3301_;
v___y_3212_ = v___y_3302_;
v___y_3213_ = v___x_3333_;
goto v___jp_3202_;
}
else
{
lean_object* v_val_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_val_3334_ = lean_ctor_get(v___y_3307_, 0);
lean_inc(v_val_3334_);
lean_dec_ref_known(v___y_3307_, 1);
v___x_3335_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_3336_ = lean_array_push(v___x_3335_, v_val_3334_);
v___y_3203_ = v___y_3303_;
v___y_3204_ = v___y_3304_;
v___y_3205_ = v___y_3296_;
v___y_3206_ = v___y_3298_;
v___y_3207_ = v___x_3331_;
v___y_3208_ = v___x_3332_;
v___y_3209_ = v_a_3330_;
v___y_3210_ = v___y_3299_;
v___y_3211_ = v___y_3301_;
v___y_3212_ = v___y_3302_;
v___y_3213_ = v___x_3336_;
goto v___jp_3202_;
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v___y_3307_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_2898_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3337_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3329_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3329_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
else
{
lean_dec(v___x_2895_);
if (v_useReducible_2896_ == 0)
{
lean_dec(v___x_2894_);
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_dec(v___y_3307_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___y_2957_ = v___y_3303_;
v___y_2958_ = v___y_3305_;
v___y_2959_ = v___y_3297_;
v___y_2960_ = v___y_3293_;
v___y_2961_ = v___y_3306_;
v___y_2962_ = v___y_3294_;
v___y_2963_ = v___y_3300_;
v___y_2964_ = v___y_3296_;
v___y_2965_ = v___y_3298_;
goto v___jp_2956_;
}
else
{
lean_object* v_val_3345_; lean_object* v___x_3346_; 
v_val_3345_ = lean_ctor_get(v___y_3304_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v___y_3304_, 1);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3296_);
v___x_3346_ = lean_apply_9(v___f_2897_, v___y_3305_, v___y_3297_, v___y_3293_, v___y_3306_, v___y_3294_, v___y_3300_, v___y_3296_, v___y_3298_, lean_box(0));
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc_n(v_a_3347_, 5);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2891_, 2);
lean_inc_ref_n(v___x_2890_, 2);
lean_inc_ref_n(v___x_2889_, 2);
v___x_3349_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3350_, 0, v_a_3347_);
lean_ctor_set(v___x_3350_, 1, v___x_2898_);
v___x_3351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3351_, 0, v_a_3347_);
lean_ctor_set(v___x_3351_, 1, v___x_2985_);
lean_ctor_set(v___x_3351_, 2, v___x_2986_);
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3353_, 0, v_a_3347_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = l_Lean_Syntax_node1(v_a_3347_, v___x_2985_, v___x_3353_);
v___x_3355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3356_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3355_);
if (lean_obj_tag(v___y_3307_) == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3119_ = v___x_3350_;
v___y_3120_ = v___y_3296_;
v___y_3121_ = v___y_3298_;
v___y_3122_ = v___y_3299_;
v___y_3123_ = v___y_3301_;
v___y_3124_ = v_a_3347_;
v___y_3125_ = v___y_3302_;
v___y_3126_ = v___x_3356_;
v___y_3127_ = v___y_3303_;
v___y_3128_ = v___x_3354_;
v___y_3129_ = v_val_3345_;
v___y_3130_ = v___x_3349_;
v___y_3131_ = v___x_3351_;
v___y_3132_ = v___x_3357_;
goto v___jp_3118_;
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_val_3358_ = lean_ctor_get(v___y_3307_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___y_3307_, 1);
v___x_3359_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_3360_ = lean_array_push(v___x_3359_, v_val_3358_);
v___y_3119_ = v___x_3350_;
v___y_3120_ = v___y_3296_;
v___y_3121_ = v___y_3298_;
v___y_3122_ = v___y_3299_;
v___y_3123_ = v___y_3301_;
v___y_3124_ = v_a_3347_;
v___y_3125_ = v___y_3302_;
v___y_3126_ = v___x_3356_;
v___y_3127_ = v___y_3303_;
v___y_3128_ = v___x_3354_;
v___y_3129_ = v_val_3345_;
v___y_3130_ = v___x_3349_;
v___y_3131_ = v___x_3351_;
v___y_3132_ = v___x_3360_;
goto v___jp_3118_;
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_val_3345_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___x_2898_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3361_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3346_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3346_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
else
{
lean_object* v___x_3369_; 
lean_dec_ref(v___x_2898_);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3296_);
v___x_3369_ = lean_apply_9(v___f_2897_, v___y_3305_, v___y_3297_, v___y_3293_, v___y_3306_, v___y_3294_, v___y_3300_, v___y_3296_, v___y_3298_, lean_box(0));
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc_n(v_a_3370_, 2);
lean_dec_ref_known(v___x_3369_, 1);
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2891_);
lean_inc_ref(v___x_2890_);
lean_inc_ref(v___x_2889_);
v___x_3372_ = l_Lean_Name_mkStr4(v___x_2889_, v___x_2890_, v___x_2891_, v___x_3371_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3374_, 0, v_a_3370_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
if (lean_obj_tag(v___y_3307_) == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3049_ = v___x_3372_;
v___y_3050_ = v___y_3303_;
v___y_3051_ = v_a_3370_;
v___y_3052_ = v___y_3304_;
v___y_3053_ = v___y_3296_;
v___y_3054_ = v___y_3298_;
v___y_3055_ = v___x_3374_;
v___y_3056_ = v___y_3299_;
v___y_3057_ = v___y_3301_;
v___y_3058_ = v___y_3302_;
v___y_3059_ = v___x_3375_;
goto v___jp_3048_;
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_val_3376_ = lean_ctor_get(v___y_3307_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v___y_3307_, 1);
v___x_3377_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_3378_ = lean_array_push(v___x_3377_, v_val_3376_);
v___y_3049_ = v___x_3372_;
v___y_3050_ = v___y_3303_;
v___y_3051_ = v_a_3370_;
v___y_3052_ = v___y_3304_;
v___y_3053_ = v___y_3296_;
v___y_3054_ = v___y_3298_;
v___y_3055_ = v___x_3374_;
v___y_3056_ = v___y_3299_;
v___y_3057_ = v___y_3301_;
v___y_3058_ = v___y_3302_;
v___y_3059_ = v___x_3378_;
goto v___jp_3048_;
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v___y_3307_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3379_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3369_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3369_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
}
v___jp_3387_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3404_ = lean_unsigned_to_nat(5u);
v___x_3405_ = l_Lean_Syntax_getArg(v___y_3392_, v___x_3404_);
lean_dec(v___y_3392_);
v___x_3406_ = l_Lean_Syntax_matchesNull(v___x_3405_, v___x_2892_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_dec(v_args_3395_);
lean_dec(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3407_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3408_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3407_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___y_2951_ = v___y_3388_;
v_stx_2952_ = v_a_3409_;
v___y_2953_ = v___y_3402_;
v___y_2954_ = v___y_3403_;
goto v___jp_2950_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec_ref(v___y_3388_);
lean_dec(v_tk_2888_);
v_a_3410_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3408_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3408_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_Syntax_getOptional_x3f(v___y_3389_);
lean_dec(v___y_3389_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_box(0);
v___y_3293_ = v___y_3398_;
v___y_3294_ = v___y_3400_;
v___y_3295_ = v___y_3391_;
v___y_3296_ = v___y_3402_;
v___y_3297_ = v___y_3397_;
v___y_3298_ = v___y_3403_;
v___y_3299_ = v___y_3393_;
v___y_3300_ = v___y_3401_;
v___y_3301_ = v___y_3394_;
v___y_3302_ = v_args_3395_;
v___y_3303_ = v___y_3388_;
v___y_3304_ = v___y_3390_;
v___y_3305_ = v___y_3396_;
v___y_3306_ = v___y_3399_;
v___y_3307_ = v___x_3419_;
goto v___jp_3292_;
}
else
{
lean_object* v_val_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v_val_3420_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3418_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_val_3420_);
lean_dec(v___x_3418_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_val_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
v___y_3293_ = v___y_3398_;
v___y_3294_ = v___y_3400_;
v___y_3295_ = v___y_3391_;
v___y_3296_ = v___y_3402_;
v___y_3297_ = v___y_3397_;
v___y_3298_ = v___y_3403_;
v___y_3299_ = v___y_3393_;
v___y_3300_ = v___y_3401_;
v___y_3301_ = v___y_3394_;
v___y_3302_ = v_args_3395_;
v___y_3303_ = v___y_3388_;
v___y_3304_ = v___y_3390_;
v___y_3305_ = v___y_3396_;
v___y_3306_ = v___y_3399_;
v___y_3307_ = v___x_3425_;
goto v___jp_3292_;
}
}
}
}
}
v___jp_3428_:
{
lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3444_ = l_Lean_Syntax_getArg(v___y_3433_, v___x_2899_);
v___x_3445_ = l_Lean_Syntax_isNone(v___x_3444_);
if (v___x_3445_ == 0)
{
uint8_t v___x_3446_; 
lean_inc(v___x_3444_);
v___x_3446_ = l_Lean_Syntax_matchesNull(v___x_3444_, v___x_2900_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec(v___x_3444_);
lean_dec(v_only_3435_);
lean_dec(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3430_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3447_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3448_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3447_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___y_2951_ = v___y_3429_;
v_stx_2952_ = v_a_3449_;
v___y_2953_ = v___y_3442_;
v___y_2954_ = v___y_3443_;
goto v___jp_2950_;
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v___y_3429_);
lean_dec(v_tk_2888_);
v_a_3450_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3448_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = l_Lean_Syntax_getArg(v___x_3444_, v___x_2901_);
lean_dec(v___x_2901_);
lean_dec(v___x_3444_);
v___x_3459_ = l_Lean_Syntax_getArgs(v___x_3458_);
lean_dec(v___x_3458_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
v___y_3388_ = v___y_3429_;
v___y_3389_ = v___y_3430_;
v___y_3390_ = v___y_3432_;
v___y_3391_ = v___y_3431_;
v___y_3392_ = v___y_3433_;
v___y_3393_ = v___y_3434_;
v___y_3394_ = v_only_3435_;
v_args_3395_ = v___x_3460_;
v___y_3396_ = v___y_3436_;
v___y_3397_ = v___y_3437_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
v___y_3401_ = v___y_3441_;
v___y_3402_ = v___y_3442_;
v___y_3403_ = v___y_3443_;
goto v___jp_3387_;
}
}
else
{
lean_object* v___x_3461_; 
lean_dec(v___x_3444_);
lean_dec(v___x_2901_);
v___x_3461_ = lean_box(0);
v___y_3388_ = v___y_3429_;
v___y_3389_ = v___y_3430_;
v___y_3390_ = v___y_3432_;
v___y_3391_ = v___y_3431_;
v___y_3392_ = v___y_3433_;
v___y_3393_ = v___y_3434_;
v___y_3394_ = v_only_3435_;
v_args_3395_ = v___x_3461_;
v___y_3396_ = v___y_3436_;
v___y_3397_ = v___y_3437_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
v___y_3401_ = v___y_3441_;
v___y_3402_ = v___y_3442_;
v___y_3403_ = v___y_3443_;
goto v___jp_3387_;
}
}
v___jp_3462_:
{
lean_object* v_usedTheorems_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_usedTheorems_3467_ = lean_ctor_get(v___y_3463_, 0);
v___x_3468_ = l_Lean_Syntax_unsetTrailing(v___y_3465_);
v___x_3469_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3468_, v_usedTheorems_3467_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; uint8_t v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc_n(v_a_3470_, 2);
lean_dec_ref_known(v___x_3469_, 1);
v___x_3471_ = l_Lean_Syntax_isOfKind(v_a_3470_, v___x_2983_);
lean_dec(v___x_2983_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_inc(v_ref_2979_);
lean_dec(v_a_3470_);
lean_dec(v___y_3466_);
lean_dec(v___x_2903_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3472_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3473_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3472_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___y_2928_ = v___y_3463_;
v_stx_2929_ = v_a_3474_;
v___y_2930_ = v___y_2920_;
v_ref_2931_ = v_ref_2979_;
v___y_2932_ = v___y_2921_;
goto v___jp_2927_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v___y_3463_);
lean_dec(v_ref_2979_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v_tk_2888_);
v_a_3475_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3483_ = l_Lean_Syntax_getArg(v_a_3470_, v___x_2901_);
lean_inc(v___x_3483_);
v___x_3484_ = l_Lean_Syntax_isOfKind(v___x_3483_, v___x_2902_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_inc(v_ref_2979_);
lean_dec(v___x_3483_);
lean_dec(v_a_3470_);
lean_dec(v___y_3466_);
lean_dec(v___x_2903_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3485_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3486_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3485_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___y_2928_ = v___y_3463_;
v_stx_2929_ = v_a_3487_;
v___y_2930_ = v___y_2920_;
v_ref_2931_ = v_ref_2979_;
v___y_2932_ = v___y_2921_;
goto v___jp_2927_;
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec_ref(v___y_3463_);
lean_dec(v_ref_2979_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v_tk_2888_);
v_a_3488_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3486_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3486_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3496_ = l_Lean_Syntax_getArg(v_a_3470_, v___x_2903_);
lean_dec(v___x_2903_);
v___x_3497_ = l_Lean_Syntax_getArg(v_a_3470_, v___x_2900_);
v___x_3498_ = l_Lean_Syntax_isNone(v___x_3497_);
if (v___x_3498_ == 0)
{
uint8_t v___x_3499_; 
lean_inc(v___x_3497_);
v___x_3499_ = l_Lean_Syntax_matchesNull(v___x_3497_, v___x_2901_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
lean_inc(v_ref_2979_);
lean_dec(v___x_3497_);
lean_dec(v___x_3496_);
lean_dec(v___x_3483_);
lean_dec(v_a_3470_);
lean_dec(v___y_3466_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
v___x_3500_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3501_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3500_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___y_2928_ = v___y_3463_;
v_stx_2929_ = v_a_3502_;
v___y_2930_ = v___y_2920_;
v_ref_2931_ = v_ref_2979_;
v___y_2932_ = v___y_2921_;
goto v___jp_2927_;
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v___y_3463_);
lean_dec(v_ref_2979_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v_tk_2888_);
v_a_3503_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3501_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3501_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = l_Lean_Syntax_getArg(v___x_3497_, v___x_2892_);
lean_dec(v___x_3497_);
v___x_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
v___y_3429_ = v___y_3463_;
v___y_3430_ = v___x_3496_;
v___y_3431_ = v___y_3464_;
v___y_3432_ = v___y_3466_;
v___y_3433_ = v_a_3470_;
v___y_3434_ = v___x_3483_;
v_only_3435_ = v___x_3512_;
v___y_3436_ = v___y_2914_;
v___y_3437_ = v___y_2915_;
v___y_3438_ = v___y_2916_;
v___y_3439_ = v___y_2917_;
v___y_3440_ = v___y_2918_;
v___y_3441_ = v___y_2919_;
v___y_3442_ = v___y_2920_;
v___y_3443_ = v___y_2921_;
goto v___jp_3428_;
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v___x_3497_);
v___x_3513_ = lean_box(0);
v___y_3429_ = v___y_3463_;
v___y_3430_ = v___x_3496_;
v___y_3431_ = v___y_3464_;
v___y_3432_ = v___y_3466_;
v___y_3433_ = v_a_3470_;
v___y_3434_ = v___x_3483_;
v_only_3435_ = v___x_3513_;
v___y_3436_ = v___y_2914_;
v___y_3437_ = v___y_2915_;
v___y_3438_ = v___y_2916_;
v___y_3439_ = v___y_2917_;
v___y_3440_ = v___y_2918_;
v___y_3441_ = v___y_2919_;
v___y_3442_ = v___y_2920_;
v___y_3443_ = v___y_2921_;
goto v___jp_3428_;
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3463_);
lean_dec(v___x_2983_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___x_2903_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3514_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3469_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3469_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
v___jp_3522_:
{
if (lean_obj_tag(v_usingArg_2904_) == 0)
{
v___y_3463_ = v___y_3523_;
v___y_3464_ = v___y_3524_;
v___y_3465_ = v___y_3525_;
v___y_3466_ = v_usingArg_2904_;
goto v___jp_3462_;
}
else
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v_val_3526_ = lean_ctor_get(v_usingArg_2904_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_usingArg_2904_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3528_ = v_usingArg_2904_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v_usingArg_2904_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = l_Lean_Syntax_unsetTrailing(v_val_3526_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3530_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
v___y_3463_ = v___y_3523_;
v___y_3464_ = v___y_3524_;
v___y_3465_ = v___y_3525_;
v___y_3466_ = v___x_3532_;
goto v___jp_3462_;
}
}
}
}
v___jp_3535_:
{
if (v___y_3539_ == 0)
{
lean_dec(v___y_3538_);
lean_dec(v___x_2983_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v_usingArg_2904_);
lean_dec(v___x_2903_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v___y_2924_ = v___y_3536_;
goto v___jp_2923_;
}
else
{
v___y_3523_ = v___y_3536_;
v___y_3524_ = v___y_3537_;
v___y_3525_ = v___y_3538_;
goto v___jp_3522_;
}
}
v___jp_3540_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___f_3551_; lean_object* v___x_3552_; 
v___x_3546_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3545_, v___x_2980_);
v___x_3547_ = lean_box(v___x_2893_);
v___x_3548_ = lean_box(v___x_2980_);
v___x_3549_ = lean_box(v_useReducible_2896_);
v___x_3550_ = lean_box(v___x_2906_);
lean_inc_ref(v___x_2891_);
lean_inc_ref(v___x_2890_);
lean_inc_ref(v___x_2889_);
lean_inc_ref(v___f_2897_);
lean_inc(v___x_2901_);
lean_inc_ref(v___x_2898_);
lean_inc(v_usingArg_2904_);
lean_inc(v___x_2892_);
lean_inc(v_tk_2888_);
lean_inc(v___x_2903_);
v___f_3551_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3551_, 0, v___x_2903_);
lean_closure_set(v___f_3551_, 1, v_tk_2888_);
lean_closure_set(v___f_3551_, 2, v___x_2985_);
lean_closure_set(v___f_3551_, 3, v___x_2892_);
lean_closure_set(v___f_3551_, 4, v___x_3546_);
lean_closure_set(v___f_3551_, 5, v___y_3541_);
lean_closure_set(v___f_3551_, 6, v___x_3547_);
lean_closure_set(v___f_3551_, 7, v_usingArg_2904_);
lean_closure_set(v___f_3551_, 8, v___x_2898_);
lean_closure_set(v___f_3551_, 9, v___x_3548_);
lean_closure_set(v___f_3551_, 10, v___x_3549_);
lean_closure_set(v___f_3551_, 11, v___x_3550_);
lean_closure_set(v___f_3551_, 12, v___x_2901_);
lean_closure_set(v___f_3551_, 13, v___f_2897_);
lean_closure_set(v___f_3551_, 14, v___x_2889_);
lean_closure_set(v___f_3551_, 15, v___x_2890_);
lean_closure_set(v___f_3551_, 16, v___x_2891_);
lean_closure_set(v___f_3551_, 17, v___f_2907_);
lean_closure_set(v___f_3551_, 18, v_a_2978_);
lean_closure_set(v___f_3551_, 19, v_usingTk_x3f_2908_);
v___x_3552_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3542_, v___f_3551_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_3542_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
v___x_3554_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2920_);
v___x_3555_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3556_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_3554_, v___x_3555_);
lean_dec_ref(v___x_3554_);
if (v___x_3556_ == 0)
{
if (lean_obj_tag(v_squeeze_2909_) == 0)
{
v___y_3536_ = v_a_3553_;
v___y_3537_ = v___y_3543_;
v___y_3538_ = v___y_3544_;
v___y_3539_ = v___x_3556_;
goto v___jp_3535_;
}
else
{
v___y_3536_ = v_a_3553_;
v___y_3537_ = v___y_3543_;
v___y_3538_ = v___y_3544_;
v___y_3539_ = v___x_2906_;
goto v___jp_3535_;
}
}
else
{
v___y_3523_ = v_a_3553_;
v___y_3524_ = v___y_3543_;
v___y_3525_ = v___y_3544_;
goto v___jp_3522_;
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec(v___y_3544_);
lean_dec(v___x_2983_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v_usingArg_2904_);
lean_dec(v___x_2903_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3557_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3552_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3552_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
v___jp_3565_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3569_ = l_Array_append___redArg(v___x_2986_, v___y_3568_);
lean_dec_ref(v___y_3568_);
lean_inc_n(v___x_2981_, 2);
v___x_3570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3570_, 0, v___x_2981_);
lean_ctor_set(v___x_3570_, 1, v___x_2985_);
lean_ctor_set(v___x_3570_, 2, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3571_, 0, v___x_2981_);
lean_ctor_set(v___x_3571_, 1, v___x_2985_);
lean_ctor_set(v___x_3571_, 2, v___x_2986_);
lean_inc(v___x_2983_);
v___x_3572_ = l_Lean_Syntax_node6(v___x_2981_, v___x_2983_, v___x_2984_, v___x_2905_, v___y_3567_, v___y_3566_, v___x_3570_, v___x_3571_);
v___x_3573_ = 0;
v___x_3574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3575_ = lean_box(v___x_2980_);
v___x_3576_ = lean_box(v___x_3573_);
v___x_3577_ = lean_box(v___x_2980_);
lean_inc(v___x_3572_);
v___x_3578_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3578_, 0, v___x_3572_);
lean_closure_set(v___x_3578_, 1, v___x_3575_);
lean_closure_set(v___x_3578_, 2, v___x_3576_);
lean_closure_set(v___x_3578_, 3, v___x_3577_);
lean_closure_set(v___x_3578_, 4, v___x_3574_);
v___x_3579_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3578_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
if (lean_obj_tag(v_unfold_2910_) == 0)
{
lean_object* v_ctx_3581_; lean_object* v_simprocs_3582_; lean_object* v_dischargeWrapper_3583_; 
v_ctx_3581_ = lean_ctor_get(v_a_3580_, 0);
lean_inc_ref(v_ctx_3581_);
v_simprocs_3582_ = lean_ctor_get(v_a_3580_, 1);
lean_inc_ref(v_simprocs_3582_);
v_dischargeWrapper_3583_ = lean_ctor_get(v_a_3580_, 2);
lean_inc(v_dischargeWrapper_3583_);
lean_dec(v_a_3580_);
v___y_3541_ = v_simprocs_3582_;
v___y_3542_ = v_dischargeWrapper_3583_;
v___y_3543_ = v___x_2980_;
v___y_3544_ = v___x_3572_;
v___y_3545_ = v_ctx_3581_;
goto v___jp_3540_;
}
else
{
if (v___x_2906_ == 0)
{
lean_object* v_ctx_3584_; lean_object* v_simprocs_3585_; lean_object* v_dischargeWrapper_3586_; 
v_ctx_3584_ = lean_ctor_get(v_a_3580_, 0);
lean_inc_ref(v_ctx_3584_);
v_simprocs_3585_ = lean_ctor_get(v_a_3580_, 1);
lean_inc_ref(v_simprocs_3585_);
v_dischargeWrapper_3586_ = lean_ctor_get(v_a_3580_, 2);
lean_inc(v_dischargeWrapper_3586_);
lean_dec(v_a_3580_);
v___y_3541_ = v_simprocs_3585_;
v___y_3542_ = v_dischargeWrapper_3586_;
v___y_3543_ = v___x_2906_;
v___y_3544_ = v___x_3572_;
v___y_3545_ = v_ctx_3584_;
goto v___jp_3540_;
}
else
{
lean_object* v_ctx_3587_; lean_object* v_simprocs_3588_; lean_object* v_dischargeWrapper_3589_; lean_object* v___x_3590_; 
v_ctx_3587_ = lean_ctor_get(v_a_3580_, 0);
lean_inc_ref(v_ctx_3587_);
v_simprocs_3588_ = lean_ctor_get(v_a_3580_, 1);
lean_inc_ref(v_simprocs_3588_);
v_dischargeWrapper_3589_ = lean_ctor_get(v_a_3580_, 2);
lean_inc(v_dischargeWrapper_3589_);
lean_dec(v_a_3580_);
v___x_3590_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3587_);
v___y_3541_ = v_simprocs_3588_;
v___y_3542_ = v_dischargeWrapper_3589_;
v___y_3543_ = v___x_2906_;
v___y_3544_ = v___x_3572_;
v___y_3545_ = v___x_3590_;
goto v___jp_3540_;
}
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v___x_3572_);
lean_dec(v___x_2983_);
lean_dec(v_a_2978_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v_usingTk_x3f_2908_);
lean_dec_ref(v___f_2907_);
lean_dec(v_usingArg_2904_);
lean_dec(v___x_2903_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3591_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3579_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3579_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
v___jp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = l_Array_append___redArg(v___x_2986_, v___y_3601_);
lean_dec_ref(v___y_3601_);
lean_inc(v___x_2981_);
v___x_3603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3603_, 0, v___x_2981_);
lean_ctor_set(v___x_3603_, 1, v___x_2985_);
lean_ctor_set(v___x_3603_, 2, v___x_3602_);
if (lean_obj_tag(v_args_2911_) == 1)
{
lean_object* v_val_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v_val_3604_ = lean_ctor_get(v_args_2911_, 0);
v___x_3605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_2981_, 3);
v___x_3606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_2981_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Array_append___redArg(v___x_2986_, v_val_3604_);
v___x_3608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3608_, 0, v___x_2981_);
lean_ctor_set(v___x_3608_, 1, v___x_2985_);
lean_ctor_set(v___x_3608_, 2, v___x_3607_);
v___x_3609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3610_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_2981_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = l_Array_mkArray3___redArg(v___x_3606_, v___x_3608_, v___x_3610_);
v___y_3566_ = v___x_3603_;
v___y_3567_ = v___y_3600_;
v___y_3568_ = v___x_3611_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3566_ = v___x_3603_;
v___y_3567_ = v___y_3600_;
v___y_3568_ = v___x_3612_;
goto v___jp_3565_;
}
}
v___jp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = l_Array_append___redArg(v___x_2986_, v___y_3614_);
lean_dec_ref(v___y_3614_);
lean_inc(v___x_2981_);
v___x_3616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3616_, 0, v___x_2981_);
lean_ctor_set(v___x_3616_, 1, v___x_2985_);
lean_ctor_set(v___x_3616_, 2, v___x_3615_);
if (lean_obj_tag(v_only_2912_) == 1)
{
lean_object* v_val_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_val_3617_ = lean_ctor_get(v_only_2912_, 0);
v___x_3618_ = l_Lean_SourceInfo_fromRef(v_val_3617_, v___x_2893_);
v___x_3619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = l_Array_mkArray1___redArg(v___x_3620_);
v___y_3600_ = v___x_3616_;
v___y_3601_ = v___x_3621_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___y_3600_ = v___x_3616_;
v___y_3601_ = v___x_3622_;
goto v___jp_3599_;
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec(v_usingTk_x3f_2908_);
lean_dec_ref(v___f_2907_);
lean_dec(v___x_2905_);
lean_dec(v_usingArg_2904_);
lean_dec(v___x_2903_);
lean_dec(v___x_2901_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___f_2897_);
lean_dec(v___x_2895_);
lean_dec(v___x_2894_);
lean_dec(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2889_);
lean_dec(v_tk_2888_);
v_a_3627_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_2977_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_2977_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
v___jp_2923_:
{
lean_object* v_diag_2925_; lean_object* v___x_2926_; 
v_diag_2925_ = lean_ctor_get(v___y_2924_, 1);
lean_inc_ref(v_diag_2925_);
lean_dec_ref(v___y_2924_);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_diag_2925_);
return v___x_2926_;
}
v___jp_2927_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v_stx_2929_);
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
lean_ctor_set(v___x_2936_, 2, v___x_2935_);
lean_ctor_set(v___x_2936_, 3, v___x_2935_);
lean_ctor_set(v___x_2936_, 4, v___x_2935_);
lean_ctor_set(v___x_2936_, 5, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_ref_2931_);
v___x_2938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0));
v___x_2939_ = 4;
v___x_2940_ = l_Lean_MessageData_nil;
v___x_2941_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2888_, v___x_2936_, v___x_2937_, v___x_2938_, v___x_2935_, v___x_2939_, v___x_2940_, v___y_2930_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2930_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_dec_ref_known(v___x_2941_, 1);
v___y_2924_ = v___y_2928_;
goto v___jp_2923_;
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec_ref(v___y_2928_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
v___jp_2950_:
{
lean_object* v_ref_2955_; 
v_ref_2955_ = lean_ctor_get(v___y_2953_, 2);
lean_inc(v_ref_2955_);
v___y_2928_ = v___y_2951_;
v_stx_2929_ = v_stx_2952_;
v___y_2930_ = v___y_2953_;
v_ref_2931_ = v_ref_2955_;
v___y_2932_ = v___y_2954_;
goto v___jp_2927_;
}
v___jp_2956_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4);
v___x_2967_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_2966_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___y_2951_ = v___y_2957_;
v_stx_2952_ = v_a_2968_;
v___y_2953_ = v___y_2964_;
v___y_2954_ = v___y_2965_;
goto v___jp_2950_;
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v___y_2957_);
lean_dec(v_tk_2888_);
v_a_2969_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2967_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2967_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object** _args){
lean_object* v_tk_3635_ = _args[0];
lean_object* v___x_3636_ = _args[1];
lean_object* v___x_3637_ = _args[2];
lean_object* v___x_3638_ = _args[3];
lean_object* v___x_3639_ = _args[4];
lean_object* v___x_3640_ = _args[5];
lean_object* v___x_3641_ = _args[6];
lean_object* v___x_3642_ = _args[7];
lean_object* v_useReducible_3643_ = _args[8];
lean_object* v___f_3644_ = _args[9];
lean_object* v___x_3645_ = _args[10];
lean_object* v___x_3646_ = _args[11];
lean_object* v___x_3647_ = _args[12];
lean_object* v___x_3648_ = _args[13];
lean_object* v___x_3649_ = _args[14];
lean_object* v___x_3650_ = _args[15];
lean_object* v_usingArg_3651_ = _args[16];
lean_object* v___x_3652_ = _args[17];
lean_object* v___x_3653_ = _args[18];
lean_object* v___f_3654_ = _args[19];
lean_object* v_usingTk_x3f_3655_ = _args[20];
lean_object* v_squeeze_3656_ = _args[21];
lean_object* v_unfold_3657_ = _args[22];
lean_object* v_args_3658_ = _args[23];
lean_object* v_only_3659_ = _args[24];
lean_object* v___y_3660_ = _args[25];
lean_object* v___y_3661_ = _args[26];
lean_object* v___y_3662_ = _args[27];
lean_object* v___y_3663_ = _args[28];
lean_object* v___y_3664_ = _args[29];
lean_object* v___y_3665_ = _args[30];
lean_object* v___y_3666_ = _args[31];
lean_object* v___y_3667_ = _args[32];
lean_object* v___y_3668_ = _args[33];
lean_object* v___y_3669_ = _args[34];
_start:
{
uint8_t v___x_96988__boxed_3670_; uint8_t v_useReducible_boxed_3671_; uint8_t v___x_96999__boxed_3672_; lean_object* v_res_3673_; 
v___x_96988__boxed_3670_ = lean_unbox(v___x_3640_);
v_useReducible_boxed_3671_ = lean_unbox(v_useReducible_3643_);
v___x_96999__boxed_3672_ = lean_unbox(v___x_3653_);
v_res_3673_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3635_, v___x_3636_, v___x_3637_, v___x_3638_, v___x_3639_, v___x_96988__boxed_3670_, v___x_3641_, v___x_3642_, v_useReducible_boxed_3671_, v___f_3644_, v___x_3645_, v___x_3646_, v___x_3647_, v___x_3648_, v___x_3649_, v___x_3650_, v_usingArg_3651_, v___x_3652_, v___x_96999__boxed_3672_, v___f_3654_, v_usingTk_x3f_3655_, v_squeeze_3656_, v_unfold_3657_, v_args_3658_, v_only_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v_only_3659_);
lean_dec(v_args_3658_);
lean_dec(v_unfold_3657_);
lean_dec(v_squeeze_3656_);
lean_dec(v___x_3649_);
lean_dec(v___x_3647_);
lean_dec(v___x_3646_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3699_, lean_object* v_stx_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_3711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3712_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_3713_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3700_);
v___x_3715_ = l_Lean_Syntax_isOfKind(v_stx_3700_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; 
lean_dec(v_stx_3700_);
v___x_3716_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3716_;
}
else
{
lean_object* v___f_3717_; lean_object* v___x_3718_; lean_object* v_tk_3719_; lean_object* v___x_3720_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; uint8_t v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; uint8_t v___y_3772_; lean_object* v___y_3773_; lean_object* v_usingTk_x3f_3774_; lean_object* v_usingArg_3775_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; uint8_t v___y_3805_; lean_object* v___y_3806_; lean_object* v_args_3807_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; uint8_t v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v_only_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v_unfold_3863_; lean_object* v_squeeze_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___f_3717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3718_ = lean_unsigned_to_nat(0u);
v_tk_3719_ = l_Lean_Syntax_getArg(v_stx_3700_, v___x_3718_);
v___x_3720_ = lean_unsigned_to_nat(1u);
v___x_3899_ = l_Lean_Syntax_getArg(v_stx_3700_, v___x_3720_);
v___x_3900_ = l_Lean_Syntax_isNone(v___x_3899_);
if (v___x_3900_ == 0)
{
uint8_t v___x_3901_; 
lean_inc(v___x_3899_);
v___x_3901_ = l_Lean_Syntax_matchesNull(v___x_3899_, v___x_3720_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
lean_dec(v___x_3899_);
lean_dec(v_tk_3719_);
lean_dec(v_stx_3700_);
v___x_3902_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3902_;
}
else
{
lean_object* v_squeeze_3903_; lean_object* v___x_3904_; 
v_squeeze_3903_ = l_Lean_Syntax_getArg(v___x_3899_, v___x_3718_);
lean_dec(v___x_3899_);
v___x_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3904_, 0, v_squeeze_3903_);
v_squeeze_3882_ = v___x_3904_;
v___y_3883_ = v_a_3701_;
v___y_3884_ = v_a_3702_;
v___y_3885_ = v_a_3703_;
v___y_3886_ = v_a_3704_;
v___y_3887_ = v_a_3705_;
v___y_3888_ = v_a_3706_;
v___y_3889_ = v_a_3707_;
v___y_3890_ = v_a_3708_;
goto v___jp_3881_;
}
}
else
{
lean_object* v___x_3905_; 
lean_dec(v___x_3899_);
v___x_3905_ = lean_box(0);
v_squeeze_3882_ = v___x_3905_;
v___y_3883_ = v_a_3701_;
v___y_3884_ = v_a_3702_;
v___y_3885_ = v_a_3703_;
v___y_3886_ = v_a_3704_;
v___y_3887_ = v_a_3705_;
v___y_3888_ = v_a_3706_;
v___y_3889_ = v_a_3707_;
v___y_3890_ = v_a_3708_;
goto v___jp_3881_;
}
v___jp_3721_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___f_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___f_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3744_ = lean_box(v___x_3715_);
v___x_3745_ = lean_box(v___y_3741_);
lean_inc(v___y_3729_);
lean_inc(v___y_3733_);
lean_inc(v___y_3743_);
lean_inc(v___y_3738_);
lean_inc(v___y_3727_);
lean_inc(v___y_3736_);
v___f_3746_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 22, 12);
lean_closure_set(v___f_3746_, 0, v___y_3736_);
lean_closure_set(v___f_3746_, 1, v___x_3718_);
lean_closure_set(v___f_3746_, 2, v___y_3727_);
lean_closure_set(v___f_3746_, 3, v___y_3738_);
lean_closure_set(v___f_3746_, 4, v___x_3744_);
lean_closure_set(v___f_3746_, 5, v___x_3710_);
lean_closure_set(v___f_3746_, 6, v___x_3711_);
lean_closure_set(v___f_3746_, 7, v___x_3712_);
lean_closure_set(v___f_3746_, 8, v___y_3743_);
lean_closure_set(v___f_3746_, 9, v___y_3733_);
lean_closure_set(v___f_3746_, 10, v___x_3745_);
lean_closure_set(v___f_3746_, 11, v___y_3729_);
v___x_3747_ = lean_box(v___x_3715_);
v___x_3748_ = lean_box(v_useReducible_3699_);
v___x_3749_ = lean_box(v___y_3741_);
lean_inc(v___y_3728_);
lean_inc(v___y_3739_);
v___f_3750_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3750_, 0, v_tk_3719_);
lean_closure_set(v___f_3750_, 1, v___x_3710_);
lean_closure_set(v___f_3750_, 2, v___x_3711_);
lean_closure_set(v___f_3750_, 3, v___x_3712_);
lean_closure_set(v___f_3750_, 4, v___x_3718_);
lean_closure_set(v___f_3750_, 5, v___x_3747_);
lean_closure_set(v___f_3750_, 6, v___y_3739_);
lean_closure_set(v___f_3750_, 7, v___x_3714_);
lean_closure_set(v___f_3750_, 8, v___x_3748_);
lean_closure_set(v___f_3750_, 9, v___f_3717_);
lean_closure_set(v___f_3750_, 10, v___x_3713_);
lean_closure_set(v___f_3750_, 11, v___y_3731_);
lean_closure_set(v___f_3750_, 12, v___y_3732_);
lean_closure_set(v___f_3750_, 13, v___x_3720_);
lean_closure_set(v___f_3750_, 14, v___y_3728_);
lean_closure_set(v___f_3750_, 15, v___y_3724_);
lean_closure_set(v___f_3750_, 16, v___y_3730_);
lean_closure_set(v___f_3750_, 17, v___y_3736_);
lean_closure_set(v___f_3750_, 18, v___x_3749_);
lean_closure_set(v___f_3750_, 19, v___f_3746_);
lean_closure_set(v___f_3750_, 20, v___y_3725_);
lean_closure_set(v___f_3750_, 21, v___y_3729_);
lean_closure_set(v___f_3750_, 22, v___y_3733_);
lean_closure_set(v___f_3750_, 23, v___y_3727_);
lean_closure_set(v___f_3750_, 24, v___y_3738_);
lean_closure_set(v___f_3750_, 25, v___y_3743_);
v___x_3751_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3751_, 0, v___f_3750_);
v___x_3752_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3751_, v___y_3723_, v___y_3726_, v___y_3735_, v___y_3737_, v___y_3742_, v___y_3722_, v___y_3740_, v___y_3734_);
return v___x_3752_;
}
v___jp_3753_:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_Syntax_getOptional_x3f(v___y_3770_);
lean_dec(v___y_3770_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_box(0);
v___y_3722_ = v___y_3754_;
v___y_3723_ = v___y_3755_;
v___y_3724_ = v___y_3756_;
v___y_3725_ = v_usingTk_x3f_3774_;
v___y_3726_ = v___y_3757_;
v___y_3727_ = v___y_3758_;
v___y_3728_ = v___y_3759_;
v___y_3729_ = v___y_3760_;
v___y_3730_ = v_usingArg_3775_;
v___y_3731_ = v___y_3761_;
v___y_3732_ = v___y_3762_;
v___y_3733_ = v___y_3763_;
v___y_3734_ = v___y_3764_;
v___y_3735_ = v___y_3766_;
v___y_3736_ = v___y_3765_;
v___y_3737_ = v___y_3769_;
v___y_3738_ = v___y_3768_;
v___y_3739_ = v___y_3767_;
v___y_3740_ = v___y_3771_;
v___y_3741_ = v___y_3772_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v___x_3777_;
goto v___jp_3721_;
}
else
{
lean_object* v_val_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
v_val_3778_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3776_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_val_3778_);
lean_dec(v___x_3776_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_val_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
v___y_3722_ = v___y_3754_;
v___y_3723_ = v___y_3755_;
v___y_3724_ = v___y_3756_;
v___y_3725_ = v_usingTk_x3f_3774_;
v___y_3726_ = v___y_3757_;
v___y_3727_ = v___y_3758_;
v___y_3728_ = v___y_3759_;
v___y_3729_ = v___y_3760_;
v___y_3730_ = v_usingArg_3775_;
v___y_3731_ = v___y_3761_;
v___y_3732_ = v___y_3762_;
v___y_3733_ = v___y_3763_;
v___y_3734_ = v___y_3764_;
v___y_3735_ = v___y_3766_;
v___y_3736_ = v___y_3765_;
v___y_3737_ = v___y_3769_;
v___y_3738_ = v___y_3768_;
v___y_3739_ = v___y_3767_;
v___y_3740_ = v___y_3771_;
v___y_3741_ = v___y_3772_;
v___y_3742_ = v___y_3773_;
v___y_3743_ = v___x_3783_;
goto v___jp_3721_;
}
}
}
}
v___jp_3786_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v___x_3808_ = lean_unsigned_to_nat(4u);
v___x_3809_ = l_Lean_Syntax_getArg(v___y_3794_, v___x_3808_);
lean_dec(v___y_3794_);
v___x_3810_ = l_Lean_Syntax_isNone(v___x_3809_);
if (v___x_3810_ == 0)
{
uint8_t v___x_3811_; 
lean_inc(v___x_3809_);
v___x_3811_ = l_Lean_Syntax_matchesNull(v___x_3809_, v___y_3795_);
lean_dec(v___y_3795_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; 
lean_dec(v___x_3809_);
lean_dec(v_args_3807_);
lean_dec(v___y_3803_);
lean_dec(v___y_3801_);
lean_dec(v___y_3798_);
lean_dec(v___y_3796_);
lean_dec(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec(v___y_3789_);
lean_dec(v_tk_3719_);
v___x_3812_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3812_;
}
else
{
lean_object* v_usingTk_x3f_3813_; lean_object* v_usingArg_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_usingTk_x3f_3813_ = l_Lean_Syntax_getArg(v___x_3809_, v___x_3718_);
v_usingArg_3814_ = l_Lean_Syntax_getArg(v___x_3809_, v___x_3720_);
lean_dec(v___x_3809_);
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_usingTk_x3f_3813_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v_usingArg_3814_);
v___y_3754_ = v___y_3787_;
v___y_3755_ = v___y_3788_;
v___y_3756_ = v___y_3789_;
v___y_3757_ = v___y_3790_;
v___y_3758_ = v_args_3807_;
v___y_3759_ = v___y_3791_;
v___y_3760_ = v___y_3792_;
v___y_3761_ = v___x_3808_;
v___y_3762_ = v___y_3793_;
v___y_3763_ = v___y_3796_;
v___y_3764_ = v___y_3797_;
v___y_3765_ = v___y_3798_;
v___y_3766_ = v___y_3799_;
v___y_3767_ = v___y_3802_;
v___y_3768_ = v___y_3801_;
v___y_3769_ = v___y_3800_;
v___y_3770_ = v___y_3803_;
v___y_3771_ = v___y_3804_;
v___y_3772_ = v___y_3805_;
v___y_3773_ = v___y_3806_;
v_usingTk_x3f_3774_ = v___x_3815_;
v_usingArg_3775_ = v___x_3816_;
goto v___jp_3753_;
}
}
else
{
lean_object* v___x_3817_; 
lean_dec(v___x_3809_);
lean_dec(v___y_3795_);
v___x_3817_ = lean_box(0);
v___y_3754_ = v___y_3787_;
v___y_3755_ = v___y_3788_;
v___y_3756_ = v___y_3789_;
v___y_3757_ = v___y_3790_;
v___y_3758_ = v_args_3807_;
v___y_3759_ = v___y_3791_;
v___y_3760_ = v___y_3792_;
v___y_3761_ = v___x_3808_;
v___y_3762_ = v___y_3793_;
v___y_3763_ = v___y_3796_;
v___y_3764_ = v___y_3797_;
v___y_3765_ = v___y_3798_;
v___y_3766_ = v___y_3799_;
v___y_3767_ = v___y_3802_;
v___y_3768_ = v___y_3801_;
v___y_3769_ = v___y_3800_;
v___y_3770_ = v___y_3803_;
v___y_3771_ = v___y_3804_;
v___y_3772_ = v___y_3805_;
v___y_3773_ = v___y_3806_;
v_usingTk_x3f_3774_ = v___x_3817_;
v_usingArg_3775_ = v___x_3817_;
goto v___jp_3753_;
}
}
v___jp_3818_:
{
lean_object* v___x_3840_; uint8_t v___x_3841_; 
v___x_3840_ = l_Lean_Syntax_getArg(v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
v___x_3841_ = l_Lean_Syntax_isNone(v___x_3840_);
if (v___x_3841_ == 0)
{
uint8_t v___x_3842_; 
lean_inc(v___x_3840_);
v___x_3842_ = l_Lean_Syntax_matchesNull(v___x_3840_, v___x_3720_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; 
lean_dec(v___x_3840_);
lean_dec(v_only_3831_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec(v___y_3824_);
lean_dec(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec(v_tk_3719_);
v___x_3843_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v___x_3844_ = l_Lean_Syntax_getArg(v___x_3840_, v___x_3718_);
lean_dec(v___x_3840_);
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3844_);
v___x_3846_ = l_Lean_Syntax_isOfKind(v___x_3844_, v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
lean_dec(v___x_3844_);
lean_dec(v_only_3831_);
lean_dec(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec(v___y_3824_);
lean_dec(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec(v_tk_3719_);
v___x_3847_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3847_;
}
else
{
lean_object* v___x_3848_; lean_object* v_args_3849_; lean_object* v___x_3850_; 
v___x_3848_ = l_Lean_Syntax_getArg(v___x_3844_, v___x_3720_);
lean_dec(v___x_3844_);
v_args_3849_ = l_Lean_Syntax_getArgs(v___x_3848_);
lean_dec(v___x_3848_);
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v_args_3849_);
v___y_3787_ = v___y_3837_;
v___y_3788_ = v___y_3832_;
v___y_3789_ = v___y_3819_;
v___y_3790_ = v___y_3833_;
v___y_3791_ = v___y_3823_;
v___y_3792_ = v___y_3824_;
v___y_3793_ = v___y_3826_;
v___y_3794_ = v___y_3829_;
v___y_3795_ = v___y_3827_;
v___y_3796_ = v___y_3820_;
v___y_3797_ = v___y_3839_;
v___y_3798_ = v___y_3821_;
v___y_3799_ = v___y_3834_;
v___y_3800_ = v___y_3835_;
v___y_3801_ = v_only_3831_;
v___y_3802_ = v___y_3822_;
v___y_3803_ = v___y_3828_;
v___y_3804_ = v___y_3838_;
v___y_3805_ = v___y_3825_;
v___y_3806_ = v___y_3836_;
v_args_3807_ = v___x_3850_;
goto v___jp_3786_;
}
}
}
else
{
lean_object* v___x_3851_; 
lean_dec(v___x_3840_);
v___x_3851_ = lean_box(0);
v___y_3787_ = v___y_3837_;
v___y_3788_ = v___y_3832_;
v___y_3789_ = v___y_3819_;
v___y_3790_ = v___y_3833_;
v___y_3791_ = v___y_3823_;
v___y_3792_ = v___y_3824_;
v___y_3793_ = v___y_3826_;
v___y_3794_ = v___y_3829_;
v___y_3795_ = v___y_3827_;
v___y_3796_ = v___y_3820_;
v___y_3797_ = v___y_3839_;
v___y_3798_ = v___y_3821_;
v___y_3799_ = v___y_3834_;
v___y_3800_ = v___y_3835_;
v___y_3801_ = v_only_3831_;
v___y_3802_ = v___y_3822_;
v___y_3803_ = v___y_3828_;
v___y_3804_ = v___y_3838_;
v___y_3805_ = v___y_3825_;
v___y_3806_ = v___y_3836_;
v_args_3807_ = v___x_3851_;
goto v___jp_3786_;
}
}
v___jp_3852_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3864_ = lean_unsigned_to_nat(3u);
v___x_3865_ = l_Lean_Syntax_getArg(v_stx_3700_, v___x_3864_);
lean_dec(v_stx_3700_);
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3865_);
v___x_3867_ = l_Lean_Syntax_isOfKind(v___x_3865_, v___x_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; 
lean_dec(v___x_3865_);
lean_dec(v_unfold_3863_);
lean_dec(v___y_3860_);
lean_dec(v___y_3854_);
lean_dec(v_tk_3719_);
v___x_3868_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3868_;
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; 
v___x_3869_ = l_Lean_Syntax_getArg(v___x_3865_, v___x_3718_);
v___x_3870_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3869_);
v___x_3871_ = l_Lean_Syntax_isOfKind(v___x_3869_, v___x_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
lean_dec(v___x_3869_);
lean_dec(v___x_3865_);
lean_dec(v_unfold_3863_);
lean_dec(v___y_3860_);
lean_dec(v___y_3854_);
lean_dec(v_tk_3719_);
v___x_3872_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3872_;
}
else
{
lean_object* v___x_3873_; lean_object* v___x_3874_; uint8_t v___x_3875_; 
v___x_3873_ = l_Lean_Syntax_getArg(v___x_3865_, v___x_3720_);
v___x_3874_ = l_Lean_Syntax_getArg(v___x_3865_, v___y_3854_);
v___x_3875_ = l_Lean_Syntax_isNone(v___x_3874_);
if (v___x_3875_ == 0)
{
uint8_t v___x_3876_; 
lean_inc(v___x_3874_);
v___x_3876_ = l_Lean_Syntax_matchesNull(v___x_3874_, v___x_3720_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; 
lean_dec(v___x_3874_);
lean_dec(v___x_3873_);
lean_dec(v___x_3869_);
lean_dec(v___x_3865_);
lean_dec(v_unfold_3863_);
lean_dec(v___y_3860_);
lean_dec(v___y_3854_);
lean_dec(v_tk_3719_);
v___x_3877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3877_;
}
else
{
lean_object* v_only_3878_; lean_object* v___x_3879_; 
v_only_3878_ = l_Lean_Syntax_getArg(v___x_3874_, v___x_3718_);
lean_dec(v___x_3874_);
v___x_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3879_, 0, v_only_3878_);
lean_inc(v___y_3854_);
v___y_3819_ = v___y_3854_;
v___y_3820_ = v_unfold_3863_;
v___y_3821_ = v___x_3869_;
v___y_3822_ = v___x_3866_;
v___y_3823_ = v___x_3870_;
v___y_3824_ = v___y_3860_;
v___y_3825_ = v___x_3867_;
v___y_3826_ = v___x_3864_;
v___y_3827_ = v___y_3854_;
v___y_3828_ = v___x_3873_;
v___y_3829_ = v___x_3865_;
v___y_3830_ = v___x_3864_;
v_only_3831_ = v___x_3879_;
v___y_3832_ = v___y_3861_;
v___y_3833_ = v___y_3853_;
v___y_3834_ = v___y_3858_;
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3862_;
v___y_3837_ = v___y_3859_;
v___y_3838_ = v___y_3855_;
v___y_3839_ = v___y_3856_;
goto v___jp_3818_;
}
}
else
{
lean_object* v___x_3880_; 
lean_dec(v___x_3874_);
v___x_3880_ = lean_box(0);
lean_inc(v___y_3854_);
v___y_3819_ = v___y_3854_;
v___y_3820_ = v_unfold_3863_;
v___y_3821_ = v___x_3869_;
v___y_3822_ = v___x_3866_;
v___y_3823_ = v___x_3870_;
v___y_3824_ = v___y_3860_;
v___y_3825_ = v___x_3867_;
v___y_3826_ = v___x_3864_;
v___y_3827_ = v___y_3854_;
v___y_3828_ = v___x_3873_;
v___y_3829_ = v___x_3865_;
v___y_3830_ = v___x_3864_;
v_only_3831_ = v___x_3880_;
v___y_3832_ = v___y_3861_;
v___y_3833_ = v___y_3853_;
v___y_3834_ = v___y_3858_;
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3862_;
v___y_3837_ = v___y_3859_;
v___y_3838_ = v___y_3855_;
v___y_3839_ = v___y_3856_;
goto v___jp_3818_;
}
}
}
}
v___jp_3881_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3891_ = lean_unsigned_to_nat(2u);
v___x_3892_ = l_Lean_Syntax_getArg(v_stx_3700_, v___x_3891_);
v___x_3893_ = l_Lean_Syntax_isNone(v___x_3892_);
if (v___x_3893_ == 0)
{
uint8_t v___x_3894_; 
lean_inc(v___x_3892_);
v___x_3894_ = l_Lean_Syntax_matchesNull(v___x_3892_, v___x_3720_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
lean_dec(v___x_3892_);
lean_dec(v_squeeze_3882_);
lean_dec(v_tk_3719_);
lean_dec(v_stx_3700_);
v___x_3895_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3895_;
}
else
{
lean_object* v_unfold_3896_; lean_object* v___x_3897_; 
v_unfold_3896_ = l_Lean_Syntax_getArg(v___x_3892_, v___x_3718_);
lean_dec(v___x_3892_);
v___x_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3897_, 0, v_unfold_3896_);
v___y_3853_ = v___y_3884_;
v___y_3854_ = v___x_3891_;
v___y_3855_ = v___y_3889_;
v___y_3856_ = v___y_3890_;
v___y_3857_ = v___y_3886_;
v___y_3858_ = v___y_3885_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v_squeeze_3882_;
v___y_3861_ = v___y_3883_;
v___y_3862_ = v___y_3887_;
v_unfold_3863_ = v___x_3897_;
goto v___jp_3852_;
}
}
else
{
lean_object* v___x_3898_; 
lean_dec(v___x_3892_);
v___x_3898_ = lean_box(0);
v___y_3853_ = v___y_3884_;
v___y_3854_ = v___x_3891_;
v___y_3855_ = v___y_3889_;
v___y_3856_ = v___y_3890_;
v___y_3857_ = v___y_3886_;
v___y_3858_ = v___y_3885_;
v___y_3859_ = v___y_3888_;
v___y_3860_ = v_squeeze_3882_;
v___y_3861_ = v___y_3883_;
v___y_3862_ = v___y_3887_;
v_unfold_3863_ = v___x_3898_;
goto v___jp_3852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3906_, lean_object* v_stx_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
uint8_t v_useReducible_boxed_3917_; lean_object* v_res_3918_; 
v_useReducible_boxed_3917_ = lean_unbox(v_useReducible_3906_);
v_res_3918_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3917_, v_stx_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_3919_, lean_object* v_val_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_3919_, v_val_3920_, v___y_3926_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_3931_, lean_object* v_val_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_3931_, v_val_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_o_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_3943_, v___y_3951_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___boxed(lean_object* v_o_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(v_o_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_3965_, lean_object* v_msg_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_3966_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_3977_, lean_object* v_msg_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_3977_, v_msg_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v_00_u03b1_3989_, lean_object* v_x_3990_, lean_object* v_mkInfoTree_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_3990_, v_mkInfoTree_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v_00_u03b1_4002_, lean_object* v_x_4003_, lean_object* v_mkInfoTree_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v_00_u03b1_4002_, v_x_4003_, v_mkInfoTree_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_00_u03b2_4015_, lean_object* v_x_4016_, lean_object* v_x_4017_, lean_object* v_x_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_x_4016_, v_x_4017_, v_x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_4020_, lean_object* v_x_4021_, size_t v_x_4022_, size_t v_x_4023_, lean_object* v_x_4024_, lean_object* v_x_4025_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_4021_, v_x_4022_, v_x_4023_, v_x_4024_, v_x_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_4027_, lean_object* v_x_4028_, lean_object* v_x_4029_, lean_object* v_x_4030_, lean_object* v_x_4031_, lean_object* v_x_4032_){
_start:
{
size_t v_x_99152__boxed_4033_; size_t v_x_99153__boxed_4034_; lean_object* v_res_4035_; 
v_x_99152__boxed_4033_ = lean_unbox_usize(v_x_4029_);
lean_dec(v_x_4029_);
v_x_99153__boxed_4034_ = lean_unbox_usize(v_x_4030_);
lean_dec(v_x_4030_);
v_res_4035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_4027_, v_x_4028_, v_x_99152__boxed_4033_, v_x_99153__boxed_4034_, v_x_4031_, v_x_4032_);
return v_res_4035_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_4036_, lean_object* v_m_4037_, lean_object* v_a_4038_){
_start:
{
uint8_t v___x_4039_; 
v___x_4039_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_4037_, v_a_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_4040_, lean_object* v_m_4041_, lean_object* v_a_4042_){
_start:
{
uint8_t v_res_4043_; lean_object* v_r_4044_; 
v_res_4043_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(v_00_u03b2_4040_, v_m_4041_, v_a_4042_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_m_4041_);
v_r_4044_ = lean_box(v_res_4043_);
return v_r_4044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_4045_, lean_object* v_m_4046_, lean_object* v_a_4047_, lean_object* v_b_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_m_4046_, v_a_4047_, v_b_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(lean_object* v_mvarId_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_4050_, v___y_4051_, v___y_4057_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___boxed(lean_object* v_mvarId_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(v_mvarId_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v_mvarId_4062_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(lean_object* v_mvarId_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_4074_, v___y_4075_, v___y_4081_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___boxed(lean_object* v_mvarId_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(v_mvarId_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v_mvarId_4086_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4098_, lean_object* v_n_4099_, lean_object* v_k_4100_, lean_object* v_v_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_n_4099_, v_k_4100_, v_v_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_4103_, size_t v_depth_4104_, lean_object* v_keys_4105_, lean_object* v_vals_4106_, lean_object* v_heq_4107_, lean_object* v_i_4108_, lean_object* v_entries_4109_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_4104_, v_keys_4105_, v_vals_4106_, v_i_4108_, v_entries_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_4111_, lean_object* v_depth_4112_, lean_object* v_keys_4113_, lean_object* v_vals_4114_, lean_object* v_heq_4115_, lean_object* v_i_4116_, lean_object* v_entries_4117_){
_start:
{
size_t v_depth_boxed_4118_; lean_object* v_res_4119_; 
v_depth_boxed_4118_ = lean_unbox_usize(v_depth_4112_);
lean_dec(v_depth_4112_);
v_res_4119_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(v_00_u03b2_4111_, v_depth_boxed_4118_, v_keys_4113_, v_vals_4114_, v_heq_4115_, v_i_4116_, v_entries_4117_);
lean_dec_ref(v_vals_4114_);
lean_dec_ref(v_keys_4113_);
return v_res_4119_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(lean_object* v_00_u03b2_4120_, lean_object* v_a_4121_, lean_object* v_x_4122_){
_start:
{
uint8_t v___x_4123_; 
v___x_4123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_4121_, v_x_4122_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03b2_4124_, lean_object* v_a_4125_, lean_object* v_x_4126_){
_start:
{
uint8_t v_res_4127_; lean_object* v_r_4128_; 
v_res_4127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(v_00_u03b2_4124_, v_a_4125_, v_x_4126_);
lean_dec(v_x_4126_);
lean_dec_ref(v_a_4125_);
v_r_4128_ = lean_box(v_res_4127_);
return v_r_4128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17(lean_object* v_00_u03b2_4129_, lean_object* v_data_4130_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_data_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_4132_, lean_object* v_x_4133_, lean_object* v_x_4134_, lean_object* v_x_4135_, lean_object* v_x_4136_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_x_4133_, v_x_4134_, v_x_4135_, v_x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19(lean_object* v_00_u03b2_4138_, lean_object* v_i_4139_, lean_object* v_source_4140_, lean_object* v_target_4141_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v_i_4139_, v_source_4140_, v_target_4141_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23(lean_object* v_00_u03b2_4143_, lean_object* v_x_4144_, lean_object* v_x_4145_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_x_4144_, v_x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_){
_start:
{
uint8_t v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = 1;
v___x_4158_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_4157_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4179_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4182_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_4183_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4179_, v___x_4180_, v___x_4181_, v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_4214_ = l_Lean_addBuiltinDeclarationRanges(v___x_4212_, v___x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_4219_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_4221_);
lean_dec(v_x_4221_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; uint8_t v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___x_4275_; uint8_t v___x_4276_; 
v___x_4275_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_4234_);
v___x_4276_ = l_Lean_Syntax_isOfKind(v_stx_4234_, v___x_4275_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; 
lean_dec(v_stx_4234_);
v___x_4277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4277_;
}
else
{
lean_object* v___x_4278_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; uint8_t v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; uint8_t v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; uint8_t v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; uint8_t v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v_tk_4405_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v_args_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___x_4465_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v_only_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v_unfold_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v_squeeze_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4278_ = lean_unsigned_to_nat(0u);
v_tk_4405_ = l_Lean_Syntax_getArg(v_stx_4234_, v___x_4278_);
v___x_4465_ = lean_unsigned_to_nat(1u);
v___x_4541_ = l_Lean_Syntax_getArg(v_stx_4234_, v___x_4465_);
v___x_4542_ = l_Lean_Syntax_isNone(v___x_4541_);
if (v___x_4542_ == 0)
{
uint8_t v___x_4543_; 
lean_inc(v___x_4541_);
v___x_4543_ = l_Lean_Syntax_matchesNull(v___x_4541_, v___x_4465_);
if (v___x_4543_ == 0)
{
lean_object* v___x_4544_; 
lean_dec(v___x_4541_);
lean_dec(v_tk_4405_);
lean_dec(v_stx_4234_);
v___x_4544_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4544_;
}
else
{
lean_object* v_squeeze_4545_; lean_object* v___x_4546_; 
v_squeeze_4545_ = l_Lean_Syntax_getArg(v___x_4541_, v___x_4278_);
lean_dec(v___x_4541_);
v___x_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4546_, 0, v_squeeze_4545_);
v_squeeze_4524_ = v___x_4546_;
v___y_4525_ = v_a_4235_;
v___y_4526_ = v_a_4236_;
v___y_4527_ = v_a_4237_;
v___y_4528_ = v_a_4238_;
v___y_4529_ = v_a_4239_;
v___y_4530_ = v_a_4240_;
v___y_4531_ = v_a_4241_;
v___y_4532_ = v_a_4242_;
goto v___jp_4523_;
}
}
else
{
lean_object* v___x_4547_; 
lean_dec(v___x_4541_);
v___x_4547_ = lean_box(0);
v_squeeze_4524_ = v___x_4547_;
v___y_4525_ = v_a_4235_;
v___y_4526_ = v_a_4236_;
v___y_4527_ = v_a_4237_;
v___y_4528_ = v_a_4238_;
v___y_4529_ = v_a_4239_;
v___y_4530_ = v_a_4240_;
v___y_4531_ = v_a_4241_;
v___y_4532_ = v_a_4242_;
goto v___jp_4523_;
}
v___jp_4279_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
lean_inc_ref(v___y_4292_);
v___x_4302_ = l_Array_append___redArg(v___y_4292_, v___y_4301_);
lean_dec_ref(v___y_4301_);
lean_inc(v___y_4300_);
lean_inc(v___y_4296_);
v___x_4303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4303_, 0, v___y_4296_);
lean_ctor_set(v___x_4303_, 1, v___y_4300_);
lean_ctor_set(v___x_4303_, 2, v___x_4302_);
if (lean_obj_tag(v___y_4280_) == 1)
{
lean_object* v_val_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v_val_4304_ = lean_ctor_get(v___y_4280_, 0);
lean_inc(v_val_4304_);
lean_dec_ref_known(v___y_4280_, 1);
v___x_4305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_4296_, 4);
v___x_4307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___y_4296_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
lean_inc_ref(v___y_4292_);
v___x_4308_ = l_Array_append___redArg(v___y_4292_, v_val_4304_);
lean_dec(v_val_4304_);
lean_inc(v___y_4300_);
v___x_4309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4309_, 0, v___y_4296_);
lean_ctor_set(v___x_4309_, 1, v___y_4300_);
lean_ctor_set(v___x_4309_, 2, v___x_4308_);
v___x_4310_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_4311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___y_4296_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = l_Lean_Syntax_node3(v___y_4296_, v___x_4305_, v___x_4307_, v___x_4309_, v___x_4311_);
v___x_4313_ = l_Array_mkArray1___redArg(v___x_4312_);
v___y_4245_ = v___y_4281_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___y_4284_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4288_;
v___y_4253_ = v___y_4290_;
v___y_4254_ = v___y_4291_;
v___y_4255_ = v___y_4289_;
v___y_4256_ = v___y_4292_;
v___y_4257_ = v___y_4293_;
v___y_4258_ = v___y_4294_;
v___y_4259_ = v___y_4295_;
v___y_4260_ = v___y_4296_;
v___y_4261_ = v___y_4297_;
v___y_4262_ = v___y_4298_;
v___y_4263_ = v___x_4303_;
v___y_4264_ = v___y_4299_;
v___y_4265_ = v___y_4300_;
v___y_4266_ = v___x_4313_;
goto v___jp_4244_;
}
else
{
lean_object* v___x_4314_; 
lean_dec(v___y_4280_);
v___x_4314_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4245_ = v___y_4281_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___y_4284_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4288_;
v___y_4253_ = v___y_4290_;
v___y_4254_ = v___y_4291_;
v___y_4255_ = v___y_4289_;
v___y_4256_ = v___y_4292_;
v___y_4257_ = v___y_4293_;
v___y_4258_ = v___y_4294_;
v___y_4259_ = v___y_4295_;
v___y_4260_ = v___y_4296_;
v___y_4261_ = v___y_4297_;
v___y_4262_ = v___y_4298_;
v___y_4263_ = v___x_4303_;
v___y_4264_ = v___y_4299_;
v___y_4265_ = v___y_4300_;
v___y_4266_ = v___x_4314_;
goto v___jp_4244_;
}
}
v___jp_4315_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
lean_inc_ref(v___y_4328_);
v___x_4338_ = l_Array_append___redArg(v___y_4328_, v___y_4337_);
lean_dec_ref(v___y_4337_);
lean_inc(v___y_4336_);
lean_inc(v___y_4332_);
v___x_4339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4339_, 0, v___y_4332_);
lean_ctor_set(v___x_4339_, 1, v___y_4336_);
lean_ctor_set(v___x_4339_, 2, v___x_4338_);
if (lean_obj_tag(v___y_4334_) == 1)
{
lean_object* v_val_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v_val_4340_ = lean_ctor_get(v___y_4334_, 0);
lean_inc(v_val_4340_);
lean_dec_ref_known(v___y_4334_, 1);
v___x_4341_ = l_Lean_SourceInfo_fromRef(v_val_4340_, v___x_4276_);
lean_dec(v_val_4340_);
v___x_4342_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = l_Array_mkArray1___redArg(v___x_4343_);
v___y_4280_ = v___y_4316_;
v___y_4281_ = v___y_4317_;
v___y_4282_ = v___y_4318_;
v___y_4283_ = v___y_4319_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___y_4324_;
v___y_4289_ = v___y_4327_;
v___y_4290_ = v___y_4326_;
v___y_4291_ = v___y_4325_;
v___y_4292_ = v___y_4328_;
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4331_;
v___y_4296_ = v___y_4332_;
v___y_4297_ = v___y_4333_;
v___y_4298_ = v___x_4339_;
v___y_4299_ = v___y_4335_;
v___y_4300_ = v___y_4336_;
v___y_4301_ = v___x_4344_;
goto v___jp_4279_;
}
else
{
lean_object* v___x_4345_; 
v___x_4345_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4334_);
lean_dec(v___y_4334_);
v___y_4280_ = v___y_4316_;
v___y_4281_ = v___y_4317_;
v___y_4282_ = v___y_4318_;
v___y_4283_ = v___y_4319_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___y_4324_;
v___y_4289_ = v___y_4327_;
v___y_4290_ = v___y_4326_;
v___y_4291_ = v___y_4325_;
v___y_4292_ = v___y_4328_;
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4331_;
v___y_4296_ = v___y_4332_;
v___y_4297_ = v___y_4333_;
v___y_4298_ = v___x_4339_;
v___y_4299_ = v___y_4335_;
v___y_4300_ = v___y_4336_;
v___y_4301_ = v___x_4345_;
goto v___jp_4279_;
}
}
v___jp_4346_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
lean_inc_ref(v___y_4358_);
v___x_4368_ = l_Array_append___redArg(v___y_4358_, v___y_4367_);
lean_dec_ref(v___y_4367_);
lean_inc(v___y_4366_);
lean_inc(v___y_4362_);
v___x_4369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4369_, 0, v___y_4362_);
lean_ctor_set(v___x_4369_, 1, v___y_4366_);
lean_ctor_set(v___x_4369_, 2, v___x_4368_);
v___x_4370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4361_) == 0)
{
lean_object* v___x_4371_; 
v___x_4371_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4348_;
v___y_4318_ = v___x_4369_;
v___y_4319_ = v___y_4349_;
v___y_4320_ = v___y_4350_;
v___y_4321_ = v___y_4351_;
v___y_4322_ = v___y_4352_;
v___y_4323_ = v___y_4353_;
v___y_4324_ = v___y_4354_;
v___y_4325_ = v___y_4356_;
v___y_4326_ = v___y_4357_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4358_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4360_;
v___y_4331_ = v___x_4370_;
v___y_4332_ = v___y_4362_;
v___y_4333_ = v___y_4363_;
v___y_4334_ = v___y_4364_;
v___y_4335_ = v___y_4365_;
v___y_4336_ = v___y_4366_;
v___y_4337_ = v___x_4371_;
goto v___jp_4315_;
}
else
{
lean_object* v_val_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v_val_4372_ = lean_ctor_get(v___y_4361_, 0);
lean_inc(v_val_4372_);
lean_dec_ref_known(v___y_4361_, 1);
v___x_4373_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4374_ = lean_array_push(v___x_4373_, v_val_4372_);
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4348_;
v___y_4318_ = v___x_4369_;
v___y_4319_ = v___y_4349_;
v___y_4320_ = v___y_4350_;
v___y_4321_ = v___y_4351_;
v___y_4322_ = v___y_4352_;
v___y_4323_ = v___y_4353_;
v___y_4324_ = v___y_4354_;
v___y_4325_ = v___y_4356_;
v___y_4326_ = v___y_4357_;
v___y_4327_ = v___y_4355_;
v___y_4328_ = v___y_4358_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4360_;
v___y_4331_ = v___x_4370_;
v___y_4332_ = v___y_4362_;
v___y_4333_ = v___y_4363_;
v___y_4334_ = v___y_4364_;
v___y_4335_ = v___y_4365_;
v___y_4336_ = v___y_4366_;
v___y_4337_ = v___x_4374_;
goto v___jp_4315_;
}
}
v___jp_4375_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
lean_inc_ref(v___y_4387_);
v___x_4397_ = l_Array_append___redArg(v___y_4387_, v___y_4396_);
lean_dec_ref(v___y_4396_);
lean_inc(v___y_4395_);
lean_inc(v___y_4391_);
v___x_4398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4398_, 0, v___y_4391_);
lean_ctor_set(v___x_4398_, 1, v___y_4395_);
lean_ctor_set(v___x_4398_, 2, v___x_4397_);
if (lean_obj_tag(v___y_4382_) == 1)
{
lean_object* v_val_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_val_4399_ = lean_ctor_get(v___y_4382_, 0);
lean_inc(v_val_4399_);
lean_dec_ref_known(v___y_4382_, 1);
v___x_4400_ = l_Lean_SourceInfo_fromRef(v_val_4399_, v___x_4276_);
lean_dec(v_val_4399_);
v___x_4401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_4402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4400_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = l_Array_mkArray1___redArg(v___x_4402_);
v___y_4347_ = v___y_4376_;
v___y_4348_ = v___y_4377_;
v___y_4349_ = v___y_4378_;
v___y_4350_ = v___y_4379_;
v___y_4351_ = v___y_4380_;
v___y_4352_ = v___y_4381_;
v___y_4353_ = v___y_4383_;
v___y_4354_ = v___y_4384_;
v___y_4355_ = v___x_4398_;
v___y_4356_ = v___y_4385_;
v___y_4357_ = v___y_4386_;
v___y_4358_ = v___y_4387_;
v___y_4359_ = v___y_4388_;
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4390_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4392_;
v___y_4364_ = v___y_4393_;
v___y_4365_ = v___y_4394_;
v___y_4366_ = v___y_4395_;
v___y_4367_ = v___x_4403_;
goto v___jp_4346_;
}
else
{
lean_object* v___x_4404_; 
v___x_4404_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4382_);
lean_dec(v___y_4382_);
v___y_4347_ = v___y_4376_;
v___y_4348_ = v___y_4377_;
v___y_4349_ = v___y_4378_;
v___y_4350_ = v___y_4379_;
v___y_4351_ = v___y_4380_;
v___y_4352_ = v___y_4381_;
v___y_4353_ = v___y_4383_;
v___y_4354_ = v___y_4384_;
v___y_4355_ = v___x_4398_;
v___y_4356_ = v___y_4385_;
v___y_4357_ = v___y_4386_;
v___y_4358_ = v___y_4387_;
v___y_4359_ = v___y_4388_;
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4390_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4392_;
v___y_4364_ = v___y_4393_;
v___y_4365_ = v___y_4394_;
v___y_4366_ = v___y_4395_;
v___y_4367_ = v___x_4404_;
goto v___jp_4346_;
}
}
v___jp_4406_:
{
lean_object* v_ref_4422_; uint8_t v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v_ref_4422_ = lean_ctor_get(v___y_4415_, 2);
v___x_4423_ = 0;
v___x_4424_ = l_Lean_SourceInfo_fromRef(v_ref_4422_, v___x_4423_);
v___x_4425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4427_ = l_Lean_SourceInfo_fromRef(v_tk_4405_, v___x_4276_);
lean_dec(v_tk_4405_);
v___x_4428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
lean_ctor_set(v___x_4428_, 1, v___x_4425_);
v___x_4429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_4430_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_4416_) == 1)
{
lean_object* v_val_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_val_4431_ = lean_ctor_get(v___y_4416_, 0);
lean_inc(v_val_4431_);
lean_dec_ref_known(v___y_4416_, 1);
v___x_4432_ = l_Lean_SourceInfo_fromRef(v_val_4431_, v___x_4276_);
lean_dec(v_val_4431_);
v___x_4433_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = l_Array_mkArray1___redArg(v___x_4434_);
v___y_4376_ = v___y_4407_;
v___y_4377_ = v___y_4408_;
v___y_4378_ = v___y_4409_;
v___y_4379_ = v___y_4410_;
v___y_4380_ = v___y_4411_;
v___y_4381_ = v___y_4412_;
v___y_4382_ = v___y_4413_;
v___y_4383_ = v___y_4414_;
v___y_4384_ = v___x_4423_;
v___y_4385_ = v___x_4426_;
v___y_4386_ = v___y_4415_;
v___y_4387_ = v___x_4430_;
v___y_4388_ = v___x_4428_;
v___y_4389_ = v___y_4417_;
v___y_4390_ = v___y_4421_;
v___y_4391_ = v___x_4424_;
v___y_4392_ = v___y_4418_;
v___y_4393_ = v___y_4419_;
v___y_4394_ = v___y_4420_;
v___y_4395_ = v___x_4429_;
v___y_4396_ = v___x_4435_;
goto v___jp_4375_;
}
else
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4416_);
lean_dec(v___y_4416_);
v___y_4376_ = v___y_4407_;
v___y_4377_ = v___y_4408_;
v___y_4378_ = v___y_4409_;
v___y_4379_ = v___y_4410_;
v___y_4380_ = v___y_4411_;
v___y_4381_ = v___y_4412_;
v___y_4382_ = v___y_4413_;
v___y_4383_ = v___y_4414_;
v___y_4384_ = v___x_4423_;
v___y_4385_ = v___x_4426_;
v___y_4386_ = v___y_4415_;
v___y_4387_ = v___x_4430_;
v___y_4388_ = v___x_4428_;
v___y_4389_ = v___y_4417_;
v___y_4390_ = v___y_4421_;
v___y_4391_ = v___x_4424_;
v___y_4392_ = v___y_4418_;
v___y_4393_ = v___y_4419_;
v___y_4394_ = v___y_4420_;
v___y_4395_ = v___x_4429_;
v___y_4396_ = v___x_4436_;
goto v___jp_4375_;
}
}
v___jp_4437_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; 
v___x_4453_ = lean_unsigned_to_nat(5u);
v___x_4454_ = l_Lean_Syntax_getArg(v___y_4440_, v___x_4453_);
lean_dec(v___y_4440_);
v___x_4455_ = l_Lean_Syntax_getOptional_x3f(v___y_4441_);
lean_dec(v___y_4441_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_box(0);
v___y_4407_ = v_args_4444_;
v___y_4408_ = v___y_4445_;
v___y_4409_ = v___y_4449_;
v___y_4410_ = v___y_4439_;
v___y_4411_ = v___y_4448_;
v___y_4412_ = v___x_4454_;
v___y_4413_ = v___y_4443_;
v___y_4414_ = v___y_4446_;
v___y_4415_ = v___y_4451_;
v___y_4416_ = v___y_4438_;
v___y_4417_ = v___y_4447_;
v___y_4418_ = v___y_4452_;
v___y_4419_ = v___y_4442_;
v___y_4420_ = v___y_4450_;
v___y_4421_ = v___x_4456_;
goto v___jp_4406_;
}
else
{
lean_object* v_val_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
v_val_4457_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4455_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_val_4457_);
lean_dec(v___x_4455_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_val_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
v___y_4407_ = v_args_4444_;
v___y_4408_ = v___y_4445_;
v___y_4409_ = v___y_4449_;
v___y_4410_ = v___y_4439_;
v___y_4411_ = v___y_4448_;
v___y_4412_ = v___x_4454_;
v___y_4413_ = v___y_4443_;
v___y_4414_ = v___y_4446_;
v___y_4415_ = v___y_4451_;
v___y_4416_ = v___y_4438_;
v___y_4417_ = v___y_4447_;
v___y_4418_ = v___y_4452_;
v___y_4419_ = v___y_4442_;
v___y_4420_ = v___y_4450_;
v___y_4421_ = v___x_4462_;
goto v___jp_4406_;
}
}
}
}
v___jp_4466_:
{
lean_object* v___x_4482_; uint8_t v___x_4483_; 
v___x_4482_ = l_Lean_Syntax_getArg(v___y_4469_, v___y_4472_);
v___x_4483_ = l_Lean_Syntax_isNone(v___x_4482_);
if (v___x_4483_ == 0)
{
uint8_t v___x_4484_; 
lean_inc(v___x_4482_);
v___x_4484_ = l_Lean_Syntax_matchesNull(v___x_4482_, v___x_4465_);
if (v___x_4484_ == 0)
{
lean_object* v___x_4485_; 
lean_dec(v___x_4482_);
lean_dec(v_only_4473_);
lean_dec(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec(v_tk_4405_);
v___x_4485_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4485_;
}
else
{
lean_object* v___x_4486_; lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4486_ = l_Lean_Syntax_getArg(v___x_4482_, v___x_4278_);
lean_dec(v___x_4482_);
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4486_);
v___x_4488_ = l_Lean_Syntax_isOfKind(v___x_4486_, v___x_4487_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; 
lean_dec(v___x_4486_);
lean_dec(v_only_4473_);
lean_dec(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec(v_tk_4405_);
v___x_4489_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4489_;
}
else
{
lean_object* v___x_4490_; lean_object* v_args_4491_; lean_object* v___x_4492_; 
v___x_4490_ = l_Lean_Syntax_getArg(v___x_4486_, v___x_4465_);
lean_dec(v___x_4486_);
v_args_4491_ = l_Lean_Syntax_getArgs(v___x_4490_);
lean_dec(v___x_4490_);
v___x_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4492_, 0, v_args_4491_);
v___y_4438_ = v___y_4467_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4469_;
v___y_4441_ = v___y_4470_;
v___y_4442_ = v_only_4473_;
v___y_4443_ = v___y_4471_;
v_args_4444_ = v___x_4492_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4475_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4478_;
v___y_4450_ = v___y_4479_;
v___y_4451_ = v___y_4480_;
v___y_4452_ = v___y_4481_;
goto v___jp_4437_;
}
}
}
else
{
lean_object* v___x_4493_; 
lean_dec(v___x_4482_);
v___x_4493_ = lean_box(0);
v___y_4438_ = v___y_4467_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4469_;
v___y_4441_ = v___y_4470_;
v___y_4442_ = v_only_4473_;
v___y_4443_ = v___y_4471_;
v_args_4444_ = v___x_4493_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4475_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4478_;
v___y_4450_ = v___y_4479_;
v___y_4451_ = v___y_4480_;
v___y_4452_ = v___y_4481_;
goto v___jp_4437_;
}
}
v___jp_4494_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; uint8_t v___x_4509_; 
v___x_4506_ = lean_unsigned_to_nat(3u);
v___x_4507_ = l_Lean_Syntax_getArg(v_stx_4234_, v___x_4506_);
lean_dec(v_stx_4234_);
v___x_4508_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4507_);
v___x_4509_ = l_Lean_Syntax_isOfKind(v___x_4507_, v___x_4508_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4510_; 
lean_dec(v___x_4507_);
lean_dec(v_unfold_4497_);
lean_dec(v___y_4495_);
lean_dec(v_tk_4405_);
v___x_4510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4510_;
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4511_ = l_Lean_Syntax_getArg(v___x_4507_, v___x_4278_);
v___x_4512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4511_);
v___x_4513_ = l_Lean_Syntax_isOfKind(v___x_4511_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; 
lean_dec(v___x_4511_);
lean_dec(v___x_4507_);
lean_dec(v_unfold_4497_);
lean_dec(v___y_4495_);
lean_dec(v_tk_4405_);
v___x_4514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4515_ = l_Lean_Syntax_getArg(v___x_4507_, v___x_4465_);
v___x_4516_ = l_Lean_Syntax_getArg(v___x_4507_, v___y_4496_);
v___x_4517_ = l_Lean_Syntax_isNone(v___x_4516_);
if (v___x_4517_ == 0)
{
uint8_t v___x_4518_; 
lean_inc(v___x_4516_);
v___x_4518_ = l_Lean_Syntax_matchesNull(v___x_4516_, v___x_4465_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; 
lean_dec(v___x_4516_);
lean_dec(v___x_4515_);
lean_dec(v___x_4511_);
lean_dec(v___x_4507_);
lean_dec(v_unfold_4497_);
lean_dec(v___y_4495_);
lean_dec(v_tk_4405_);
v___x_4519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4519_;
}
else
{
lean_object* v_only_4520_; lean_object* v___x_4521_; 
v_only_4520_ = l_Lean_Syntax_getArg(v___x_4516_, v___x_4278_);
lean_dec(v___x_4516_);
v___x_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4521_, 0, v_only_4520_);
v___y_4467_ = v___y_4495_;
v___y_4468_ = v___x_4511_;
v___y_4469_ = v___x_4507_;
v___y_4470_ = v___x_4515_;
v___y_4471_ = v_unfold_4497_;
v___y_4472_ = v___x_4506_;
v_only_4473_ = v___x_4521_;
v___y_4474_ = v___y_4498_;
v___y_4475_ = v___y_4499_;
v___y_4476_ = v___y_4500_;
v___y_4477_ = v___y_4501_;
v___y_4478_ = v___y_4502_;
v___y_4479_ = v___y_4503_;
v___y_4480_ = v___y_4504_;
v___y_4481_ = v___y_4505_;
goto v___jp_4466_;
}
}
else
{
lean_object* v___x_4522_; 
lean_dec(v___x_4516_);
v___x_4522_ = lean_box(0);
v___y_4467_ = v___y_4495_;
v___y_4468_ = v___x_4511_;
v___y_4469_ = v___x_4507_;
v___y_4470_ = v___x_4515_;
v___y_4471_ = v_unfold_4497_;
v___y_4472_ = v___x_4506_;
v_only_4473_ = v___x_4522_;
v___y_4474_ = v___y_4498_;
v___y_4475_ = v___y_4499_;
v___y_4476_ = v___y_4500_;
v___y_4477_ = v___y_4501_;
v___y_4478_ = v___y_4502_;
v___y_4479_ = v___y_4503_;
v___y_4480_ = v___y_4504_;
v___y_4481_ = v___y_4505_;
goto v___jp_4466_;
}
}
}
}
v___jp_4523_:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v___x_4533_ = lean_unsigned_to_nat(2u);
v___x_4534_ = l_Lean_Syntax_getArg(v_stx_4234_, v___x_4533_);
v___x_4535_ = l_Lean_Syntax_isNone(v___x_4534_);
if (v___x_4535_ == 0)
{
uint8_t v___x_4536_; 
lean_inc(v___x_4534_);
v___x_4536_ = l_Lean_Syntax_matchesNull(v___x_4534_, v___x_4465_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; 
lean_dec(v___x_4534_);
lean_dec(v_squeeze_4524_);
lean_dec(v_tk_4405_);
lean_dec(v_stx_4234_);
v___x_4537_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4537_;
}
else
{
lean_object* v_unfold_4538_; lean_object* v___x_4539_; 
v_unfold_4538_ = l_Lean_Syntax_getArg(v___x_4534_, v___x_4278_);
lean_dec(v___x_4534_);
v___x_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4539_, 0, v_unfold_4538_);
v___y_4495_ = v_squeeze_4524_;
v___y_4496_ = v___x_4533_;
v_unfold_4497_ = v___x_4539_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
v___y_4500_ = v___y_4527_;
v___y_4501_ = v___y_4528_;
v___y_4502_ = v___y_4529_;
v___y_4503_ = v___y_4530_;
v___y_4504_ = v___y_4531_;
v___y_4505_ = v___y_4532_;
goto v___jp_4494_;
}
}
else
{
lean_object* v___x_4540_; 
lean_dec(v___x_4534_);
v___x_4540_ = lean_box(0);
v___y_4495_ = v_squeeze_4524_;
v___y_4496_ = v___x_4533_;
v_unfold_4497_ = v___x_4540_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
v___y_4500_ = v___y_4527_;
v___y_4501_ = v___y_4528_;
v___y_4502_ = v___y_4529_;
v___y_4503_ = v___y_4530_;
v___y_4504_ = v___y_4531_;
v___y_4505_ = v___y_4532_;
goto v___jp_4494_;
}
}
}
v___jp_4244_:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_inc_ref(v___y_4256_);
v___x_4267_ = l_Array_append___redArg(v___y_4256_, v___y_4266_);
lean_dec_ref(v___y_4266_);
lean_inc_n(v___y_4265_, 2);
lean_inc_n(v___y_4260_, 4);
v___x_4268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4268_, 0, v___y_4260_);
lean_ctor_set(v___x_4268_, 1, v___y_4265_);
lean_ctor_set(v___x_4268_, 2, v___x_4267_);
v___x_4269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___y_4260_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l_Lean_Syntax_node2(v___y_4260_, v___y_4265_, v___x_4270_, v___y_4250_);
lean_inc(v___y_4259_);
v___x_4272_ = l_Lean_Syntax_node5(v___y_4260_, v___y_4259_, v___y_4248_, v___y_4262_, v___y_4263_, v___x_4268_, v___x_4271_);
lean_inc(v___y_4254_);
v___x_4273_ = l_Lean_Syntax_node4(v___y_4260_, v___y_4254_, v___y_4257_, v___y_4255_, v___y_4246_, v___x_4272_);
v___x_4274_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4252_, v___x_4273_, v___y_4245_, v___y_4251_, v___y_4258_, v___y_4249_, v___y_4247_, v___y_4264_, v___y_4253_, v___y_4261_);
return v___x_4274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4567_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4568_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4570_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4571_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4567_, v___x_4568_, v___x_4569_, v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4573_;
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
