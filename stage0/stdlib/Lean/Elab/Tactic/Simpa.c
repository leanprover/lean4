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
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__6_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_55_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__spec__0(v___x_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_();
return v_res_58_;
}
}
uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object* v_o_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = l_Lean_linter_unnecessarySimpa;
v___x_61_ = l_Lean_Linter_getLinterValue(v___x_60_, v_o_59_);
return v___x_61_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_59_ = stack[0].m_obj;
uint8_t v_res_62_;
v_res_62_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_o_59_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object* v_o_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_o_63_);
lean_dec_ref(v_o_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_66_, lean_object* v_opt_67_){
_start:
{
lean_object* v_name_68_; lean_object* v_defValue_69_; lean_object* v_map_70_; lean_object* v___x_71_; 
v_name_68_ = lean_ctor_get(v_opt_67_, 0);
v_defValue_69_ = lean_ctor_get(v_opt_67_, 1);
v_map_70_ = lean_ctor_get(v_opts_66_, 0);
v___x_71_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_70_, v_name_68_);
if (lean_obj_tag(v___x_71_) == 0)
{
uint8_t v___x_72_; 
v___x_72_ = lean_unbox(v_defValue_69_);
return v___x_72_;
}
else
{
lean_object* v_val_73_; 
v_val_73_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v___x_71_, 1);
if (lean_obj_tag(v_val_73_) == 1)
{
uint8_t v_v_74_; 
v_v_74_ = lean_ctor_get_uint8(v_val_73_, 0);
lean_dec_ref_known(v_val_73_, 0);
return v_v_74_;
}
else
{
uint8_t v___x_75_; 
lean_dec(v_val_73_);
v___x_75_ = lean_unbox(v_defValue_69_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_66_ = stack[0].m_obj;
lean_object* v_opt_67_ = stack[1].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_opts_66_, v_opt_67_);
stack->m_num = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_77_, lean_object* v_opt_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_opts_77_, v_opt_78_);
lean_dec_ref(v_opt_78_);
lean_dec_ref(v_opts_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_89_, uint8_t v___y_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 1)
{
lean_object* v_pre_92_; 
v_pre_92_ = lean_ctor_get(v_x_91_, 0);
switch(lean_obj_tag(v_pre_92_))
{
case 1:
{
lean_object* v_pre_93_; 
v_pre_93_ = lean_ctor_get(v_pre_92_, 0);
switch(lean_obj_tag(v_pre_93_))
{
case 0:
{
lean_object* v_str_94_; lean_object* v_str_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_str_94_ = lean_ctor_get(v_x_91_, 1);
v_str_95_ = lean_ctor_get(v_pre_92_, 1);
v___x_96_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__0));
v___x_97_ = lean_string_dec_eq(v_str_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_99_ = lean_string_dec_eq(v_str_95_, v___x_98_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__2));
v___x_101_ = lean_string_dec_eq(v_str_94_, v___x_100_);
if (v___x_101_ == 0)
{
return v___x_101_;
}
else
{
return v_suppressElabErrors_89_;
}
}
}
else
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__3));
v___x_103_ = lean_string_dec_eq(v_str_94_, v___x_102_);
if (v___x_103_ == 0)
{
return v___x_103_;
}
else
{
return v_suppressElabErrors_89_;
}
}
}
case 1:
{
lean_object* v_pre_104_; 
v_pre_104_ = lean_ctor_get(v_pre_93_, 0);
if (lean_obj_tag(v_pre_104_) == 0)
{
lean_object* v_str_105_; lean_object* v_str_106_; lean_object* v_str_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_str_105_ = lean_ctor_get(v_x_91_, 1);
v_str_106_ = lean_ctor_get(v_pre_92_, 1);
v_str_107_ = lean_ctor_get(v_pre_93_, 1);
v___x_108_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__4));
v___x_109_ = lean_string_dec_eq(v_str_107_, v___x_108_);
if (v___x_109_ == 0)
{
return v___x_109_;
}
else
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__5));
v___x_111_ = lean_string_dec_eq(v_str_106_, v___x_110_);
if (v___x_111_ == 0)
{
return v___x_111_;
}
else
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__6));
v___x_113_ = lean_string_dec_eq(v_str_105_, v___x_112_);
if (v___x_113_ == 0)
{
return v___x_113_;
}
else
{
return v_suppressElabErrors_89_;
}
}
}
}
else
{
return v___y_90_;
}
}
default: 
{
return v___y_90_;
}
}
}
case 0:
{
lean_object* v_str_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_str_114_ = lean_ctor_get(v_x_91_, 1);
v___x_115_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__7));
v___x_116_ = lean_string_dec_eq(v_str_114_, v___x_115_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
return v_suppressElabErrors_89_;
}
}
default: 
{
return v___y_90_;
}
}
}
else
{
return v___y_90_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_89_ = stack[0].m_num;
uint8_t v___y_90_ = stack[1].m_num;
lean_object* v_x_91_ = stack[2].m_obj;
uint8_t v_res_117_;
v_res_117_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_89_, v___y_90_, v_x_91_);
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_118_, lean_object* v___y_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_suppressElabErrors_boxed_121_; uint8_t v___y_4873__boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_suppressElabErrors_boxed_121_ = lean_unbox(v_suppressElabErrors_118_);
v___y_4873__boxed_122_ = lean_unbox(v___y_119_);
v_res_123_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_121_, v___y_4873__boxed_122_, v_x_120_);
lean_dec(v_x_120_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; lean_object* v_env_132_; uint8_t v___x_133_; lean_object* v_env_134_; lean_object* v___x_135_; lean_object* v_toCold_136_; lean_object* v_mctx_137_; lean_object* v_lctx_138_; lean_object* v_options_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_131_ = lean_st_ref_get(v___y_129_);
v_env_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_env_132_);
lean_dec(v___x_131_);
v___x_133_ = 0;
v_env_134_ = l_Lean_Environment_setRecordingDeps(v_env_132_, v___x_133_);
v___x_135_ = lean_st_ref_get(v___y_127_);
v_toCold_136_ = lean_ctor_get(v___y_128_, 0);
v_mctx_137_ = lean_ctor_get(v___x_135_, 0);
lean_inc_ref(v_mctx_137_);
lean_dec(v___x_135_);
v_lctx_138_ = lean_ctor_get(v___y_126_, 2);
v_options_139_ = lean_ctor_get(v_toCold_136_, 2);
lean_inc_ref(v_options_139_);
lean_inc_ref(v_lctx_138_);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_env_134_);
lean_ctor_set(v___x_140_, 1, v_mctx_137_);
lean_ctor_set(v___x_140_, 2, v_lctx_138_);
lean_ctor_set(v___x_140_, 3, v_options_139_);
v___x_141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_msgData_125_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_125_ = stack[0].m_obj;
lean_object* v___y_126_ = stack[1].m_obj;
lean_object* v___y_127_ = stack[2].m_obj;
lean_object* v___y_128_ = stack[3].m_obj;
lean_object* v___y_129_ = stack[4].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msgData_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msgData_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
return v_res_150_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_152_, lean_object* v_msgData_153_, uint8_t v_severity_154_, uint8_t v_isSilent_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___y_162_; uint8_t v___y_163_; uint8_t v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v_toCold_169_; lean_object* v___y_170_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; uint8_t v___y_202_; uint8_t v___y_203_; uint8_t v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; uint8_t v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; uint8_t v___y_229_; uint8_t v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; uint8_t v___y_236_; uint8_t v___y_237_; uint8_t v___y_238_; uint8_t v___x_249_; uint8_t v___y_251_; uint8_t v___y_252_; uint8_t v___y_253_; uint8_t v___y_255_; uint8_t v___x_263_; 
v___x_249_ = 2;
v___x_263_ = l_Lean_instBEqMessageSeverity_beq(v_severity_154_, v___x_249_);
if (v___x_263_ == 0)
{
v___y_255_ = v___x_263_;
goto v___jp_254_;
}
else
{
uint8_t v___x_264_; 
lean_inc_ref(v_msgData_153_);
v___x_264_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_153_);
v___y_255_ = v___x_264_;
goto v___jp_254_;
}
v___jp_161_:
{
lean_object* v_currNamespace_171_; lean_object* v_openDecls_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_env_177_; lean_object* v_nextMacroScope_178_; lean_object* v_ngen_179_; lean_object* v_auxDeclNGen_180_; lean_object* v_traceState_181_; lean_object* v_cache_182_; lean_object* v_recordedDeps_183_; lean_object* v_messages_184_; lean_object* v_infoState_185_; lean_object* v_snapshotTasks_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_197_; 
v_currNamespace_171_ = lean_ctor_get(v_toCold_169_, 4);
v_openDecls_172_ = lean_ctor_get(v_toCold_169_, 5);
lean_inc(v_openDecls_172_);
lean_inc(v_currNamespace_171_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_currNamespace_171_);
lean_ctor_set(v___x_173_, 1, v_openDecls_172_);
v___x_174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___y_162_);
lean_inc_ref(v___y_167_);
lean_inc_ref(v___y_166_);
v___x_175_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_175_, 0, v___y_166_);
lean_ctor_set(v___x_175_, 1, v___y_168_);
lean_ctor_set(v___x_175_, 2, v___y_165_);
lean_ctor_set(v___x_175_, 3, v___y_167_);
lean_ctor_set(v___x_175_, 4, v___x_174_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*5, v___y_163_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*5 + 1, v___y_164_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*5 + 2, v_isSilent_155_);
v___x_176_ = lean_st_ref_take(v___y_170_);
v_env_177_ = lean_ctor_get(v___x_176_, 0);
v_nextMacroScope_178_ = lean_ctor_get(v___x_176_, 1);
v_ngen_179_ = lean_ctor_get(v___x_176_, 2);
v_auxDeclNGen_180_ = lean_ctor_get(v___x_176_, 3);
v_traceState_181_ = lean_ctor_get(v___x_176_, 4);
v_cache_182_ = lean_ctor_get(v___x_176_, 5);
v_recordedDeps_183_ = lean_ctor_get(v___x_176_, 6);
v_messages_184_ = lean_ctor_get(v___x_176_, 7);
v_infoState_185_ = lean_ctor_get(v___x_176_, 8);
v_snapshotTasks_186_ = lean_ctor_get(v___x_176_, 9);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_197_ == 0)
{
v___x_188_ = v___x_176_;
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_snapshotTasks_186_);
lean_inc(v_infoState_185_);
lean_inc(v_messages_184_);
lean_inc(v_recordedDeps_183_);
lean_inc(v_cache_182_);
lean_inc(v_traceState_181_);
lean_inc(v_auxDeclNGen_180_);
lean_inc(v_ngen_179_);
lean_inc(v_nextMacroScope_178_);
lean_inc(v_env_177_);
lean_dec(v___x_176_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_box(0);
v___x_191_ = l_Lean_MessageLog_add(v___x_175_, v_messages_184_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 7, v___x_191_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_env_177_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_nextMacroScope_178_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_ngen_179_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_auxDeclNGen_180_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_traceState_181_);
lean_ctor_set(v_reuseFailAlloc_196_, 5, v_cache_182_);
lean_ctor_set(v_reuseFailAlloc_196_, 6, v_recordedDeps_183_);
lean_ctor_set(v_reuseFailAlloc_196_, 7, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_196_, 8, v_infoState_185_);
lean_ctor_set(v_reuseFailAlloc_196_, 9, v_snapshotTasks_186_);
v___x_193_ = v_reuseFailAlloc_196_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_st_ref_put(v___y_170_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_190_);
return v___x_195_;
}
}
}
v___jp_198_:
{
lean_object* v_fileName_207_; lean_object* v_fileMap_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_224_; 
v_fileName_207_ = lean_ctor_get(v___y_205_, 0);
v_fileMap_208_ = lean_ctor_get(v___y_205_, 1);
v___x_209_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_153_);
v___x_210_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v___x_209_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_224_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_224_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_224_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_inc_ref_n(v_fileMap_208_, 2);
v___x_215_ = l_Lean_FileMap_toPosition(v_fileMap_208_, v___y_201_);
lean_dec(v___y_201_);
v___x_216_ = l_Lean_FileMap_toPosition(v_fileMap_208_, v___y_206_);
lean_dec(v___y_206_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___x_218_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0));
if (v___y_203_ == 0)
{
lean_del_object(v___x_213_);
lean_dec_ref(v___y_199_);
v___y_162_ = v_a_211_;
v___y_163_ = v___y_202_;
v___y_164_ = v___y_204_;
v___y_165_ = v___x_217_;
v___y_166_ = v_fileName_207_;
v___y_167_ = v___x_218_;
v___y_168_ = v___x_215_;
v_toCold_169_ = v___y_200_;
v___y_170_ = v___y_159_;
goto v___jp_161_;
}
else
{
uint8_t v___x_219_; 
lean_inc(v_a_211_);
v___x_219_ = l_Lean_MessageData_hasTag(v___y_199_, v_a_211_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec_ref_known(v___x_217_, 1);
lean_dec_ref(v___x_215_);
lean_dec(v_a_211_);
v___x_220_ = lean_box(0);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_220_);
v___x_222_ = v___x_213_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
else
{
lean_del_object(v___x_213_);
v___y_162_ = v_a_211_;
v___y_163_ = v___y_202_;
v___y_164_ = v___y_204_;
v___y_165_ = v___x_217_;
v___y_166_ = v_fileName_207_;
v___y_167_ = v___x_218_;
v___y_168_ = v___x_215_;
v_toCold_169_ = v___y_200_;
v___y_170_ = v___y_159_;
goto v___jp_161_;
}
}
}
}
v___jp_225_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Syntax_getTailPos_x3f(v___y_231_, v___y_229_);
lean_dec(v___y_231_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_inc(v___y_232_);
v___y_199_ = v___y_227_;
v___y_200_ = v___y_228_;
v___y_201_ = v___y_232_;
v___y_202_ = v___y_229_;
v___y_203_ = v___y_226_;
v___y_204_ = v___y_230_;
v___y_205_ = v___y_228_;
v___y_206_ = v___y_232_;
goto v___jp_198_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_233_, 1);
v___y_199_ = v___y_227_;
v___y_200_ = v___y_228_;
v___y_201_ = v___y_232_;
v___y_202_ = v___y_229_;
v___y_203_ = v___y_226_;
v___y_204_ = v___y_230_;
v___y_205_ = v___y_228_;
v___y_206_ = v_val_234_;
goto v___jp_198_;
}
}
v___jp_235_:
{
lean_object* v_toCold_239_; lean_object* v_ref_240_; uint8_t v_suppressElabErrors_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___f_244_; lean_object* v_ref_245_; lean_object* v___x_246_; 
v_toCold_239_ = lean_ctor_get(v___y_158_, 0);
v_ref_240_ = lean_ctor_get(v___y_158_, 2);
v_suppressElabErrors_241_ = lean_ctor_get_uint8(v___y_158_, sizeof(void*)*3 + 2);
v___x_242_ = lean_box(v_suppressElabErrors_241_);
v___x_243_ = lean_box(v___y_236_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_244_, 0, v___x_242_);
lean_closure_set(v___f_244_, 1, v___x_243_);
v_ref_245_ = l_Lean_replaceRef(v_ref_152_, v_ref_240_);
v___x_246_ = l_Lean_Syntax_getPos_x3f(v_ref_245_, v___y_237_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_unsigned_to_nat(0u);
v___y_226_ = v_suppressElabErrors_241_;
v___y_227_ = v___f_244_;
v___y_228_ = v_toCold_239_;
v___y_229_ = v___y_237_;
v___y_230_ = v___y_238_;
v___y_231_ = v_ref_245_;
v___y_232_ = v___x_247_;
goto v___jp_225_;
}
else
{
lean_object* v_val_248_; 
v_val_248_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v___x_246_, 1);
v___y_226_ = v_suppressElabErrors_241_;
v___y_227_ = v___f_244_;
v___y_228_ = v_toCold_239_;
v___y_229_ = v___y_237_;
v___y_230_ = v___y_238_;
v___y_231_ = v_ref_245_;
v___y_232_ = v_val_248_;
goto v___jp_225_;
}
}
v___jp_250_:
{
if (v___y_253_ == 0)
{
v___y_236_ = v___y_251_;
v___y_237_ = v___y_252_;
v___y_238_ = v_severity_154_;
goto v___jp_235_;
}
else
{
v___y_236_ = v___y_251_;
v___y_237_ = v___y_252_;
v___y_238_ = v___x_249_;
goto v___jp_235_;
}
}
v___jp_254_:
{
if (v___y_255_ == 0)
{
uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 1;
v___x_257_ = l_Lean_instBEqMessageSeverity_beq(v_severity_154_, v___x_256_);
if (v___x_257_ == 0)
{
v___y_251_ = v___y_255_;
v___y_252_ = v___y_255_;
v___y_253_ = v___x_257_;
goto v___jp_250_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_158_);
v___x_259_ = l_Lean_warningAsError;
v___x_260_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_258_, v___x_259_);
lean_dec_ref(v___x_258_);
v___y_251_ = v___y_255_;
v___y_252_ = v___y_255_;
v___y_253_ = v___x_260_;
goto v___jp_250_;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref(v_msgData_153_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_152_ = stack[0].m_obj;
lean_object* v_msgData_153_ = stack[1].m_obj;
uint8_t v_severity_154_ = stack[2].m_num;
uint8_t v_isSilent_155_ = stack[3].m_num;
lean_object* v___y_156_ = stack[4].m_obj;
lean_object* v___y_157_ = stack[5].m_obj;
lean_object* v___y_158_ = stack[6].m_obj;
lean_object* v___y_159_ = stack[7].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_152_, v_msgData_153_, v_severity_154_, v_isSilent_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_266_, lean_object* v_msgData_267_, lean_object* v_severity_268_, lean_object* v_isSilent_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v_severity_boxed_275_; uint8_t v_isSilent_boxed_276_; lean_object* v_res_277_; 
v_severity_boxed_275_ = lean_unbox(v_severity_268_);
v_isSilent_boxed_276_ = lean_unbox(v_isSilent_269_);
v_res_277_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_266_, v_msgData_267_, v_severity_boxed_275_, v_isSilent_boxed_276_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_ref_266_);
return v_res_277_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_278_, lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
uint8_t v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = 1;
v___x_290_ = 0;
v___x_291_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_278_, v_msgData_279_, v___x_289_, v___x_290_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_291_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_278_ = stack[0].m_obj;
lean_object* v_msgData_279_ = stack[1].m_obj;
lean_object* v___y_280_ = stack[2].m_obj;
lean_object* v___y_281_ = stack[3].m_obj;
lean_object* v___y_282_ = stack[4].m_obj;
lean_object* v___y_283_ = stack[5].m_obj;
lean_object* v___y_284_ = stack[6].m_obj;
lean_object* v___y_285_ = stack[7].m_obj;
lean_object* v___y_286_ = stack[8].m_obj;
lean_object* v___y_287_ = stack[9].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_278_, v_msgData_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_293_, lean_object* v_msgData_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_293_, v_msgData_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v_ref_293_);
return v_res_304_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_311_, lean_object* v_stx_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_name_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_341_; 
v_name_323_ = lean_ctor_get(v_linterOption_311_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_linterOption_311_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; 
v_unused_342_ = lean_ctor_get(v_linterOption_311_, 1);
lean_dec(v_unused_342_);
v___x_325_ = v_linterOption_311_;
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_name_323_);
lean_dec(v_linterOption_311_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_323_);
v___x_328_ = l_Lean_MessageData_ofName(v_name_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 7);
lean_ctor_set(v___x_325_, 1, v___x_328_);
lean_ctor_set(v___x_325_, 0, v___x_327_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_340_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_disable_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_331_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v_disable_333_ = l_Lean_MessageData_note(v___x_332_);
v___x_334_ = l_Lean_Linter_linterMessageTag;
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v_msg_313_);
lean_ctor_set(v___x_335_, 1, v_disable_333_);
v___x_336_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_337_, 0, v_name_323_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_inc(v_stx_312_);
v___x_338_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_338_, 0, v_stx_312_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_312_, v___x_338_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v_stx_312_);
return v___x_339_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_311_ = stack[0].m_obj;
lean_object* v_stx_312_ = stack[1].m_obj;
lean_object* v_msg_313_ = stack[2].m_obj;
lean_object* v___y_314_ = stack[3].m_obj;
lean_object* v___y_315_ = stack[4].m_obj;
lean_object* v___y_316_ = stack[5].m_obj;
lean_object* v___y_317_ = stack[6].m_obj;
lean_object* v___y_318_ = stack[7].m_obj;
lean_object* v___y_319_ = stack[8].m_obj;
lean_object* v___y_320_ = stack[9].m_obj;
lean_object* v___y_321_ = stack[10].m_obj;
lean_object* v_res_343_;
v_res_343_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_311_, v_stx_312_, v_msg_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_344_, lean_object* v_stx_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_344_, v_stx_345_, v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_356_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v_msg_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_359_ = l_Lean_stringToMessageData(v___x_358_);
return v_msg_359_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_367_ = l_Lean_MessageData_ofFormat(v___x_366_);
return v___x_367_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_368_, lean_object* v_ref_369_, lean_object* v_replacement_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_msg_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v_msg_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_msg_392_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_393_ = lean_box(0);
lean_inc(v_replacement_370_);
v___x_394_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_368_, v_replacement_370_, v___x_393_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; uint8_t v___x_396_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = lean_unbox(v_a_395_);
lean_dec(v_a_395_);
if (v___x_396_ == 0)
{
lean_dec(v_replacement_370_);
v_msg_381_ = v_msg_392_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
v___y_385_ = v_a_374_;
v___y_386_ = v_a_375_;
v___y_387_ = v_a_376_;
v___y_388_ = v_a_377_;
v___y_389_ = v_a_378_;
goto v___jp_380_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; 
v___x_397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_replacement_370_);
v___x_399_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_393_);
lean_ctor_set(v___x_399_, 2, v___x_393_);
lean_ctor_set(v___x_399_, 3, v___x_393_);
lean_ctor_set(v___x_399_, 4, v___x_393_);
lean_ctor_set(v___x_399_, 5, v___x_393_);
lean_inc(v_ref_369_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_ref_369_);
v___x_401_ = 4;
lean_inc_ref(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_402_, 0, v___x_399_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_393_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*3, v___x_401_);
v___x_403_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
v___x_406_ = lean_array_push(v___x_405_, v___x_402_);
v___x_407_ = 0;
v___x_408_ = l_Lean_MessageData_hint(v___x_403_, v___x_406_, v___x_400_, v___x_393_, v___x_407_, v_a_377_, v_a_378_);
lean_dec_ref(v___x_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_410_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v_msg_392_);
lean_ctor_set(v___x_410_, 1, v_a_409_);
v_msg_381_ = v___x_410_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
v___y_385_ = v_a_374_;
v___y_386_ = v_a_375_;
v___y_387_ = v_a_376_;
v___y_388_ = v_a_377_;
v___y_389_ = v_a_378_;
goto v___jp_380_;
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_ref_369_);
v_a_411_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_408_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_408_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_replacement_370_);
lean_dec(v_ref_369_);
v_a_419_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_394_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_394_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
v___jp_380_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = l_Lean_linter_unnecessarySimpa;
v___x_391_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_390_, v_ref_369_, v_msg_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_0interp(lean_interpreter_value* stack)
{
lean_object* v_initialState_368_ = stack[0].m_obj;
lean_object* v_ref_369_ = stack[1].m_obj;
lean_object* v_replacement_370_ = stack[2].m_obj;
lean_object* v_a_371_ = stack[3].m_obj;
lean_object* v_a_372_ = stack[4].m_obj;
lean_object* v_a_373_ = stack[5].m_obj;
lean_object* v_a_374_ = stack[6].m_obj;
lean_object* v_a_375_ = stack[7].m_obj;
lean_object* v_a_376_ = stack[8].m_obj;
lean_object* v_a_377_ = stack[9].m_obj;
lean_object* v_a_378_ = stack[10].m_obj;
lean_object* v_res_427_;
v_res_427_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_368_, v_ref_369_, v_replacement_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_428_, lean_object* v_ref_429_, lean_object* v_replacement_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_428_, v_ref_429_, v_replacement_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_440_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_441_, lean_object* v_msgData_442_, uint8_t v_severity_443_, uint8_t v_isSilent_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_441_, v_msgData_442_, v_severity_443_, v_isSilent_444_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_441_ = stack[0].m_obj;
lean_object* v_msgData_442_ = stack[1].m_obj;
uint8_t v_severity_443_ = stack[2].m_num;
uint8_t v_isSilent_444_ = stack[3].m_num;
lean_object* v___y_445_ = stack[4].m_obj;
lean_object* v___y_446_ = stack[5].m_obj;
lean_object* v___y_447_ = stack[6].m_obj;
lean_object* v___y_448_ = stack[7].m_obj;
lean_object* v___y_449_ = stack[8].m_obj;
lean_object* v___y_450_ = stack[9].m_obj;
lean_object* v___y_451_ = stack[10].m_obj;
lean_object* v___y_452_ = stack[11].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_441_, v_msgData_442_, v_severity_443_, v_isSilent_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_456_, lean_object* v_msgData_457_, lean_object* v_severity_458_, lean_object* v_isSilent_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v_severity_boxed_469_; uint8_t v_isSilent_boxed_470_; lean_object* v_res_471_; 
v_severity_boxed_469_ = lean_unbox(v_severity_458_);
v_isSilent_boxed_470_ = lean_unbox(v_isSilent_459_);
v_res_471_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_456_, v_msgData_457_, v_severity_boxed_469_, v_isSilent_boxed_470_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v_ref_456_);
return v_res_471_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_box(0);
v___x_473_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
return v___x_474_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_478_;
v_res_478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_480_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_491_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_482_ = stack[1].m_obj;
lean_object* v___y_483_ = stack[2].m_obj;
lean_object* v___y_484_ = stack[3].m_obj;
lean_object* v___y_485_ = stack[4].m_obj;
lean_object* v___y_486_ = stack[5].m_obj;
lean_object* v___y_487_ = stack[6].m_obj;
lean_object* v___y_488_ = stack[7].m_obj;
lean_object* v___y_489_ = stack[8].m_obj;
lean_object* v_res_492_;
v_res_492_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_box(0), v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_503_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(lean_object* v_x_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; 
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
v___x_514_ = lean_apply_9(v_x_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, lean_box(0));
return v___x_514_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_504_ = stack[0].m_obj;
lean_object* v___y_505_ = stack[1].m_obj;
lean_object* v___y_506_ = stack[2].m_obj;
lean_object* v___y_507_ = stack[3].m_obj;
lean_object* v___y_508_ = stack[4].m_obj;
lean_object* v___y_509_ = stack[5].m_obj;
lean_object* v___y_510_ = stack[6].m_obj;
lean_object* v___y_511_ = stack[7].m_obj;
lean_object* v___y_512_ = stack[8].m_obj;
lean_object* v_res_515_;
v_res_515_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(v_x_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed(lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(v_x_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_526_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(lean_object* v_mvarId_527_, lean_object* v_x_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___f_538_; lean_object* v___x_539_; 
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_538_, 0, v_x_528_);
lean_closure_set(v___f_538_, 1, v___y_529_);
lean_closure_set(v___f_538_, 2, v___y_530_);
lean_closure_set(v___f_538_, 3, v___y_531_);
lean_closure_set(v___f_538_, 4, v___y_532_);
v___x_539_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_527_, v___f_538_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_539_) == 0)
{
return v___x_539_;
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_527_ = stack[0].m_obj;
lean_object* v_x_528_ = stack[1].m_obj;
lean_object* v___y_529_ = stack[2].m_obj;
lean_object* v___y_530_ = stack[3].m_obj;
lean_object* v___y_531_ = stack[4].m_obj;
lean_object* v___y_532_ = stack[5].m_obj;
lean_object* v___y_533_ = stack[6].m_obj;
lean_object* v___y_534_ = stack[7].m_obj;
lean_object* v___y_535_ = stack[8].m_obj;
lean_object* v___y_536_ = stack[9].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_527_, v_x_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___boxed(lean_object* v_mvarId_549_, lean_object* v_x_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_549_, v_x_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_560_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v_00_u03b1_561_, lean_object* v_mvarId_562_, lean_object* v_x_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_562_, v_x_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
return v___x_573_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_562_ = stack[1].m_obj;
lean_object* v_x_563_ = stack[2].m_obj;
lean_object* v___y_564_ = stack[3].m_obj;
lean_object* v___y_565_ = stack[4].m_obj;
lean_object* v___y_566_ = stack[5].m_obj;
lean_object* v___y_567_ = stack[6].m_obj;
lean_object* v___y_568_ = stack[7].m_obj;
lean_object* v___y_569_ = stack[8].m_obj;
lean_object* v___y_570_ = stack[9].m_obj;
lean_object* v___y_571_ = stack[10].m_obj;
lean_object* v_res_574_;
v_res_574_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_box(0), v_mvarId_562_, v_x_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v_00_u03b1_575_, lean_object* v_mvarId_576_, lean_object* v_x_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v_00_u03b1_575_, v_mvarId_576_, v_x_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(32u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_591_ = ((size_t)5ULL);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_unsigned_to_nat(32u);
v___x_594_ = lean_mk_empty_array_with_capacity(v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_596_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
lean_ctor_set(v___x_596_, 2, v___x_592_);
lean_ctor_set(v___x_596_, 3, v___x_592_);
lean_ctor_set_usize(v___x_596_, 4, v___x_591_);
return v___x_596_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v_infoState_600_; lean_object* v_trees_601_; lean_object* v___x_602_; lean_object* v_infoState_603_; lean_object* v_env_604_; lean_object* v_nextMacroScope_605_; lean_object* v_ngen_606_; lean_object* v_auxDeclNGen_607_; lean_object* v_traceState_608_; lean_object* v_cache_609_; lean_object* v_recordedDeps_610_; lean_object* v_messages_611_; lean_object* v_snapshotTasks_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_633_; 
v___x_599_ = lean_st_ref_get(v___y_597_);
v_infoState_600_ = lean_ctor_get(v___x_599_, 8);
lean_inc_ref(v_infoState_600_);
lean_dec(v___x_599_);
v_trees_601_ = lean_ctor_get(v_infoState_600_, 2);
lean_inc_ref(v_trees_601_);
lean_dec_ref(v_infoState_600_);
v___x_602_ = lean_st_ref_take(v___y_597_);
v_infoState_603_ = lean_ctor_get(v___x_602_, 8);
v_env_604_ = lean_ctor_get(v___x_602_, 0);
v_nextMacroScope_605_ = lean_ctor_get(v___x_602_, 1);
v_ngen_606_ = lean_ctor_get(v___x_602_, 2);
v_auxDeclNGen_607_ = lean_ctor_get(v___x_602_, 3);
v_traceState_608_ = lean_ctor_get(v___x_602_, 4);
v_cache_609_ = lean_ctor_get(v___x_602_, 5);
v_recordedDeps_610_ = lean_ctor_get(v___x_602_, 6);
v_messages_611_ = lean_ctor_get(v___x_602_, 7);
v_snapshotTasks_612_ = lean_ctor_get(v___x_602_, 9);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_633_ == 0)
{
v___x_614_ = v___x_602_;
v_isShared_615_ = v_isSharedCheck_633_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_snapshotTasks_612_);
lean_inc(v_infoState_603_);
lean_inc(v_messages_611_);
lean_inc(v_recordedDeps_610_);
lean_inc(v_cache_609_);
lean_inc(v_traceState_608_);
lean_inc(v_auxDeclNGen_607_);
lean_inc(v_ngen_606_);
lean_inc(v_nextMacroScope_605_);
lean_inc(v_env_604_);
lean_dec(v___x_602_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_633_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
uint8_t v_enabled_616_; lean_object* v_assignment_617_; lean_object* v_lazyAssignment_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_631_; 
v_enabled_616_ = lean_ctor_get_uint8(v_infoState_603_, sizeof(void*)*3);
v_assignment_617_ = lean_ctor_get(v_infoState_603_, 0);
v_lazyAssignment_618_ = lean_ctor_get(v_infoState_603_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_infoState_603_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_infoState_603_, 2);
lean_dec(v_unused_632_);
v___x_620_ = v_infoState_603_;
v_isShared_621_ = v_isSharedCheck_631_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_lazyAssignment_618_);
lean_inc(v_assignment_617_);
lean_dec(v_infoState_603_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_631_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 2, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_assignment_617_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_lazyAssignment_618_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v___x_622_);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, sizeof(void*)*3, v_enabled_616_);
v___x_624_ = v_reuseFailAlloc_630_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 8, v___x_624_);
v___x_626_ = v___x_614_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_env_604_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_nextMacroScope_605_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_ngen_606_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_auxDeclNGen_607_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_traceState_608_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v_cache_609_);
lean_ctor_set(v_reuseFailAlloc_629_, 6, v_recordedDeps_610_);
lean_ctor_set(v_reuseFailAlloc_629_, 7, v_messages_611_);
lean_ctor_set(v_reuseFailAlloc_629_, 8, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_629_, 9, v_snapshotTasks_612_);
v___x_626_ = v_reuseFailAlloc_629_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_st_ref_put(v___y_597_, v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_trees_601_);
return v___x_628_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_597_ = stack[0].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_597_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_635_);
lean_dec(v___y_635_);
return v_res_637_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_645_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_638_ = stack[0].m_obj;
lean_object* v___y_639_ = stack[1].m_obj;
lean_object* v___y_640_ = stack[2].m_obj;
lean_object* v___y_641_ = stack[3].m_obj;
lean_object* v___y_642_ = stack[4].m_obj;
lean_object* v___y_643_ = stack[5].m_obj;
lean_object* v___y_644_ = stack[6].m_obj;
lean_object* v___y_645_ = stack[7].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_658_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_msg_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___f_670_; lean_object* v___x_83974__overap_671_; lean_object* v___x_672_; 
v___f_670_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_83974__overap_671_ = lean_panic_fn_borrowed(v___f_670_, v_msg_660_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
v___x_672_ = lean_apply_9(v___x_83974__overap_671_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, lean_box(0));
return v___x_672_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_660_ = stack[0].m_obj;
lean_object* v___y_661_ = stack[1].m_obj;
lean_object* v___y_662_ = stack[2].m_obj;
lean_object* v___y_663_ = stack[3].m_obj;
lean_object* v___y_664_ = stack[4].m_obj;
lean_object* v___y_665_ = stack[5].m_obj;
lean_object* v___y_666_ = stack[6].m_obj;
lean_object* v___y_667_ = stack[7].m_obj;
lean_object* v___y_668_ = stack[8].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_msg_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
return v_res_684_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_ref_694_; uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_ref_694_ = lean_ctor_get(v___y_691_, 2);
v___x_695_ = 0;
v___x_696_ = l_Lean_SourceInfo_fromRef(v_ref_694_, v___x_695_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_685_ = stack[0].m_obj;
lean_object* v___y_686_ = stack[1].m_obj;
lean_object* v___y_687_ = stack[2].m_obj;
lean_object* v___y_688_ = stack[3].m_obj;
lean_object* v___y_689_ = stack[4].m_obj;
lean_object* v___y_690_ = stack[5].m_obj;
lean_object* v___y_691_ = stack[6].m_obj;
lean_object* v___y_692_ = stack[7].m_obj;
lean_object* v_res_698_;
v_res_698_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_708_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Array_mkArray0___redArg();
return v___x_716_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v_args_727_, lean_object* v_only_728_, uint8_t v___x_729_, lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v___x_732_, lean_object* v___y_733_, lean_object* v_unfold_734_, uint8_t v___x_735_, lean_object* v_squeeze_736_, lean_object* v_loc_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_810_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; uint8_t v___y_885_; 
if (lean_obj_tag(v_squeeze_736_) == 0)
{
uint8_t v___x_898_; 
v___x_898_ = 0;
v___y_885_ = v___x_898_;
goto v___jp_884_;
}
else
{
lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_1034_; 
v_isSharedCheck_1034_ = !lean_is_exclusive(v_squeeze_736_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_squeeze_736_, 0);
lean_dec(v_unused_1035_);
v___x_900_ = v_squeeze_736_;
v_isShared_901_ = v_isSharedCheck_1034_;
goto v_resetjp_899_;
}
else
{
lean_dec(v_squeeze_736_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_1034_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
if (v___x_735_ == 0)
{
lean_del_object(v___x_900_);
v___y_885_ = v___x_735_;
goto v___jp_884_;
}
else
{
if (lean_obj_tag(v_unfold_734_) == 0)
{
lean_object* v_ref_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_953_; 
v_ref_902_ = lean_ctor_get(v___y_744_, 2);
v___x_903_ = 0;
v___x_904_ = l_Lean_SourceInfo_fromRef(v_ref_902_, v___x_903_);
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9));
lean_inc_ref_n(v___x_732_, 2);
lean_inc_ref_n(v___x_731_, 2);
lean_inc_ref_n(v___x_730_, 2);
v___x_906_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_905_);
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10));
lean_inc_n(v___x_904_, 2);
v___x_908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_904_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_910_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
v___x_911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_911_, 0, v___x_904_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
lean_ctor_set(v___x_911_, 2, v___x_910_);
v___x_912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_913_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_912_);
if (lean_obj_tag(v___y_733_) == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_953_ = v___x_962_;
goto v___jp_952_;
}
else
{
lean_object* v_val_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_val_963_ = lean_ctor_get(v___y_733_, 0);
lean_inc(v_val_963_);
lean_dec_ref_known(v___y_733_, 1);
v___x_964_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___x_965_ = lean_array_push(v___x_964_, v_val_963_);
v___y_953_ = v___x_965_;
goto v___jp_952_;
}
v___jp_914_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_919_ = l_Array_append___redArg(v___x_910_, v___y_918_);
lean_dec_ref(v___y_918_);
lean_inc_n(v___x_904_, 2);
v___x_920_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_920_, 0, v___x_904_);
lean_ctor_set(v___x_920_, 1, v___x_909_);
lean_ctor_set(v___x_920_, 2, v___x_919_);
v___x_921_ = l_Lean_Syntax_node5(v___x_904_, v___x_913_, v___x_725_, v___y_916_, v___y_917_, v___y_915_, v___x_920_);
v___x_922_ = l_Lean_Syntax_node3(v___x_904_, v___x_906_, v___x_908_, v___x_911_, v___x_921_);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 0);
lean_ctor_set(v___x_900_, 0, v___x_922_);
v___x_924_ = v___x_900_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
v___jp_926_:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = l_Array_append___redArg(v___x_910_, v___y_929_);
lean_dec_ref(v___y_929_);
lean_inc(v___x_904_);
v___x_931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_931_, 0, v___x_904_);
lean_ctor_set(v___x_931_, 1, v___x_909_);
lean_ctor_set(v___x_931_, 2, v___x_930_);
if (lean_obj_tag(v_loc_737_) == 1)
{
lean_object* v_val_932_; lean_object* v___x_933_; 
v_val_932_ = lean_ctor_get(v_loc_737_, 0);
lean_inc(v_val_932_);
lean_dec_ref_known(v_loc_737_, 1);
v___x_933_ = l_Array_mkArray1___redArg(v_val_932_);
v___y_915_ = v___x_931_;
v___y_916_ = v___y_927_;
v___y_917_ = v___y_928_;
v___y_918_ = v___x_933_;
goto v___jp_914_;
}
else
{
lean_object* v___x_934_; 
lean_dec(v_loc_737_);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_915_ = v___x_931_;
v___y_916_ = v___y_927_;
v___y_917_ = v___y_928_;
v___y_918_ = v___x_934_;
goto v___jp_914_;
}
}
v___jp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = l_Array_append___redArg(v___x_910_, v___y_937_);
lean_dec_ref(v___y_937_);
lean_inc(v___x_904_);
v___x_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_939_, 0, v___x_904_);
lean_ctor_set(v___x_939_, 1, v___x_909_);
lean_ctor_set(v___x_939_, 2, v___x_938_);
if (lean_obj_tag(v_args_727_) == 1)
{
lean_object* v_val_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_val_940_ = lean_ctor_get(v_args_727_, 0);
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_942_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_941_);
v___x_943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_904_, 4);
v___x_944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_904_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Array_append___redArg(v___x_910_, v_val_940_);
v___x_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_946_, 0, v___x_904_);
lean_ctor_set(v___x_946_, 1, v___x_909_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_948_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_904_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_Syntax_node3(v___x_904_, v___x_942_, v___x_944_, v___x_946_, v___x_948_);
v___x_950_ = l_Array_mkArray1___redArg(v___x_949_);
v___y_927_ = v___y_936_;
v___y_928_ = v___x_939_;
v___y_929_ = v___x_950_;
goto v___jp_926_;
}
else
{
lean_object* v___x_951_; 
lean_dec_ref(v___x_732_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v___x_730_);
v___x_951_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_927_ = v___y_936_;
v___y_928_ = v___x_939_;
v___y_929_ = v___x_951_;
goto v___jp_926_;
}
}
v___jp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Array_append___redArg(v___x_910_, v___y_953_);
lean_dec_ref(v___y_953_);
lean_inc(v___x_904_);
v___x_955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_955_, 0, v___x_904_);
lean_ctor_set(v___x_955_, 1, v___x_909_);
lean_ctor_set(v___x_955_, 2, v___x_954_);
if (lean_obj_tag(v_only_728_) == 1)
{
lean_object* v_val_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_val_956_ = lean_ctor_get(v_only_728_, 0);
v___x_957_ = l_Lean_SourceInfo_fromRef(v_val_956_, v___x_729_);
v___x_958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Array_mkArray1___redArg(v___x_959_);
v___y_936_ = v___x_955_;
v___y_937_ = v___x_960_;
goto v___jp_935_;
}
else
{
lean_object* v___x_961_; 
v___x_961_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_936_ = v___x_955_;
v___y_937_ = v___x_961_;
goto v___jp_935_;
}
}
}
else
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1032_; 
lean_del_object(v___x_900_);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_unfold_734_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_unfold_734_, 0);
lean_dec(v_unused_1033_);
v___x_967_ = v_unfold_734_;
v_isShared_968_ = v_isSharedCheck_1032_;
goto v_resetjp_966_;
}
else
{
lean_dec(v_unfold_734_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1032_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_ref_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1019_; 
v_ref_969_ = lean_ctor_get(v___y_744_, 2);
v___x_970_ = 0;
v___x_971_ = l_Lean_SourceInfo_fromRef(v_ref_969_, v___x_970_);
v___x_972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13));
lean_inc_ref_n(v___x_732_, 2);
lean_inc_ref_n(v___x_731_, 2);
lean_inc_ref_n(v___x_730_, 2);
v___x_973_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_972_);
v___x_974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14));
lean_inc(v___x_971_);
v___x_975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_971_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_977_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_976_);
v___x_978_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_979_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_733_) == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_1019_ = v___x_1028_;
goto v___jp_1018_;
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_val_1029_ = lean_ctor_get(v___y_733_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v___y_733_, 1);
v___x_1030_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___x_1031_ = lean_array_push(v___x_1030_, v_val_1029_);
v___y_1019_ = v___x_1031_;
goto v___jp_1018_;
}
v___jp_980_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_985_ = l_Array_append___redArg(v___x_979_, v___y_984_);
lean_dec_ref(v___y_984_);
lean_inc_n(v___x_971_, 2);
v___x_986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_986_, 0, v___x_971_);
lean_ctor_set(v___x_986_, 1, v___x_978_);
lean_ctor_set(v___x_986_, 2, v___x_985_);
v___x_987_ = l_Lean_Syntax_node5(v___x_971_, v___x_977_, v___x_725_, v___y_982_, v___y_981_, v___y_983_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node2(v___x_971_, v___x_973_, v___x_975_, v___x_987_);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 0);
lean_ctor_set(v___x_967_, 0, v___x_988_);
v___x_990_ = v___x_967_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
v___jp_992_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = l_Array_append___redArg(v___x_979_, v___y_995_);
lean_dec_ref(v___y_995_);
lean_inc(v___x_971_);
v___x_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_997_, 0, v___x_971_);
lean_ctor_set(v___x_997_, 1, v___x_978_);
lean_ctor_set(v___x_997_, 2, v___x_996_);
if (lean_obj_tag(v_loc_737_) == 1)
{
lean_object* v_val_998_; lean_object* v___x_999_; 
v_val_998_ = lean_ctor_get(v_loc_737_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_loc_737_, 1);
v___x_999_ = l_Array_mkArray1___redArg(v_val_998_);
v___y_981_ = v___y_993_;
v___y_982_ = v___y_994_;
v___y_983_ = v___x_997_;
v___y_984_ = v___x_999_;
goto v___jp_980_;
}
else
{
lean_object* v___x_1000_; 
lean_dec(v_loc_737_);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_981_ = v___y_993_;
v___y_982_ = v___y_994_;
v___y_983_ = v___x_997_;
v___y_984_ = v___x_1000_;
goto v___jp_980_;
}
}
v___jp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = l_Array_append___redArg(v___x_979_, v___y_1003_);
lean_dec_ref(v___y_1003_);
lean_inc(v___x_971_);
v___x_1005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1005_, 0, v___x_971_);
lean_ctor_set(v___x_1005_, 1, v___x_978_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
if (lean_obj_tag(v_args_727_) == 1)
{
lean_object* v_val_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_val_1006_ = lean_ctor_get(v_args_727_, 0);
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_1008_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_1007_);
v___x_1009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_971_, 4);
v___x_1010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_971_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Array_append___redArg(v___x_979_, v_val_1006_);
v___x_1012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1012_, 0, v___x_971_);
lean_ctor_set(v___x_1012_, 1, v___x_978_);
lean_ctor_set(v___x_1012_, 2, v___x_1011_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_1014_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_971_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_Syntax_node3(v___x_971_, v___x_1008_, v___x_1010_, v___x_1012_, v___x_1014_);
v___x_1016_ = l_Array_mkArray1___redArg(v___x_1015_);
v___y_993_ = v___x_1005_;
v___y_994_ = v___y_1002_;
v___y_995_ = v___x_1016_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1017_; 
lean_dec_ref(v___x_732_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v___x_730_);
v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_993_ = v___x_1005_;
v___y_994_ = v___y_1002_;
v___y_995_ = v___x_1017_;
goto v___jp_992_;
}
}
v___jp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = l_Array_append___redArg(v___x_979_, v___y_1019_);
lean_dec_ref(v___y_1019_);
lean_inc(v___x_971_);
v___x_1021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1021_, 0, v___x_971_);
lean_ctor_set(v___x_1021_, 1, v___x_978_);
lean_ctor_set(v___x_1021_, 2, v___x_1020_);
if (lean_obj_tag(v_only_728_) == 1)
{
lean_object* v_val_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_val_1022_ = lean_ctor_get(v_only_728_, 0);
v___x_1023_ = l_Lean_SourceInfo_fromRef(v_val_1022_, v___x_729_);
v___x_1024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_1025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = l_Array_mkArray1___redArg(v___x_1025_);
v___y_1002_ = v___x_1021_;
v___y_1003_ = v___x_1026_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_1002_ = v___x_1021_;
v___y_1003_ = v___x_1027_;
goto v___jp_1001_;
}
}
}
}
}
}
}
v___jp_747_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_inc_ref(v___y_754_);
v___x_757_ = l_Array_append___redArg(v___y_754_, v___y_756_);
lean_dec_ref(v___y_756_);
lean_inc(v___y_755_);
lean_inc(v___y_751_);
v___x_758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_758_, 0, v___y_751_);
lean_ctor_set(v___x_758_, 1, v___y_755_);
lean_ctor_set(v___x_758_, 2, v___x_757_);
v___x_759_ = l_Lean_Syntax_node6(v___y_751_, v___y_748_, v___y_750_, v___x_725_, v___y_749_, v___y_753_, v___y_752_, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
v___jp_761_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc_ref(v___y_767_);
v___x_770_ = l_Array_append___redArg(v___y_767_, v___y_769_);
lean_dec_ref(v___y_769_);
lean_inc(v___y_768_);
lean_inc(v___y_765_);
v___x_771_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_771_, 0, v___y_765_);
lean_ctor_set(v___x_771_, 1, v___y_768_);
lean_ctor_set(v___x_771_, 2, v___x_770_);
if (lean_obj_tag(v_loc_737_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_773_; 
v_val_772_ = lean_ctor_get(v_loc_737_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v_loc_737_, 1);
v___x_773_ = l_Array_mkArray1___redArg(v_val_772_);
v___y_748_ = v___y_762_;
v___y_749_ = v___y_763_;
v___y_750_ = v___y_764_;
v___y_751_ = v___y_765_;
v___y_752_ = v___x_771_;
v___y_753_ = v___y_766_;
v___y_754_ = v___y_767_;
v___y_755_ = v___y_768_;
v___y_756_ = v___x_773_;
goto v___jp_747_;
}
else
{
lean_object* v___x_774_; 
lean_dec(v_loc_737_);
v___x_774_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_748_ = v___y_762_;
v___y_749_ = v___y_763_;
v___y_750_ = v___y_764_;
v___y_751_ = v___y_765_;
v___y_752_ = v___x_771_;
v___y_753_ = v___y_766_;
v___y_754_ = v___y_767_;
v___y_755_ = v___y_768_;
v___y_756_ = v___x_774_;
goto v___jp_747_;
}
}
v___jp_775_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_inc_ref(v___y_780_);
v___x_783_ = l_Array_append___redArg(v___y_780_, v___y_782_);
lean_dec_ref(v___y_782_);
lean_inc(v___y_781_);
lean_inc(v___y_779_);
v___x_784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_784_, 0, v___y_779_);
lean_ctor_set(v___x_784_, 1, v___y_781_);
lean_ctor_set(v___x_784_, 2, v___x_783_);
if (lean_obj_tag(v_args_727_) == 1)
{
lean_object* v_val_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_val_785_ = lean_ctor_get(v_args_727_, 0);
v___x_786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_779_, 3);
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v___y_779_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
lean_inc_ref(v___y_780_);
v___x_788_ = l_Array_append___redArg(v___y_780_, v_val_785_);
lean_inc(v___y_781_);
v___x_789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_789_, 0, v___y_779_);
lean_ctor_set(v___x_789_, 1, v___y_781_);
lean_ctor_set(v___x_789_, 2, v___x_788_);
v___x_790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_791_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_791_, 0, v___y_779_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Array_mkArray3___redArg(v___x_787_, v___x_789_, v___x_791_);
v___y_762_ = v___y_776_;
v___y_763_ = v___y_777_;
v___y_764_ = v___y_778_;
v___y_765_ = v___y_779_;
v___y_766_ = v___x_784_;
v___y_767_ = v___y_780_;
v___y_768_ = v___y_781_;
v___y_769_ = v___x_792_;
goto v___jp_761_;
}
else
{
lean_object* v___x_793_; 
v___x_793_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_762_ = v___y_776_;
v___y_763_ = v___y_777_;
v___y_764_ = v___y_778_;
v___y_765_ = v___y_779_;
v___y_766_ = v___x_784_;
v___y_767_ = v___y_780_;
v___y_768_ = v___y_781_;
v___y_769_ = v___x_793_;
goto v___jp_761_;
}
}
v___jp_794_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_inc_ref(v___y_798_);
v___x_801_ = l_Array_append___redArg(v___y_798_, v___y_800_);
lean_dec_ref(v___y_800_);
lean_inc(v___y_799_);
lean_inc(v___y_797_);
v___x_802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_802_, 0, v___y_797_);
lean_ctor_set(v___x_802_, 1, v___y_799_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
if (lean_obj_tag(v_only_728_) == 1)
{
lean_object* v_val_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_val_803_ = lean_ctor_get(v_only_728_, 0);
v___x_804_ = l_Lean_SourceInfo_fromRef(v_val_803_, v___x_729_);
v___x_805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Array_mkArray1___redArg(v___x_806_);
v___y_776_ = v___y_795_;
v___y_777_ = v___x_802_;
v___y_778_ = v___y_796_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_798_;
v___y_781_ = v___y_799_;
v___y_782_ = v___x_807_;
goto v___jp_775_;
}
else
{
lean_object* v___x_808_; 
v___x_808_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_776_ = v___y_795_;
v___y_777_ = v___x_802_;
v___y_778_ = v___y_796_;
v___y_779_ = v___y_797_;
v___y_780_ = v___y_798_;
v___y_781_ = v___y_799_;
v___y_782_ = v___x_808_;
goto v___jp_775_;
}
}
v___jp_809_:
{
lean_object* v_ref_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_ref_811_ = lean_ctor_get(v___y_744_, 2);
v___x_812_ = l_Lean_SourceInfo_fromRef(v_ref_811_, v___y_810_);
v___x_813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
v___x_814_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_813_);
lean_inc(v___x_812_);
v___x_815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_812_);
lean_ctor_set(v___x_815_, 1, v___x_813_);
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_817_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_733_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_795_ = v___x_814_;
v___y_796_ = v___x_815_;
v___y_797_ = v___x_812_;
v___y_798_ = v___x_817_;
v___y_799_ = v___x_816_;
v___y_800_ = v___x_818_;
goto v___jp_794_;
}
else
{
lean_object* v_val_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_val_819_ = lean_ctor_get(v___y_733_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v___y_733_, 1);
v___x_820_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___x_821_ = lean_array_push(v___x_820_, v_val_819_);
v___y_795_ = v___x_814_;
v___y_796_ = v___x_815_;
v___y_797_ = v___x_812_;
v___y_798_ = v___x_817_;
v___y_799_ = v___x_816_;
v___y_800_ = v___x_821_;
goto v___jp_794_;
}
}
v___jp_822_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc_ref(v___y_830_);
v___x_832_ = l_Array_append___redArg(v___y_830_, v___y_831_);
lean_dec_ref(v___y_831_);
lean_inc(v___y_825_);
lean_inc(v___y_824_);
v___x_833_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_833_, 0, v___y_824_);
lean_ctor_set(v___x_833_, 1, v___y_825_);
lean_ctor_set(v___x_833_, 2, v___x_832_);
v___x_834_ = l_Lean_Syntax_node6(v___y_824_, v___y_829_, v___y_827_, v___x_725_, v___y_826_, v___y_828_, v___y_823_, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
v___jp_836_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_inc_ref(v___y_843_);
v___x_845_ = l_Array_append___redArg(v___y_843_, v___y_844_);
lean_dec_ref(v___y_844_);
lean_inc(v___y_838_);
lean_inc(v___y_837_);
v___x_846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_846_, 0, v___y_837_);
lean_ctor_set(v___x_846_, 1, v___y_838_);
lean_ctor_set(v___x_846_, 2, v___x_845_);
if (lean_obj_tag(v_loc_737_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_848_; 
v_val_847_ = lean_ctor_get(v_loc_737_, 0);
lean_inc(v_val_847_);
lean_dec_ref_known(v_loc_737_, 1);
v___x_848_ = l_Array_mkArray1___redArg(v_val_847_);
v___y_823_ = v___x_846_;
v___y_824_ = v___y_837_;
v___y_825_ = v___y_838_;
v___y_826_ = v___y_839_;
v___y_827_ = v___y_840_;
v___y_828_ = v___y_841_;
v___y_829_ = v___y_842_;
v___y_830_ = v___y_843_;
v___y_831_ = v___x_848_;
goto v___jp_822_;
}
else
{
lean_object* v___x_849_; 
lean_dec(v_loc_737_);
v___x_849_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_823_ = v___x_846_;
v___y_824_ = v___y_837_;
v___y_825_ = v___y_838_;
v___y_826_ = v___y_839_;
v___y_827_ = v___y_840_;
v___y_828_ = v___y_841_;
v___y_829_ = v___y_842_;
v___y_830_ = v___y_843_;
v___y_831_ = v___x_849_;
goto v___jp_822_;
}
}
v___jp_850_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_inc_ref(v___y_856_);
v___x_858_ = l_Array_append___redArg(v___y_856_, v___y_857_);
lean_dec_ref(v___y_857_);
lean_inc(v___y_852_);
lean_inc(v___y_851_);
v___x_859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_859_, 0, v___y_851_);
lean_ctor_set(v___x_859_, 1, v___y_852_);
lean_ctor_set(v___x_859_, 2, v___x_858_);
if (lean_obj_tag(v_args_727_) == 1)
{
lean_object* v_val_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_val_860_ = lean_ctor_get(v_args_727_, 0);
v___x_861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_851_, 3);
v___x_862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_862_, 0, v___y_851_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
lean_inc_ref(v___y_856_);
v___x_863_ = l_Array_append___redArg(v___y_856_, v_val_860_);
lean_inc(v___y_852_);
v___x_864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_864_, 0, v___y_851_);
lean_ctor_set(v___x_864_, 1, v___y_852_);
lean_ctor_set(v___x_864_, 2, v___x_863_);
v___x_865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v___y_851_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = l_Array_mkArray3___redArg(v___x_862_, v___x_864_, v___x_866_);
v___y_837_ = v___y_851_;
v___y_838_ = v___y_852_;
v___y_839_ = v___y_853_;
v___y_840_ = v___y_854_;
v___y_841_ = v___x_859_;
v___y_842_ = v___y_855_;
v___y_843_ = v___y_856_;
v___y_844_ = v___x_867_;
goto v___jp_836_;
}
else
{
lean_object* v___x_868_; 
v___x_868_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_837_ = v___y_851_;
v___y_838_ = v___y_852_;
v___y_839_ = v___y_853_;
v___y_840_ = v___y_854_;
v___y_841_ = v___x_859_;
v___y_842_ = v___y_855_;
v___y_843_ = v___y_856_;
v___y_844_ = v___x_868_;
goto v___jp_836_;
}
}
v___jp_869_:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc_ref(v___y_874_);
v___x_876_ = l_Array_append___redArg(v___y_874_, v___y_875_);
lean_dec_ref(v___y_875_);
lean_inc(v___y_871_);
lean_inc(v___y_870_);
v___x_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_877_, 0, v___y_870_);
lean_ctor_set(v___x_877_, 1, v___y_871_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
if (lean_obj_tag(v_only_728_) == 1)
{
lean_object* v_val_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_val_878_ = lean_ctor_get(v_only_728_, 0);
v___x_879_ = l_Lean_SourceInfo_fromRef(v_val_878_, v___x_729_);
v___x_880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Array_mkArray1___redArg(v___x_881_);
v___y_851_ = v___y_870_;
v___y_852_ = v___y_871_;
v___y_853_ = v___x_877_;
v___y_854_ = v___y_872_;
v___y_855_ = v___y_873_;
v___y_856_ = v___y_874_;
v___y_857_ = v___x_882_;
goto v___jp_850_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_851_ = v___y_870_;
v___y_852_ = v___y_871_;
v___y_853_ = v___x_877_;
v___y_854_ = v___y_872_;
v___y_855_ = v___y_873_;
v___y_856_ = v___y_874_;
v___y_857_ = v___x_883_;
goto v___jp_850_;
}
}
v___jp_884_:
{
if (lean_obj_tag(v_unfold_734_) == 0)
{
v___y_810_ = v___y_885_;
goto v___jp_809_;
}
else
{
lean_dec_ref_known(v_unfold_734_, 1);
if (v___x_735_ == 0)
{
v___y_810_ = v___x_735_;
goto v___jp_809_;
}
else
{
lean_object* v_ref_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_ref_886_ = lean_ctor_get(v___y_744_, 2);
v___x_887_ = l_Lean_SourceInfo_fromRef(v_ref_886_, v___y_885_);
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7));
v___x_889_ = l_Lean_Name_mkStr4(v___x_730_, v___x_731_, v___x_732_, v___x_888_);
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8));
lean_inc(v___x_887_);
v___x_891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_887_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_893_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_733_) == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___y_870_ = v___x_887_;
v___y_871_ = v___x_892_;
v___y_872_ = v___x_891_;
v___y_873_ = v___x_889_;
v___y_874_ = v___x_893_;
v___y_875_ = v___x_894_;
goto v___jp_869_;
}
else
{
lean_object* v_val_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_val_895_ = lean_ctor_get(v___y_733_, 0);
lean_inc(v_val_895_);
lean_dec_ref_known(v___y_733_, 1);
v___x_896_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___x_897_ = lean_array_push(v___x_896_, v_val_895_);
v___y_870_ = v___x_887_;
v___y_871_ = v___x_892_;
v___y_872_ = v___x_891_;
v___y_873_ = v___x_889_;
v___y_874_ = v___x_893_;
v___y_875_ = v___x_897_;
goto v___jp_869_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_725_ = stack[0].m_obj;
lean_object* v___x_726_ = stack[1].m_obj;
lean_object* v_args_727_ = stack[2].m_obj;
lean_object* v_only_728_ = stack[3].m_obj;
uint8_t v___x_729_ = stack[4].m_num;
lean_object* v___x_730_ = stack[5].m_obj;
lean_object* v___x_731_ = stack[6].m_obj;
lean_object* v___x_732_ = stack[7].m_obj;
lean_object* v___y_733_ = stack[8].m_obj;
lean_object* v_unfold_734_ = stack[9].m_obj;
uint8_t v___x_735_ = stack[10].m_num;
lean_object* v_squeeze_736_ = stack[11].m_obj;
lean_object* v_loc_737_ = stack[12].m_obj;
lean_object* v___y_738_ = stack[13].m_obj;
lean_object* v___y_739_ = stack[14].m_obj;
lean_object* v___y_740_ = stack[15].m_obj;
lean_object* v___y_741_ = stack[16].m_obj;
lean_object* v___y_742_ = stack[17].m_obj;
lean_object* v___y_743_ = stack[18].m_obj;
lean_object* v___y_744_ = stack[19].m_obj;
lean_object* v___y_745_ = stack[20].m_obj;
lean_object* v_res_1036_;
v_res_1036_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_725_, v___x_726_, v_args_727_, v_only_728_, v___x_729_, v___x_730_, v___x_731_, v___x_732_, v___y_733_, v_unfold_734_, v___x_735_, v_squeeze_736_, v_loc_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
stack->m_obj
 = v_res_1036_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_1037_ = _args[0];
lean_object* v___x_1038_ = _args[1];
lean_object* v_args_1039_ = _args[2];
lean_object* v_only_1040_ = _args[3];
lean_object* v___x_1041_ = _args[4];
lean_object* v___x_1042_ = _args[5];
lean_object* v___x_1043_ = _args[6];
lean_object* v___x_1044_ = _args[7];
lean_object* v___y_1045_ = _args[8];
lean_object* v_unfold_1046_ = _args[9];
lean_object* v___x_1047_ = _args[10];
lean_object* v_squeeze_1048_ = _args[11];
lean_object* v_loc_1049_ = _args[12];
lean_object* v___y_1050_ = _args[13];
lean_object* v___y_1051_ = _args[14];
lean_object* v___y_1052_ = _args[15];
lean_object* v___y_1053_ = _args[16];
lean_object* v___y_1054_ = _args[17];
lean_object* v___y_1055_ = _args[18];
lean_object* v___y_1056_ = _args[19];
lean_object* v___y_1057_ = _args[20];
lean_object* v___y_1058_ = _args[21];
_start:
{
uint8_t v___x_93414__boxed_1059_; uint8_t v___x_93419__boxed_1060_; lean_object* v_res_1061_; 
v___x_93414__boxed_1059_ = lean_unbox(v___x_1041_);
v___x_93419__boxed_1060_ = lean_unbox(v___x_1047_);
v_res_1061_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_1037_, v___x_1038_, v_args_1039_, v_only_1040_, v___x_93414__boxed_1059_, v___x_1042_, v___x_1043_, v___x_1044_, v___y_1045_, v_unfold_1046_, v___x_93419__boxed_1060_, v_squeeze_1048_, v_loc_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v_only_1040_);
lean_dec(v_args_1039_);
lean_dec(v___x_1038_);
return v_res_1061_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_1062_, lean_object* v_trees_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
v___x_1073_ = lean_apply_9(v_a_1062_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, lean_box(0));
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_a_1074_);
lean_ctor_set(v___x_1078_, 1, v_trees_1063_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_trees_1063_);
v_a_1083_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1073_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1073_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1062_ = stack[0].m_obj;
lean_object* v_trees_1063_ = stack[1].m_obj;
lean_object* v___y_1064_ = stack[2].m_obj;
lean_object* v___y_1065_ = stack[3].m_obj;
lean_object* v___y_1066_ = stack[4].m_obj;
lean_object* v___y_1067_ = stack[5].m_obj;
lean_object* v___y_1068_ = stack[6].m_obj;
lean_object* v___y_1069_ = stack[7].m_obj;
lean_object* v___y_1070_ = stack[8].m_obj;
lean_object* v___y_1071_ = stack[9].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1062_, v_trees_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object* v_a_1092_, lean_object* v_trees_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1092_, v_trees_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1103_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1110_, lean_object* v_a_1111_, uint8_t v___x_1112_, lean_object* v_a_1113_, lean_object* v_mvarCounter_1114_, lean_object* v___x_1115_, uint8_t v___x_1116_, lean_object* v___x_1117_, uint8_t v_useReducible_1118_, uint8_t v___x_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
lean_inc(v_a_1110_);
v___x_1129_ = l_Lean_MVarId_getType(v_a_1110_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc_n(v_a_1130_, 2);
lean_dec_ref_known(v___x_1129_, 1);
v___x_1131_ = l_Lean_mkIdent(v_a_1111_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_a_1130_);
v___x_1133_ = l_Lean_Elab_Term_elabTerm(v___x_1131_, v___x_1132_, v___x_1112_, v___x_1112_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___x_1168_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1168_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1116_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1351_; 
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v___x_1168_, 0);
lean_dec(v_unused_1352_);
v___x_1170_ = v___x_1168_;
v_isShared_1171_ = v_isSharedCheck_1351_;
goto v_resetjp_1169_;
}
else
{
lean_dec(v___x_1168_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1351_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; 
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc(v___y_1125_);
lean_inc_ref(v___y_1124_);
lean_inc(v_a_1134_);
v___x_1172_ = lean_infer_type(v_a_1134_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; uint8_t v_____do__lift_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1194_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
if (v_useReducible_1118_ == 0)
{
lean_object* v___x_1205_; uint8_t v_foApprox_1206_; uint8_t v_ctxApprox_1207_; uint8_t v_quasiPatternApprox_1208_; uint8_t v_constApprox_1209_; uint8_t v_isDefEqStuckEx_1210_; uint8_t v_unificationHints_1211_; uint8_t v_proofIrrelevance_1212_; uint8_t v_offsetCnstrs_1213_; uint8_t v_transparency_1214_; uint8_t v_etaStruct_1215_; uint8_t v_univApprox_1216_; uint8_t v_iota_1217_; uint8_t v_beta_1218_; uint8_t v_proj_1219_; uint8_t v_zeta_1220_; uint8_t v_zetaDelta_1221_; uint8_t v_zetaUnused_1222_; uint8_t v_zetaHave_1223_; uint8_t v_canUnfoldPredicateConfig_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1255_; 
v___x_1205_ = l_Lean_Meta_Context_config(v___y_1124_);
v_foApprox_1206_ = lean_ctor_get_uint8(v___x_1205_, 0);
v_ctxApprox_1207_ = lean_ctor_get_uint8(v___x_1205_, 1);
v_quasiPatternApprox_1208_ = lean_ctor_get_uint8(v___x_1205_, 2);
v_constApprox_1209_ = lean_ctor_get_uint8(v___x_1205_, 3);
v_isDefEqStuckEx_1210_ = lean_ctor_get_uint8(v___x_1205_, 4);
v_unificationHints_1211_ = lean_ctor_get_uint8(v___x_1205_, 5);
v_proofIrrelevance_1212_ = lean_ctor_get_uint8(v___x_1205_, 6);
v_offsetCnstrs_1213_ = lean_ctor_get_uint8(v___x_1205_, 8);
v_transparency_1214_ = lean_ctor_get_uint8(v___x_1205_, 9);
v_etaStruct_1215_ = lean_ctor_get_uint8(v___x_1205_, 10);
v_univApprox_1216_ = lean_ctor_get_uint8(v___x_1205_, 11);
v_iota_1217_ = lean_ctor_get_uint8(v___x_1205_, 12);
v_beta_1218_ = lean_ctor_get_uint8(v___x_1205_, 13);
v_proj_1219_ = lean_ctor_get_uint8(v___x_1205_, 14);
v_zeta_1220_ = lean_ctor_get_uint8(v___x_1205_, 15);
v_zetaDelta_1221_ = lean_ctor_get_uint8(v___x_1205_, 16);
v_zetaUnused_1222_ = lean_ctor_get_uint8(v___x_1205_, 17);
v_zetaHave_1223_ = lean_ctor_get_uint8(v___x_1205_, 18);
v_canUnfoldPredicateConfig_1224_ = lean_ctor_get_uint8(v___x_1205_, 19);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1226_ = v___x_1205_;
v_isShared_1227_ = v_isSharedCheck_1255_;
goto v_resetjp_1225_;
}
else
{
lean_dec(v___x_1205_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1255_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
uint8_t v_trackZetaDelta_1228_; lean_object* v_zetaDeltaSet_1229_; lean_object* v_lctx_1230_; lean_object* v_localInstances_1231_; lean_object* v_defEqCtx_x3f_1232_; lean_object* v_synthPendingDepth_1233_; lean_object* v_customCanUnfoldPredicate_x3f_1234_; uint8_t v_univApprox_1235_; uint8_t v_inTypeClassResolution_1236_; uint8_t v_cacheInferType_1237_; lean_object* v___x_1239_; 
v_trackZetaDelta_1228_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7);
v_zetaDeltaSet_1229_ = lean_ctor_get(v___y_1124_, 1);
v_lctx_1230_ = lean_ctor_get(v___y_1124_, 2);
v_localInstances_1231_ = lean_ctor_get(v___y_1124_, 3);
v_defEqCtx_x3f_1232_ = lean_ctor_get(v___y_1124_, 4);
v_synthPendingDepth_1233_ = lean_ctor_get(v___y_1124_, 5);
v_customCanUnfoldPredicate_x3f_1234_ = lean_ctor_get(v___y_1124_, 6);
v_univApprox_1235_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1236_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 2);
v_cacheInferType_1237_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 3);
if (v_isShared_1227_ == 0)
{
v___x_1239_ = v___x_1226_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 0, v_foApprox_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 1, v_ctxApprox_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 2, v_quasiPatternApprox_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 3, v_constApprox_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 4, v_isDefEqStuckEx_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 5, v_unificationHints_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 6, v_proofIrrelevance_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 8, v_offsetCnstrs_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 9, v_transparency_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 10, v_etaStruct_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 11, v_univApprox_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 12, v_iota_1217_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 13, v_beta_1218_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 14, v_proj_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 15, v_zeta_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 16, v_zetaDelta_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 17, v_zetaUnused_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 18, v_zetaHave_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1254_, 19, v_canUnfoldPredicateConfig_1224_);
v___x_1239_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
uint64_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_ctor_set_uint8(v___x_1239_, 7, v___x_1119_);
v___x_1240_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set_uint64(v___x_1241_, sizeof(void*)*1, v___x_1240_);
lean_inc(v_customCanUnfoldPredicate_x3f_1234_);
lean_inc(v_synthPendingDepth_1233_);
lean_inc(v_defEqCtx_x3f_1232_);
lean_inc_ref(v_localInstances_1231_);
lean_inc_ref(v_lctx_1230_);
lean_inc(v_zetaDeltaSet_1229_);
v___x_1242_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_zetaDeltaSet_1229_);
lean_ctor_set(v___x_1242_, 2, v_lctx_1230_);
lean_ctor_set(v___x_1242_, 3, v_localInstances_1231_);
lean_ctor_set(v___x_1242_, 4, v_defEqCtx_x3f_1232_);
lean_ctor_set(v___x_1242_, 5, v_synthPendingDepth_1233_);
lean_ctor_set(v___x_1242_, 6, v_customCanUnfoldPredicate_x3f_1234_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*7, v_trackZetaDelta_1228_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*7 + 1, v_univApprox_1235_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1236_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*7 + 3, v_cacheInferType_1237_);
lean_inc(v_a_1173_);
lean_inc(v_a_1130_);
v___x_1243_ = l_Lean_Meta_isExprDefEq(v_a_1130_, v_a_1173_, v___x_1242_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec_ref_known(v___x_1242_, 7);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; uint8_t v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = lean_unbox(v_a_1244_);
lean_dec(v_a_1244_);
v_____do__lift_1175_ = v___x_1245_;
v___y_1176_ = v___y_1120_;
v___y_1177_ = v___y_1121_;
v___y_1178_ = v___y_1122_;
v___y_1179_ = v___y_1123_;
v___y_1180_ = v___y_1124_;
v___y_1181_ = v___y_1125_;
v___y_1182_ = v___y_1126_;
v___y_1183_ = v___y_1127_;
goto v___jp_1174_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_a_1173_);
lean_del_object(v___x_1170_);
lean_dec(v_a_1134_);
lean_dec(v_a_1130_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___x_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1110_);
v_a_1246_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1243_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1243_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
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
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
}
else
{
lean_object* v___x_1256_; uint8_t v_foApprox_1257_; uint8_t v_ctxApprox_1258_; uint8_t v_quasiPatternApprox_1259_; uint8_t v_constApprox_1260_; uint8_t v_isDefEqStuckEx_1261_; uint8_t v_unificationHints_1262_; uint8_t v_proofIrrelevance_1263_; uint8_t v_offsetCnstrs_1264_; uint8_t v_transparency_1265_; uint8_t v_etaStruct_1266_; uint8_t v_univApprox_1267_; uint8_t v_iota_1268_; uint8_t v_beta_1269_; uint8_t v_proj_1270_; uint8_t v_zeta_1271_; uint8_t v_zetaDelta_1272_; uint8_t v_zetaUnused_1273_; uint8_t v_zetaHave_1274_; uint8_t v_canUnfoldPredicateConfig_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1342_; 
v___x_1256_ = l_Lean_Meta_Context_config(v___y_1124_);
v_foApprox_1257_ = lean_ctor_get_uint8(v___x_1256_, 0);
v_ctxApprox_1258_ = lean_ctor_get_uint8(v___x_1256_, 1);
v_quasiPatternApprox_1259_ = lean_ctor_get_uint8(v___x_1256_, 2);
v_constApprox_1260_ = lean_ctor_get_uint8(v___x_1256_, 3);
v_isDefEqStuckEx_1261_ = lean_ctor_get_uint8(v___x_1256_, 4);
v_unificationHints_1262_ = lean_ctor_get_uint8(v___x_1256_, 5);
v_proofIrrelevance_1263_ = lean_ctor_get_uint8(v___x_1256_, 6);
v_offsetCnstrs_1264_ = lean_ctor_get_uint8(v___x_1256_, 8);
v_transparency_1265_ = lean_ctor_get_uint8(v___x_1256_, 9);
v_etaStruct_1266_ = lean_ctor_get_uint8(v___x_1256_, 10);
v_univApprox_1267_ = lean_ctor_get_uint8(v___x_1256_, 11);
v_iota_1268_ = lean_ctor_get_uint8(v___x_1256_, 12);
v_beta_1269_ = lean_ctor_get_uint8(v___x_1256_, 13);
v_proj_1270_ = lean_ctor_get_uint8(v___x_1256_, 14);
v_zeta_1271_ = lean_ctor_get_uint8(v___x_1256_, 15);
v_zetaDelta_1272_ = lean_ctor_get_uint8(v___x_1256_, 16);
v_zetaUnused_1273_ = lean_ctor_get_uint8(v___x_1256_, 17);
v_zetaHave_1274_ = lean_ctor_get_uint8(v___x_1256_, 18);
v_canUnfoldPredicateConfig_1275_ = lean_ctor_get_uint8(v___x_1256_, 19);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1277_ = v___x_1256_;
v_isShared_1278_ = v_isSharedCheck_1342_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v___x_1256_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1342_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
uint8_t v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = 2;
v___x_1280_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1265_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v_keyedConfig_1281_; uint8_t v_trackZetaDelta_1282_; lean_object* v_zetaDeltaSet_1283_; lean_object* v_lctx_1284_; lean_object* v_localInstances_1285_; lean_object* v_defEqCtx_x3f_1286_; lean_object* v_synthPendingDepth_1287_; lean_object* v_customCanUnfoldPredicate_x3f_1288_; uint8_t v_univApprox_1289_; uint8_t v_inTypeClassResolution_1290_; uint8_t v_cacheInferType_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v_foApprox_1295_; uint8_t v_ctxApprox_1296_; uint8_t v_quasiPatternApprox_1297_; uint8_t v_constApprox_1298_; uint8_t v_isDefEqStuckEx_1299_; uint8_t v_unificationHints_1300_; uint8_t v_proofIrrelevance_1301_; uint8_t v_offsetCnstrs_1302_; uint8_t v_transparency_1303_; uint8_t v_etaStruct_1304_; uint8_t v_univApprox_1305_; uint8_t v_iota_1306_; uint8_t v_beta_1307_; uint8_t v_proj_1308_; uint8_t v_zeta_1309_; uint8_t v_zetaDelta_1310_; uint8_t v_zetaUnused_1311_; uint8_t v_zetaHave_1312_; uint8_t v_canUnfoldPredicateConfig_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1277_);
v_keyedConfig_1281_ = lean_ctor_get(v___y_1124_, 0);
v_trackZetaDelta_1282_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7);
v_zetaDeltaSet_1283_ = lean_ctor_get(v___y_1124_, 1);
v_lctx_1284_ = lean_ctor_get(v___y_1124_, 2);
v_localInstances_1285_ = lean_ctor_get(v___y_1124_, 3);
v_defEqCtx_x3f_1286_ = lean_ctor_get(v___y_1124_, 4);
v_synthPendingDepth_1287_ = lean_ctor_get(v___y_1124_, 5);
v_customCanUnfoldPredicate_x3f_1288_ = lean_ctor_get(v___y_1124_, 6);
v_univApprox_1289_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1290_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 2);
v_cacheInferType_1291_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1281_);
v___x_1292_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1279_, v_keyedConfig_1281_);
lean_inc(v_customCanUnfoldPredicate_x3f_1288_);
lean_inc(v_synthPendingDepth_1287_);
lean_inc(v_defEqCtx_x3f_1286_);
lean_inc_ref(v_localInstances_1285_);
lean_inc_ref(v_lctx_1284_);
lean_inc(v_zetaDeltaSet_1283_);
v___x_1293_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v_zetaDeltaSet_1283_);
lean_ctor_set(v___x_1293_, 2, v_lctx_1284_);
lean_ctor_set(v___x_1293_, 3, v_localInstances_1285_);
lean_ctor_set(v___x_1293_, 4, v_defEqCtx_x3f_1286_);
lean_ctor_set(v___x_1293_, 5, v_synthPendingDepth_1287_);
lean_ctor_set(v___x_1293_, 6, v_customCanUnfoldPredicate_x3f_1288_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*7, v_trackZetaDelta_1282_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*7 + 1, v_univApprox_1289_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1290_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*7 + 3, v_cacheInferType_1291_);
v___x_1294_ = l_Lean_Meta_Context_config(v___x_1293_);
lean_dec_ref_known(v___x_1293_, 7);
v_foApprox_1295_ = lean_ctor_get_uint8(v___x_1294_, 0);
v_ctxApprox_1296_ = lean_ctor_get_uint8(v___x_1294_, 1);
v_quasiPatternApprox_1297_ = lean_ctor_get_uint8(v___x_1294_, 2);
v_constApprox_1298_ = lean_ctor_get_uint8(v___x_1294_, 3);
v_isDefEqStuckEx_1299_ = lean_ctor_get_uint8(v___x_1294_, 4);
v_unificationHints_1300_ = lean_ctor_get_uint8(v___x_1294_, 5);
v_proofIrrelevance_1301_ = lean_ctor_get_uint8(v___x_1294_, 6);
v_offsetCnstrs_1302_ = lean_ctor_get_uint8(v___x_1294_, 8);
v_transparency_1303_ = lean_ctor_get_uint8(v___x_1294_, 9);
v_etaStruct_1304_ = lean_ctor_get_uint8(v___x_1294_, 10);
v_univApprox_1305_ = lean_ctor_get_uint8(v___x_1294_, 11);
v_iota_1306_ = lean_ctor_get_uint8(v___x_1294_, 12);
v_beta_1307_ = lean_ctor_get_uint8(v___x_1294_, 13);
v_proj_1308_ = lean_ctor_get_uint8(v___x_1294_, 14);
v_zeta_1309_ = lean_ctor_get_uint8(v___x_1294_, 15);
v_zetaDelta_1310_ = lean_ctor_get_uint8(v___x_1294_, 16);
v_zetaUnused_1311_ = lean_ctor_get_uint8(v___x_1294_, 17);
v_zetaHave_1312_ = lean_ctor_get_uint8(v___x_1294_, 18);
v_canUnfoldPredicateConfig_1313_ = lean_ctor_get_uint8(v___x_1294_, 19);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1315_ = v___x_1294_;
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
else
{
lean_dec(v___x_1294_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1324_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 0, v_foApprox_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 1, v_ctxApprox_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 2, v_quasiPatternApprox_1297_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 3, v_constApprox_1298_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 4, v_isDefEqStuckEx_1299_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 5, v_unificationHints_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 6, v_proofIrrelevance_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 8, v_offsetCnstrs_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 9, v_transparency_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 10, v_etaStruct_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 11, v_univApprox_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 12, v_iota_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 13, v_beta_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 14, v_proj_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 15, v_zeta_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 16, v_zetaDelta_1310_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 17, v_zetaUnused_1311_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 18, v_zetaHave_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, 19, v_canUnfoldPredicateConfig_1313_);
v___x_1318_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
uint64_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_ctor_set_uint8(v___x_1318_, 7, v___x_1119_);
v___x_1319_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set_uint64(v___x_1320_, sizeof(void*)*1, v___x_1319_);
lean_inc(v_customCanUnfoldPredicate_x3f_1288_);
lean_inc(v_synthPendingDepth_1287_);
lean_inc(v_defEqCtx_x3f_1286_);
lean_inc_ref(v_localInstances_1285_);
lean_inc_ref(v_lctx_1284_);
lean_inc(v_zetaDeltaSet_1283_);
v___x_1321_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v_zetaDeltaSet_1283_);
lean_ctor_set(v___x_1321_, 2, v_lctx_1284_);
lean_ctor_set(v___x_1321_, 3, v_localInstances_1285_);
lean_ctor_set(v___x_1321_, 4, v_defEqCtx_x3f_1286_);
lean_ctor_set(v___x_1321_, 5, v_synthPendingDepth_1287_);
lean_ctor_set(v___x_1321_, 6, v_customCanUnfoldPredicate_x3f_1288_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*7, v_trackZetaDelta_1282_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*7 + 1, v_univApprox_1289_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1290_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*7 + 3, v_cacheInferType_1291_);
lean_inc(v_a_1173_);
lean_inc(v_a_1130_);
v___x_1322_ = l_Lean_Meta_isExprDefEq(v_a_1130_, v_a_1173_, v___x_1321_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec_ref_known(v___x_1321_, 7);
v___y_1194_ = v___x_1322_;
goto v___jp_1193_;
}
}
}
else
{
uint8_t v_trackZetaDelta_1325_; lean_object* v_zetaDeltaSet_1326_; lean_object* v_lctx_1327_; lean_object* v_localInstances_1328_; lean_object* v_defEqCtx_x3f_1329_; lean_object* v_synthPendingDepth_1330_; lean_object* v_customCanUnfoldPredicate_x3f_1331_; uint8_t v_univApprox_1332_; uint8_t v_inTypeClassResolution_1333_; uint8_t v_cacheInferType_1334_; lean_object* v___x_1336_; 
v_trackZetaDelta_1325_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7);
v_zetaDeltaSet_1326_ = lean_ctor_get(v___y_1124_, 1);
v_lctx_1327_ = lean_ctor_get(v___y_1124_, 2);
v_localInstances_1328_ = lean_ctor_get(v___y_1124_, 3);
v_defEqCtx_x3f_1329_ = lean_ctor_get(v___y_1124_, 4);
v_synthPendingDepth_1330_ = lean_ctor_get(v___y_1124_, 5);
v_customCanUnfoldPredicate_x3f_1331_ = lean_ctor_get(v___y_1124_, 6);
v_univApprox_1332_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1333_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 2);
v_cacheInferType_1334_ = lean_ctor_get_uint8(v___y_1124_, sizeof(void*)*7 + 3);
if (v_isShared_1278_ == 0)
{
v___x_1336_ = v___x_1277_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 0, v_foApprox_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 1, v_ctxApprox_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 2, v_quasiPatternApprox_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 3, v_constApprox_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 4, v_isDefEqStuckEx_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 5, v_unificationHints_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 6, v_proofIrrelevance_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 8, v_offsetCnstrs_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 9, v_transparency_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 10, v_etaStruct_1266_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 11, v_univApprox_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 12, v_iota_1268_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 13, v_beta_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 14, v_proj_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 15, v_zeta_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 16, v_zetaDelta_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 17, v_zetaUnused_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 18, v_zetaHave_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, 19, v_canUnfoldPredicateConfig_1275_);
v___x_1336_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
uint64_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_ctor_set_uint8(v___x_1336_, 7, v___x_1119_);
v___x_1337_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set_uint64(v___x_1338_, sizeof(void*)*1, v___x_1337_);
lean_inc(v_customCanUnfoldPredicate_x3f_1331_);
lean_inc(v_synthPendingDepth_1330_);
lean_inc(v_defEqCtx_x3f_1329_);
lean_inc_ref(v_localInstances_1328_);
lean_inc_ref(v_lctx_1327_);
lean_inc(v_zetaDeltaSet_1326_);
v___x_1339_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v_zetaDeltaSet_1326_);
lean_ctor_set(v___x_1339_, 2, v_lctx_1327_);
lean_ctor_set(v___x_1339_, 3, v_localInstances_1328_);
lean_ctor_set(v___x_1339_, 4, v_defEqCtx_x3f_1329_);
lean_ctor_set(v___x_1339_, 5, v_synthPendingDepth_1330_);
lean_ctor_set(v___x_1339_, 6, v_customCanUnfoldPredicate_x3f_1331_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7, v_trackZetaDelta_1325_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7 + 1, v_univApprox_1332_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1333_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*7 + 3, v_cacheInferType_1334_);
lean_inc(v_a_1173_);
lean_inc(v_a_1130_);
v___x_1340_ = l_Lean_Meta_isExprDefEq(v_a_1130_, v_a_1173_, v___x_1339_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec_ref_known(v___x_1339_, 7);
v___y_1194_ = v___x_1340_;
goto v___jp_1193_;
}
}
}
}
v___jp_1174_:
{
if (v_____do__lift_1175_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1184_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1);
lean_inc_ref(v_a_1113_);
v___x_1185_ = l_Lean_indentExpr(v_a_1113_);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 1);
lean_ctor_set(v___x_1170_, 0, v___x_1188_);
v___x_1190_ = v___x_1170_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; 
lean_inc(v_a_1134_);
v___x_1191_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1190_, v_a_1130_, v_a_1173_, v_a_1134_, v___x_1117_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec_ref(v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_dec_ref_known(v___x_1191_, 1);
v___y_1136_ = v___y_1176_;
v___y_1137_ = v___y_1177_;
v___y_1138_ = v___y_1178_;
v___y_1139_ = v___y_1179_;
v___y_1140_ = v___y_1180_;
v___y_1141_ = v___y_1181_;
v___y_1142_ = v___y_1182_;
v___y_1143_ = v___y_1183_;
goto v___jp_1135_;
}
else
{
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1110_);
return v___x_1191_;
}
}
}
else
{
lean_dec(v_a_1173_);
lean_del_object(v___x_1170_);
lean_dec(v_a_1130_);
lean_dec(v___x_1117_);
v___y_1136_ = v___y_1176_;
v___y_1137_ = v___y_1177_;
v___y_1138_ = v___y_1178_;
v___y_1139_ = v___y_1179_;
v___y_1140_ = v___y_1180_;
v___y_1141_ = v___y_1181_;
v___y_1142_ = v___y_1182_;
v___y_1143_ = v___y_1183_;
goto v___jp_1135_;
}
}
v___jp_1193_:
{
if (lean_obj_tag(v___y_1194_) == 0)
{
lean_object* v_a_1195_; uint8_t v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___y_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___y_1194_, 1);
v___x_1196_ = lean_unbox(v_a_1195_);
lean_dec(v_a_1195_);
v_____do__lift_1175_ = v___x_1196_;
v___y_1176_ = v___y_1120_;
v___y_1177_ = v___y_1121_;
v___y_1178_ = v___y_1122_;
v___y_1179_ = v___y_1123_;
v___y_1180_ = v___y_1124_;
v___y_1181_ = v___y_1125_;
v___y_1182_ = v___y_1126_;
v___y_1183_ = v___y_1127_;
goto v___jp_1174_;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_a_1173_);
lean_del_object(v___x_1170_);
lean_dec(v_a_1134_);
lean_dec(v_a_1130_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___x_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1110_);
v_a_1197_ = lean_ctor_get(v___y_1194_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___y_1194_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___y_1194_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___y_1194_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_del_object(v___x_1170_);
lean_dec(v_a_1134_);
lean_dec(v_a_1130_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___x_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1110_);
v_a_1343_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1172_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1172_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
else
{
lean_dec(v_a_1134_);
lean_dec(v_a_1130_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___x_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1110_);
return v___x_1168_;
}
v___jp_1135_:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Meta_getMVars(v_a_1113_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1145_, v_mvarCounter_1114_, v___y_1141_);
lean_dec(v_a_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1147_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v_a_1147_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1149_; 
lean_dec_ref_known(v___x_1148_, 1);
v___x_1149_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_1110_, v___y_1137_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1149_, 1);
v___x_1150_ = l_Lean_Name_mkStr1(v___x_1115_);
v___x_1151_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1150_, v_a_1134_, v___x_1116_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v___x_1151_;
}
else
{
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1115_);
return v___x_1149_;
}
}
else
{
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1110_);
return v___x_1148_;
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1110_);
v_a_1152_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1146_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1146_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_a_1134_);
lean_dec_ref(v___x_1115_);
lean_dec(v_a_1110_);
v_a_1160_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1144_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1144_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_a_1130_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___x_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1110_);
v_a_1353_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1133_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1133_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___x_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1111_);
lean_dec(v_a_1110_);
v_a_1361_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1129_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1129_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1110_ = stack[0].m_obj;
lean_object* v_a_1111_ = stack[1].m_obj;
uint8_t v___x_1112_ = stack[2].m_num;
lean_object* v_a_1113_ = stack[3].m_obj;
lean_object* v_mvarCounter_1114_ = stack[4].m_obj;
lean_object* v___x_1115_ = stack[5].m_obj;
uint8_t v___x_1116_ = stack[6].m_num;
lean_object* v___x_1117_ = stack[7].m_obj;
uint8_t v_useReducible_1118_ = stack[8].m_num;
uint8_t v___x_1119_ = stack[9].m_num;
lean_object* v___y_1120_ = stack[10].m_obj;
lean_object* v___y_1121_ = stack[11].m_obj;
lean_object* v___y_1122_ = stack[12].m_obj;
lean_object* v___y_1123_ = stack[13].m_obj;
lean_object* v___y_1124_ = stack[14].m_obj;
lean_object* v___y_1125_ = stack[15].m_obj;
lean_object* v___y_1126_ = stack[16].m_obj;
lean_object* v___y_1127_ = stack[17].m_obj;
lean_object* v_res_1369_;
v_res_1369_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1110_, v_a_1111_, v___x_1112_, v_a_1113_, v_mvarCounter_1114_, v___x_1115_, v___x_1116_, v___x_1117_, v_useReducible_1118_, v___x_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1369_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object** _args){
lean_object* v_a_1370_ = _args[0];
lean_object* v_a_1371_ = _args[1];
lean_object* v___x_1372_ = _args[2];
lean_object* v_a_1373_ = _args[3];
lean_object* v_mvarCounter_1374_ = _args[4];
lean_object* v___x_1375_ = _args[5];
lean_object* v___x_1376_ = _args[6];
lean_object* v___x_1377_ = _args[7];
lean_object* v_useReducible_1378_ = _args[8];
lean_object* v___x_1379_ = _args[9];
lean_object* v___y_1380_ = _args[10];
lean_object* v___y_1381_ = _args[11];
lean_object* v___y_1382_ = _args[12];
lean_object* v___y_1383_ = _args[13];
lean_object* v___y_1384_ = _args[14];
lean_object* v___y_1385_ = _args[15];
lean_object* v___y_1386_ = _args[16];
lean_object* v___y_1387_ = _args[17];
lean_object* v___y_1388_ = _args[18];
_start:
{
uint8_t v___x_94502__boxed_1389_; uint8_t v___x_94505__boxed_1390_; uint8_t v_useReducible_boxed_1391_; uint8_t v___x_94507__boxed_1392_; lean_object* v_res_1393_; 
v___x_94502__boxed_1389_ = lean_unbox(v___x_1372_);
v___x_94505__boxed_1390_ = lean_unbox(v___x_1376_);
v_useReducible_boxed_1391_ = lean_unbox(v_useReducible_1378_);
v___x_94507__boxed_1392_ = lean_unbox(v___x_1379_);
v_res_1393_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1370_, v_a_1371_, v___x_94502__boxed_1389_, v_a_1373_, v_mvarCounter_1374_, v___x_1375_, v___x_94505__boxed_1390_, v___x_1377_, v_useReducible_boxed_1391_, v___x_94507__boxed_1392_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v_mvarCounter_1374_);
return v_res_1393_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_infoState_1405_; lean_object* v_env_1406_; lean_object* v_nextMacroScope_1407_; lean_object* v_ngen_1408_; lean_object* v_auxDeclNGen_1409_; lean_object* v_traceState_1410_; lean_object* v_cache_1411_; lean_object* v_recordedDeps_1412_; lean_object* v_messages_1413_; lean_object* v_snapshotTasks_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1435_; 
v___x_1404_ = lean_st_ref_take(v___y_1402_);
v_infoState_1405_ = lean_ctor_get(v___x_1404_, 8);
v_env_1406_ = lean_ctor_get(v___x_1404_, 0);
v_nextMacroScope_1407_ = lean_ctor_get(v___x_1404_, 1);
v_ngen_1408_ = lean_ctor_get(v___x_1404_, 2);
v_auxDeclNGen_1409_ = lean_ctor_get(v___x_1404_, 3);
v_traceState_1410_ = lean_ctor_get(v___x_1404_, 4);
v_cache_1411_ = lean_ctor_get(v___x_1404_, 5);
v_recordedDeps_1412_ = lean_ctor_get(v___x_1404_, 6);
v_messages_1413_ = lean_ctor_get(v___x_1404_, 7);
v_snapshotTasks_1414_ = lean_ctor_get(v___x_1404_, 9);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1416_ = v___x_1404_;
v_isShared_1417_ = v_isSharedCheck_1435_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_snapshotTasks_1414_);
lean_inc(v_infoState_1405_);
lean_inc(v_messages_1413_);
lean_inc(v_recordedDeps_1412_);
lean_inc(v_cache_1411_);
lean_inc(v_traceState_1410_);
lean_inc(v_auxDeclNGen_1409_);
lean_inc(v_ngen_1408_);
lean_inc(v_nextMacroScope_1407_);
lean_inc(v_env_1406_);
lean_dec(v___x_1404_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1435_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
uint8_t v_enabled_1418_; lean_object* v_assignment_1419_; lean_object* v_lazyAssignment_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1433_; 
v_enabled_1418_ = lean_ctor_get_uint8(v_infoState_1405_, sizeof(void*)*3);
v_assignment_1419_ = lean_ctor_get(v_infoState_1405_, 0);
v_lazyAssignment_1420_ = lean_ctor_get(v_infoState_1405_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_infoState_1405_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_infoState_1405_, 2);
lean_dec(v_unused_1434_);
v___x_1422_ = v_infoState_1405_;
v_isShared_1423_ = v_isSharedCheck_1433_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_lazyAssignment_1420_);
lean_inc(v_assignment_1419_);
lean_dec(v_infoState_1405_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1433_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_box(0);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 2, v_a_1394_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_assignment_1419_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_lazyAssignment_1420_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_a_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1432_, sizeof(void*)*3, v_enabled_1418_);
v___x_1426_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1428_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 8, v___x_1426_);
v___x_1428_ = v___x_1416_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_env_1406_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_nextMacroScope_1407_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_ngen_1408_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_auxDeclNGen_1409_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_traceState_1410_);
lean_ctor_set(v_reuseFailAlloc_1431_, 5, v_cache_1411_);
lean_ctor_set(v_reuseFailAlloc_1431_, 6, v_recordedDeps_1412_);
lean_ctor_set(v_reuseFailAlloc_1431_, 7, v_messages_1413_);
lean_ctor_set(v_reuseFailAlloc_1431_, 8, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1431_, 9, v_snapshotTasks_1414_);
v___x_1428_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_st_ref_put(v___y_1402_, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1424_);
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1394_ = stack[0].m_obj;
lean_object* v___y_1395_ = stack[1].m_obj;
lean_object* v___y_1396_ = stack[2].m_obj;
lean_object* v___y_1397_ = stack[3].m_obj;
lean_object* v___y_1398_ = stack[4].m_obj;
lean_object* v___y_1399_ = stack[5].m_obj;
lean_object* v___y_1400_ = stack[6].m_obj;
lean_object* v___y_1401_ = stack[7].m_obj;
lean_object* v___y_1402_ = stack[8].m_obj;
lean_object* v_res_1436_;
v_res_1436_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
stack->m_obj
 = v_res_1436_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1447_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1448_, lean_object* v_mkInfoTree_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v_a_1457_, lean_object* v_a_x3f_1458_){
_start:
{
lean_object* v___x_1460_; lean_object* v_infoState_1461_; lean_object* v_trees_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_st_ref_get(v___y_1448_);
v_infoState_1461_ = lean_ctor_get(v___x_1460_, 8);
lean_inc_ref(v_infoState_1461_);
lean_dec(v___x_1460_);
v_trees_1462_ = lean_ctor_get(v_infoState_1461_, 2);
lean_inc_ref(v_trees_1462_);
lean_dec_ref(v_infoState_1461_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
v___x_1463_ = lean_apply_10(v_mkInfoTree_1449_, v_trees_1462_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1448_, lean_box(0));
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1503_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1503_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1503_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v_infoState_1469_; lean_object* v_env_1470_; lean_object* v_nextMacroScope_1471_; lean_object* v_ngen_1472_; lean_object* v_auxDeclNGen_1473_; lean_object* v_traceState_1474_; lean_object* v_cache_1475_; lean_object* v_recordedDeps_1476_; lean_object* v_messages_1477_; lean_object* v_snapshotTasks_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1502_; 
v___x_1468_ = lean_st_ref_take(v___y_1448_);
v_infoState_1469_ = lean_ctor_get(v___x_1468_, 8);
v_env_1470_ = lean_ctor_get(v___x_1468_, 0);
v_nextMacroScope_1471_ = lean_ctor_get(v___x_1468_, 1);
v_ngen_1472_ = lean_ctor_get(v___x_1468_, 2);
v_auxDeclNGen_1473_ = lean_ctor_get(v___x_1468_, 3);
v_traceState_1474_ = lean_ctor_get(v___x_1468_, 4);
v_cache_1475_ = lean_ctor_get(v___x_1468_, 5);
v_recordedDeps_1476_ = lean_ctor_get(v___x_1468_, 6);
v_messages_1477_ = lean_ctor_get(v___x_1468_, 7);
v_snapshotTasks_1478_ = lean_ctor_get(v___x_1468_, 9);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1480_ = v___x_1468_;
v_isShared_1481_ = v_isSharedCheck_1502_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snapshotTasks_1478_);
lean_inc(v_infoState_1469_);
lean_inc(v_messages_1477_);
lean_inc(v_recordedDeps_1476_);
lean_inc(v_cache_1475_);
lean_inc(v_traceState_1474_);
lean_inc(v_auxDeclNGen_1473_);
lean_inc(v_ngen_1472_);
lean_inc(v_nextMacroScope_1471_);
lean_inc(v_env_1470_);
lean_dec(v___x_1468_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1502_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v_enabled_1482_; lean_object* v_assignment_1483_; lean_object* v_lazyAssignment_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1500_; 
v_enabled_1482_ = lean_ctor_get_uint8(v_infoState_1469_, sizeof(void*)*3);
v_assignment_1483_ = lean_ctor_get(v_infoState_1469_, 0);
v_lazyAssignment_1484_ = lean_ctor_get(v_infoState_1469_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_infoState_1469_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_infoState_1469_, 2);
lean_dec(v_unused_1501_);
v___x_1486_ = v_infoState_1469_;
v_isShared_1487_ = v_isSharedCheck_1500_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_lazyAssignment_1484_);
lean_inc(v_assignment_1483_);
lean_dec(v_infoState_1469_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1500_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Lean_PersistentArray_push___redArg(v_a_1457_, v_a_1464_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 2, v___x_1489_);
v___x_1491_ = v___x_1486_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_assignment_1483_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_lazyAssignment_1484_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v___x_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1499_, sizeof(void*)*3, v_enabled_1482_);
v___x_1491_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 8, v___x_1491_);
v___x_1493_ = v___x_1480_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_env_1470_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_nextMacroScope_1471_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_ngen_1472_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_auxDeclNGen_1473_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_traceState_1474_);
lean_ctor_set(v_reuseFailAlloc_1498_, 5, v_cache_1475_);
lean_ctor_set(v_reuseFailAlloc_1498_, 6, v_recordedDeps_1476_);
lean_ctor_set(v_reuseFailAlloc_1498_, 7, v_messages_1477_);
lean_ctor_set(v_reuseFailAlloc_1498_, 8, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1498_, 9, v_snapshotTasks_1478_);
v___x_1493_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_st_ref_put(v___y_1448_, v___x_1493_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1488_);
v___x_1496_ = v___x_1466_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1488_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v_a_1457_);
v_a_1504_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1463_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1463_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1448_ = stack[0].m_obj;
lean_object* v_mkInfoTree_1449_ = stack[1].m_obj;
lean_object* v___y_1450_ = stack[2].m_obj;
lean_object* v___y_1451_ = stack[3].m_obj;
lean_object* v___y_1452_ = stack[4].m_obj;
lean_object* v___y_1453_ = stack[5].m_obj;
lean_object* v___y_1454_ = stack[6].m_obj;
lean_object* v___y_1455_ = stack[7].m_obj;
lean_object* v___y_1456_ = stack[8].m_obj;
lean_object* v_a_1457_ = stack[9].m_obj;
lean_object* v_a_x3f_1458_ = stack[10].m_obj;
lean_object* v_res_1512_;
v_res_1512_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1448_, v_mkInfoTree_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v_a_1457_, v_a_x3f_1458_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1513_, lean_object* v_mkInfoTree_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v_a_1522_, lean_object* v_a_x3f_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1513_, v_mkInfoTree_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v_a_1522_, v_a_x3f_1523_);
lean_dec(v_a_x3f_1523_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1513_);
return v_res_1525_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1526_, lean_object* v_mkInfoTree_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v_infoState_1538_; uint8_t v_enabled_1539_; 
v___x_1537_ = lean_st_ref_get(v___y_1535_);
v_infoState_1538_ = lean_ctor_get(v___x_1537_, 8);
lean_inc_ref(v_infoState_1538_);
lean_dec(v___x_1537_);
v_enabled_1539_ = lean_ctor_get_uint8(v_infoState_1538_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1538_);
if (v_enabled_1539_ == 0)
{
lean_object* v___x_1540_; 
lean_dec_ref(v_mkInfoTree_1527_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
v___x_1540_ = lean_apply_9(v_x_1526_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, lean_box(0));
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v_a_1542_; lean_object* v_r_1543_; 
v___x_1541_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1535_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
lean_inc(v___y_1535_);
lean_inc_ref(v___y_1534_);
lean_inc(v___y_1533_);
lean_inc_ref(v___y_1532_);
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
v_r_1543_ = lean_apply_9(v_x_1526_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, lean_box(0));
if (lean_obj_tag(v_r_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1568_; 
v_a_1544_ = lean_ctor_get(v_r_1543_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_r_1543_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1546_ = v_r_1543_;
v_isShared_1547_ = v_isSharedCheck_1568_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v_r_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1568_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
lean_inc(v_a_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1535_, v_mkInfoTree_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v_a_1542_, v___x_1549_);
lean_dec_ref(v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v___x_1550_, 0);
lean_dec(v_unused_1558_);
v___x_1552_ = v___x_1550_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v___x_1550_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_a_1544_);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1544_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1544_);
v_a_1559_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1550_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1550_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v_r_1543_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v_r_1543_, 1);
v___x_1570_ = lean_box(0);
v___x_1571_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1535_, v_mkInfoTree_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v_a_1542_, v___x_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v___x_1571_, 0);
lean_dec(v_unused_1579_);
v___x_1573_ = v___x_1571_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v___x_1571_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 1);
lean_ctor_set(v___x_1573_, 0, v_a_1569_);
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1569_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1569_);
v_a_1580_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1571_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1571_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1526_ = stack[0].m_obj;
lean_object* v_mkInfoTree_1527_ = stack[1].m_obj;
lean_object* v___y_1528_ = stack[2].m_obj;
lean_object* v___y_1529_ = stack[3].m_obj;
lean_object* v___y_1530_ = stack[4].m_obj;
lean_object* v___y_1531_ = stack[5].m_obj;
lean_object* v___y_1532_ = stack[6].m_obj;
lean_object* v___y_1533_ = stack[7].m_obj;
lean_object* v___y_1534_ = stack[8].m_obj;
lean_object* v___y_1535_ = stack[9].m_obj;
lean_object* v_res_1588_;
v_res_1588_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1526_, v_mkInfoTree_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
stack->m_obj
 = v_res_1588_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1589_, lean_object* v_mkInfoTree_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1589_, v_mkInfoTree_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
return v_res_1600_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_ref_1607_; lean_object* v___x_1608_; lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1617_; 
v_ref_1607_ = lean_ctor_get(v___y_1604_, 2);
v___x_1608_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_inc(v_ref_1607_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_ref_1607_);
lean_ctor_set(v___x_1613_, 1, v_a_1609_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 1);
lean_ctor_set(v___x_1611_, 0, v___x_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1601_ = stack[0].m_obj;
lean_object* v___y_1602_ = stack[1].m_obj;
lean_object* v___y_1603_ = stack[2].m_obj;
lean_object* v___y_1604_ = stack[3].m_obj;
lean_object* v___y_1605_ = stack[4].m_obj;
lean_object* v_res_1618_;
v_res_1618_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
stack->m_obj
 = v_res_1618_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1625_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(lean_object* v_a_1626_, lean_object* v_x_1627_){
_start:
{
if (lean_obj_tag(v_x_1627_) == 0)
{
uint8_t v___x_1628_; 
v___x_1628_ = 0;
return v___x_1628_;
}
else
{
lean_object* v_key_1629_; lean_object* v_tail_1630_; uint8_t v___x_1631_; 
v_key_1629_ = lean_ctor_get(v_x_1627_, 0);
v_tail_1630_ = lean_ctor_get(v_x_1627_, 2);
v___x_1631_ = lean_expr_eqv(v_key_1629_, v_a_1626_);
if (v___x_1631_ == 0)
{
v_x_1627_ = v_tail_1630_;
goto _start;
}
else
{
return v___x_1631_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1626_ = stack[0].m_obj;
lean_object* v_x_1627_ = stack[1].m_obj;
uint8_t v_res_1633_;
v_res_1633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1626_, v_x_1627_);
stack->m_num = v_res_1633_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_a_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_res_1636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1634_, v_x_1635_);
lean_dec(v_x_1635_);
lean_dec_ref(v_a_1634_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
return v_x_1638_;
}
else
{
lean_object* v_key_1640_; lean_object* v_value_1641_; lean_object* v_tail_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1665_; 
v_key_1640_ = lean_ctor_get(v_x_1639_, 0);
v_value_1641_ = lean_ctor_get(v_x_1639_, 1);
v_tail_1642_ = lean_ctor_get(v_x_1639_, 2);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_x_1639_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1644_ = v_x_1639_;
v_isShared_1645_ = v_isSharedCheck_1665_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_tail_1642_);
lean_inc(v_value_1641_);
lean_inc(v_key_1640_);
lean_dec(v_x_1639_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1665_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; uint64_t v___x_1647_; uint64_t v___x_1648_; uint64_t v___x_1649_; uint64_t v_fold_1650_; uint64_t v___x_1651_; uint64_t v___x_1652_; uint64_t v___x_1653_; size_t v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; size_t v___x_1657_; size_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1646_ = lean_array_get_size(v_x_1638_);
v___x_1647_ = l_Lean_Expr_hash(v_key_1640_);
v___x_1648_ = 32ULL;
v___x_1649_ = lean_uint64_shift_right(v___x_1647_, v___x_1648_);
v_fold_1650_ = lean_uint64_xor(v___x_1647_, v___x_1649_);
v___x_1651_ = 16ULL;
v___x_1652_ = lean_uint64_shift_right(v_fold_1650_, v___x_1651_);
v___x_1653_ = lean_uint64_xor(v_fold_1650_, v___x_1652_);
v___x_1654_ = lean_uint64_to_usize(v___x_1653_);
v___x_1655_ = lean_usize_of_nat(v___x_1646_);
v___x_1656_ = ((size_t)1ULL);
v___x_1657_ = lean_usize_sub(v___x_1655_, v___x_1656_);
v___x_1658_ = lean_usize_land(v___x_1654_, v___x_1657_);
v___x_1659_ = lean_array_uget_borrowed(v_x_1638_, v___x_1658_);
lean_inc(v___x_1659_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 2, v___x_1659_);
v___x_1661_ = v___x_1644_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_key_1640_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_value_1641_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_array_uset(v_x_1638_, v___x_1658_, v___x_1661_);
v_x_1638_ = v___x_1662_;
v_x_1639_ = v_tail_1642_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(lean_object* v_i_1666_, lean_object* v_source_1667_, lean_object* v_target_1668_){
_start:
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = lean_array_get_size(v_source_1667_);
v___x_1670_ = lean_nat_dec_lt(v_i_1666_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_dec_ref(v_source_1667_);
lean_dec(v_i_1666_);
return v_target_1668_;
}
else
{
lean_object* v_es_1671_; lean_object* v___x_1672_; lean_object* v_source_1673_; lean_object* v_target_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_es_1671_ = lean_array_fget(v_source_1667_, v_i_1666_);
v___x_1672_ = lean_box(0);
v_source_1673_ = lean_array_fset(v_source_1667_, v_i_1666_, v___x_1672_);
v_target_1674_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_target_1668_, v_es_1671_);
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = lean_nat_add(v_i_1666_, v___x_1675_);
lean_dec(v_i_1666_);
v_i_1666_ = v___x_1676_;
v_source_1667_ = v_source_1673_;
v_target_1668_ = v_target_1674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(lean_object* v_data_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_nbuckets_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1679_ = lean_array_get_size(v_data_1678_);
v___x_1680_ = lean_unsigned_to_nat(2u);
v_nbuckets_1681_ = lean_nat_mul(v___x_1679_, v___x_1680_);
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_mk_array(v_nbuckets_1681_, v___x_1683_);
v___x_1685_ = lean_array_propagate_mark(v_data_1678_, v___x_1684_);
v___x_1686_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v___x_1682_, v_data_1678_, v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(lean_object* v_m_1687_, lean_object* v_a_1688_, lean_object* v_b_1689_){
_start:
{
lean_object* v_size_1690_; lean_object* v_buckets_1691_; lean_object* v___x_1692_; uint64_t v___x_1693_; uint64_t v___x_1694_; uint64_t v___x_1695_; uint64_t v_fold_1696_; uint64_t v___x_1697_; uint64_t v___x_1698_; uint64_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v_bkt_1705_; uint8_t v___x_1706_; 
v_size_1690_ = lean_ctor_get(v_m_1687_, 0);
v_buckets_1691_ = lean_ctor_get(v_m_1687_, 1);
v___x_1692_ = lean_array_get_size(v_buckets_1691_);
v___x_1693_ = l_Lean_Expr_hash(v_a_1688_);
v___x_1694_ = 32ULL;
v___x_1695_ = lean_uint64_shift_right(v___x_1693_, v___x_1694_);
v_fold_1696_ = lean_uint64_xor(v___x_1693_, v___x_1695_);
v___x_1697_ = 16ULL;
v___x_1698_ = lean_uint64_shift_right(v_fold_1696_, v___x_1697_);
v___x_1699_ = lean_uint64_xor(v_fold_1696_, v___x_1698_);
v___x_1700_ = lean_uint64_to_usize(v___x_1699_);
v___x_1701_ = lean_usize_of_nat(v___x_1692_);
v___x_1702_ = ((size_t)1ULL);
v___x_1703_ = lean_usize_sub(v___x_1701_, v___x_1702_);
v___x_1704_ = lean_usize_land(v___x_1700_, v___x_1703_);
v_bkt_1705_ = lean_array_uget_borrowed(v_buckets_1691_, v___x_1704_);
v___x_1706_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1688_, v_bkt_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1727_; 
lean_inc_ref(v_buckets_1691_);
lean_inc(v_size_1690_);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_m_1687_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; lean_object* v_unused_1729_; 
v_unused_1728_ = lean_ctor_get(v_m_1687_, 1);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_m_1687_, 0);
lean_dec(v_unused_1729_);
v___x_1708_ = v_m_1687_;
v_isShared_1709_ = v_isSharedCheck_1727_;
goto v_resetjp_1707_;
}
else
{
lean_dec(v_m_1687_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1727_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v_size_x27_1711_; lean_object* v___x_1712_; lean_object* v_buckets_x27_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1710_ = lean_unsigned_to_nat(1u);
v_size_x27_1711_ = lean_nat_add(v_size_1690_, v___x_1710_);
lean_dec(v_size_1690_);
lean_inc(v_bkt_1705_);
v___x_1712_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1712_, 0, v_a_1688_);
lean_ctor_set(v___x_1712_, 1, v_b_1689_);
lean_ctor_set(v___x_1712_, 2, v_bkt_1705_);
v_buckets_x27_1713_ = lean_array_uset(v_buckets_1691_, v___x_1704_, v___x_1712_);
v___x_1714_ = lean_unsigned_to_nat(4u);
v___x_1715_ = lean_nat_mul(v_size_x27_1711_, v___x_1714_);
v___x_1716_ = lean_unsigned_to_nat(3u);
v___x_1717_ = lean_nat_div(v___x_1715_, v___x_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_array_get_size(v_buckets_x27_1713_);
v___x_1719_ = lean_nat_dec_le(v___x_1717_, v___x_1718_);
lean_dec(v___x_1717_);
if (v___x_1719_ == 0)
{
lean_object* v_val_1720_; lean_object* v___x_1722_; 
v_val_1720_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_buckets_x27_1713_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v_val_1720_);
lean_ctor_set(v___x_1708_, 0, v_size_x27_1711_);
v___x_1722_ = v___x_1708_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_size_x27_1711_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_val_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
else
{
lean_object* v___x_1725_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v_buckets_x27_1713_);
lean_ctor_set(v___x_1708_, 0, v_size_x27_1711_);
v___x_1725_ = v___x_1708_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_size_x27_1711_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_buckets_x27_1713_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_dec(v_b_1689_);
lean_dec_ref(v_a_1688_);
return v_m_1687_;
}
}
}
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(lean_object* v_mvarId_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v_mctx_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1734_ = lean_st_ref_get(v___y_1732_);
v_mctx_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc_ref(v_mctx_1735_);
lean_dec(v___x_1734_);
v___x_1736_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1735_, v_mvarId_1730_);
lean_dec_ref(v_mctx_1735_);
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___y_1731_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1730_ = stack[0].m_obj;
lean_object* v___y_1731_ = stack[1].m_obj;
lean_object* v___y_1732_ = stack[2].m_obj;
lean_object* v_res_1740_;
v_res_1740_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_1730_, v___y_1731_, v___y_1732_);
stack->m_obj
 = v_res_1740_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_mvarId_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec(v_mvarId_1741_);
return v_res_1745_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(lean_object* v_mvarId_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v_mctx_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1750_ = lean_st_ref_get(v___y_1748_);
v_mctx_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_mctx_1751_);
lean_dec(v___x_1750_);
v___x_1752_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1751_, v_mvarId_1746_);
lean_dec_ref(v_mctx_1751_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v___y_1747_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1746_ = stack[0].m_obj;
lean_object* v___y_1747_ = stack[1].m_obj;
lean_object* v___y_1748_ = stack[2].m_obj;
lean_object* v_res_1756_;
v_res_1756_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_1746_, v___y_1747_, v___y_1748_);
stack->m_obj
 = v_res_1756_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg___boxed(lean_object* v_mvarId_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec(v_mvarId_1757_);
return v_res_1761_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(lean_object* v_m_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_buckets_1764_; lean_object* v___x_1765_; uint64_t v___x_1766_; uint64_t v___x_1767_; uint64_t v___x_1768_; uint64_t v_fold_1769_; uint64_t v___x_1770_; uint64_t v___x_1771_; uint64_t v___x_1772_; size_t v___x_1773_; size_t v___x_1774_; size_t v___x_1775_; size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v_buckets_1764_ = lean_ctor_get(v_m_1762_, 1);
v___x_1765_ = lean_array_get_size(v_buckets_1764_);
v___x_1766_ = l_Lean_Expr_hash(v_a_1763_);
v___x_1767_ = 32ULL;
v___x_1768_ = lean_uint64_shift_right(v___x_1766_, v___x_1767_);
v_fold_1769_ = lean_uint64_xor(v___x_1766_, v___x_1768_);
v___x_1770_ = 16ULL;
v___x_1771_ = lean_uint64_shift_right(v_fold_1769_, v___x_1770_);
v___x_1772_ = lean_uint64_xor(v_fold_1769_, v___x_1771_);
v___x_1773_ = lean_uint64_to_usize(v___x_1772_);
v___x_1774_ = lean_usize_of_nat(v___x_1765_);
v___x_1775_ = ((size_t)1ULL);
v___x_1776_ = lean_usize_sub(v___x_1774_, v___x_1775_);
v___x_1777_ = lean_usize_land(v___x_1773_, v___x_1776_);
v___x_1778_ = lean_array_uget_borrowed(v_buckets_1764_, v___x_1777_);
v___x_1779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1763_, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1762_ = stack[0].m_obj;
lean_object* v_a_1763_ = stack[1].m_obj;
uint8_t v_res_1780_;
v_res_1780_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_1762_, v_a_1763_);
stack->m_num = v_res_1780_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_m_1781_, lean_object* v_a_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_1781_, v_a_1782_);
lean_dec_ref(v_a_1782_);
lean_dec_ref(v_m_1781_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(lean_object* v_mvarId_1789_, lean_object* v_e_1790_, lean_object* v_a_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_d_1802_; lean_object* v_b_1803_; lean_object* v___y_1804_; uint8_t v___x_1810_; 
v___x_1810_ = l_Lean_Expr_hasExprMVar(v_e_1790_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v_e_1790_);
v___x_1811_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v_a_1791_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
else
{
uint8_t v___x_1814_; 
v___x_1814_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_a_1791_, v_e_1790_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_box(0);
lean_inc_ref(v_e_1790_);
v___x_1816_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_a_1791_, v_e_1790_, v___x_1815_);
switch(lean_obj_tag(v_e_1790_))
{
case 11:
{
lean_object* v_struct_1817_; 
v_struct_1817_ = lean_ctor_get(v_e_1790_, 2);
lean_inc_ref(v_struct_1817_);
lean_dec_ref_known(v_e_1790_, 3);
v_e_1790_ = v_struct_1817_;
v_a_1791_ = v___x_1816_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1819_; lean_object* v_body_1820_; 
v_binderType_1819_ = lean_ctor_get(v_e_1790_, 1);
lean_inc_ref(v_binderType_1819_);
v_body_1820_ = lean_ctor_get(v_e_1790_, 2);
lean_inc_ref(v_body_1820_);
lean_dec_ref_known(v_e_1790_, 3);
v_d_1802_ = v_binderType_1819_;
v_b_1803_ = v_body_1820_;
v___y_1804_ = v___x_1816_;
goto v___jp_1801_;
}
case 6:
{
lean_object* v_binderType_1821_; lean_object* v_body_1822_; 
v_binderType_1821_ = lean_ctor_get(v_e_1790_, 1);
lean_inc_ref(v_binderType_1821_);
v_body_1822_ = lean_ctor_get(v_e_1790_, 2);
lean_inc_ref(v_body_1822_);
lean_dec_ref_known(v_e_1790_, 3);
v_d_1802_ = v_binderType_1821_;
v_b_1803_ = v_body_1822_;
v___y_1804_ = v___x_1816_;
goto v___jp_1801_;
}
case 8:
{
lean_object* v_type_1823_; lean_object* v_value_1824_; lean_object* v_body_1825_; lean_object* v___x_1826_; 
v_type_1823_ = lean_ctor_get(v_e_1790_, 1);
lean_inc_ref(v_type_1823_);
v_value_1824_ = lean_ctor_get(v_e_1790_, 2);
lean_inc_ref(v_value_1824_);
v_body_1825_ = lean_ctor_get(v_e_1790_, 3);
lean_inc_ref(v_body_1825_);
lean_dec_ref_known(v_e_1790_, 4);
v___x_1826_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1789_, v_type_1823_, v___x_1816_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v_fst_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_fst_1828_ = lean_ctor_get(v_a_1827_, 0);
if (lean_obj_tag(v_fst_1828_) == 0)
{
lean_dec_ref(v_body_1825_);
lean_dec_ref(v_value_1824_);
return v___x_1826_;
}
else
{
lean_object* v_snd_1829_; lean_object* v___x_1830_; 
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v_snd_1829_ = lean_ctor_get(v_a_1827_, 1);
lean_inc(v_snd_1829_);
lean_dec(v_a_1827_);
v___x_1830_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1789_, v_value_1824_, v_snd_1829_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v_fst_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_fst_1832_ = lean_ctor_get(v_a_1831_, 0);
if (lean_obj_tag(v_fst_1832_) == 0)
{
lean_dec_ref(v_body_1825_);
return v___x_1830_;
}
else
{
lean_object* v_snd_1833_; 
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v_snd_1833_ = lean_ctor_get(v_a_1831_, 1);
lean_inc(v_snd_1833_);
lean_dec(v_a_1831_);
v_e_1790_ = v_body_1825_;
v_a_1791_ = v_snd_1833_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1825_);
return v___x_1830_;
}
}
}
else
{
lean_dec_ref(v_body_1825_);
lean_dec_ref(v_value_1824_);
return v___x_1826_;
}
}
case 10:
{
lean_object* v_expr_1835_; 
v_expr_1835_ = lean_ctor_get(v_e_1790_, 1);
lean_inc_ref(v_expr_1835_);
lean_dec_ref_known(v_e_1790_, 2);
v_e_1790_ = v_expr_1835_;
v_a_1791_ = v___x_1816_;
goto _start;
}
case 5:
{
lean_object* v_fn_1837_; lean_object* v_arg_1838_; lean_object* v___x_1839_; 
v_fn_1837_ = lean_ctor_get(v_e_1790_, 0);
lean_inc_ref(v_fn_1837_);
v_arg_1838_ = lean_ctor_get(v_e_1790_, 1);
lean_inc_ref(v_arg_1838_);
lean_dec_ref_known(v_e_1790_, 2);
v___x_1839_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1789_, v_fn_1837_, v___x_1816_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v_fst_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_fst_1841_ = lean_ctor_get(v_a_1840_, 0);
if (lean_obj_tag(v_fst_1841_) == 0)
{
lean_dec_ref(v_arg_1838_);
return v___x_1839_;
}
else
{
lean_object* v_snd_1842_; 
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v_snd_1842_ = lean_ctor_get(v_a_1840_, 1);
lean_inc(v_snd_1842_);
lean_dec(v_a_1840_);
v_e_1790_ = v_arg_1838_;
v_a_1791_ = v_snd_1842_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1838_);
return v___x_1839_;
}
}
case 2:
{
lean_object* v_mvarId_1844_; lean_object* v___x_1845_; 
v_mvarId_1844_ = lean_ctor_get(v_e_1790_, 0);
lean_inc(v_mvarId_1844_);
lean_dec_ref_known(v_e_1790_, 1);
v___x_1845_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1789_, v_mvarId_1844_, v___x_1816_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v___x_1845_;
}
default: 
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref(v_e_1790_);
v___x_1846_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v___x_1816_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec_ref(v_e_1790_);
v___x_1849_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_a_1791_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
v___jp_1801_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1789_, v_d_1802_, v___y_1804_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v_fst_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_fst_1807_ = lean_ctor_get(v_a_1806_, 0);
if (lean_obj_tag(v_fst_1807_) == 0)
{
lean_dec_ref(v_b_1803_);
return v___x_1805_;
}
else
{
lean_object* v_snd_1808_; 
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v_snd_1808_ = lean_ctor_get(v_a_1806_, 1);
lean_inc(v_snd_1808_);
lean_dec(v_a_1806_);
v_e_1790_ = v_b_1803_;
v_a_1791_ = v_snd_1808_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1803_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1789_ = stack[0].m_obj;
lean_object* v_e_1790_ = stack[1].m_obj;
lean_object* v_a_1791_ = stack[2].m_obj;
lean_object* v___y_1792_ = stack[3].m_obj;
lean_object* v___y_1793_ = stack[4].m_obj;
lean_object* v___y_1794_ = stack[5].m_obj;
lean_object* v___y_1795_ = stack[6].m_obj;
lean_object* v___y_1796_ = stack[7].m_obj;
lean_object* v___y_1797_ = stack[8].m_obj;
lean_object* v___y_1798_ = stack[9].m_obj;
lean_object* v___y_1799_ = stack[10].m_obj;
lean_object* v_res_1852_;
v_res_1852_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1789_, v_e_1790_, v_a_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
stack->m_obj
 = v_res_1852_;
}
lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(lean_object* v_mvarId_1853_, lean_object* v_mvarId_x27_1854_, lean_object* v_a_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v___x_1865_; 
v___x_1865_ = l_Lean_instBEqMVarId_beq(v_mvarId_1853_, v_mvarId_x27_1854_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_x27_1854_, v_a_1855_, v___y_1861_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1950_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1950_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1950_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_fst_1871_; 
v_fst_1871_ = lean_ctor_get(v_a_1867_, 0);
lean_inc(v_fst_1871_);
if (lean_obj_tag(v_fst_1871_) == 0)
{
lean_object* v_snd_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_mvarId_x27_1854_);
v_snd_1872_ = lean_ctor_get(v_a_1867_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_a_1867_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v_a_1867_, 0);
lean_dec(v_unused_1891_);
v___x_1874_ = v_a_1867_;
v_isShared_1875_ = v_isSharedCheck_1890_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_snd_1872_);
lean_dec(v_a_1867_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1890_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1889_; 
v_a_1876_ = lean_ctor_get(v_fst_1871_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_fst_1871_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1878_ = v_fst_1871_;
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v_fst_1871_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1881_);
v___x_1883_ = v___x_1874_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_snd_1872_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1883_);
v___x_1885_ = v___x_1869_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
}
else
{
lean_object* v_a_1892_; 
lean_del_object(v___x_1869_);
v_a_1892_ = lean_ctor_get(v_fst_1871_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v_fst_1871_, 1);
if (lean_obj_tag(v_a_1892_) == 0)
{
lean_object* v_snd_1893_; lean_object* v___x_1894_; 
v_snd_1893_ = lean_ctor_get(v_a_1867_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_a_1867_);
v___x_1894_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_x27_1854_, v_snd_1893_, v___y_1861_);
lean_dec(v_mvarId_x27_1854_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1938_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1938_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1938_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_fst_1899_; 
v_fst_1899_ = lean_ctor_get(v_a_1895_, 0);
lean_inc(v_fst_1899_);
if (lean_obj_tag(v_fst_1899_) == 0)
{
lean_object* v_snd_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1918_; 
v_snd_1900_ = lean_ctor_get(v_a_1895_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_a_1895_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v_a_1895_, 0);
lean_dec(v_unused_1919_);
v___x_1902_ = v_a_1895_;
v_isShared_1903_ = v_isSharedCheck_1918_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_snd_1900_);
lean_dec(v_a_1895_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1918_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1917_; 
v_a_1904_ = lean_ctor_get(v_fst_1899_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_fst_1899_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1906_ = v_fst_1899_;
v_isShared_1907_ = v_isSharedCheck_1917_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v_fst_1899_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1917_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1909_);
v___x_1911_ = v___x_1902_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_snd_1900_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1911_);
v___x_1913_ = v___x_1897_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
else
{
lean_object* v_a_1920_; 
v_a_1920_ = lean_ctor_get(v_fst_1899_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v_fst_1899_, 1);
if (lean_obj_tag(v_a_1920_) == 0)
{
lean_object* v_snd_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1932_; 
v_snd_1921_ = lean_ctor_get(v_a_1895_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_a_1895_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v_a_1895_, 0);
lean_dec(v_unused_1933_);
v___x_1923_ = v_a_1895_;
v_isShared_1924_ = v_isSharedCheck_1932_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snd_1921_);
lean_dec(v_a_1895_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1932_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_snd_1921_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1927_);
v___x_1929_ = v___x_1897_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_val_1934_; lean_object* v_snd_1935_; lean_object* v_mvarIdPending_1936_; 
lean_del_object(v___x_1897_);
v_val_1934_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v_a_1920_, 1);
v_snd_1935_ = lean_ctor_get(v_a_1895_, 1);
lean_inc(v_snd_1935_);
lean_dec(v_a_1895_);
v_mvarIdPending_1936_ = lean_ctor_get(v_val_1934_, 1);
lean_inc(v_mvarIdPending_1936_);
lean_dec(v_val_1934_);
v_mvarId_x27_1854_ = v_mvarIdPending_1936_;
v_a_1855_ = v_snd_1935_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1894_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1894_);
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
lean_object* v_snd_1947_; lean_object* v_val_1948_; lean_object* v___x_1949_; 
lean_dec(v_mvarId_x27_1854_);
v_snd_1947_ = lean_ctor_get(v_a_1867_, 1);
lean_inc(v_snd_1947_);
lean_dec(v_a_1867_);
v_val_1948_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_val_1948_);
lean_dec_ref_known(v_a_1892_, 1);
v___x_1949_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1853_, v_val_1948_, v_snd_1947_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec(v_mvarId_x27_1854_);
v_a_1951_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1866_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1866_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v_mvarId_x27_1854_);
v___x_1959_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1));
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v_a_1855_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1853_ = stack[0].m_obj;
lean_object* v_mvarId_x27_1854_ = stack[1].m_obj;
lean_object* v_a_1855_ = stack[2].m_obj;
lean_object* v___y_1856_ = stack[3].m_obj;
lean_object* v___y_1857_ = stack[4].m_obj;
lean_object* v___y_1858_ = stack[5].m_obj;
lean_object* v___y_1859_ = stack[6].m_obj;
lean_object* v___y_1860_ = stack[7].m_obj;
lean_object* v___y_1861_ = stack[8].m_obj;
lean_object* v___y_1862_ = stack[9].m_obj;
lean_object* v___y_1863_ = stack[10].m_obj;
lean_object* v_res_1962_;
v_res_1962_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1853_, v_mvarId_x27_1854_, v_a_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
stack->m_obj
 = v_res_1962_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___boxed(lean_object* v_mvarId_1963_, lean_object* v_mvarId_x27_1964_, lean_object* v_a_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1963_, v_mvarId_x27_1964_, v_a_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v_mvarId_1963_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6___boxed(lean_object* v_mvarId_1976_, lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1976_, v_e_1977_, v_a_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v_mvarId_1976_);
return v_res_1988_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_unsigned_to_nat(16u);
v___x_1991_ = lean_mk_array(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
lean_ctor_set(v___x_1994_, 1, v___x_1992_);
return v___x_1994_;
}
}
lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_mvarId_1995_, lean_object* v_e_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lean_Expr_hasExprMVar(v_e_1996_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec_ref(v_e_1996_);
v___x_2007_ = 1;
v___x_2008_ = lean_box(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
else
{
uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = 0;
v___x_2011_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
v___x_2012_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1995_, v_e_1996_, v___x_2011_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2026_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2026_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2026_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_fst_2017_; 
v_fst_2017_ = lean_ctor_get(v_a_2013_, 0);
lean_inc(v_fst_2017_);
lean_dec(v_a_2013_);
if (lean_obj_tag(v_fst_2017_) == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_dec_ref_known(v_fst_2017_, 1);
v___x_2018_ = lean_box(v___x_2010_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2018_);
v___x_2020_ = v___x_2015_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_dec_ref_known(v_fst_2017_, 1);
v___x_2022_ = lean_box(v___x_2006_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2022_);
v___x_2024_ = v___x_2015_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_a_2027_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2012_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2012_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1995_ = stack[0].m_obj;
lean_object* v_e_1996_ = stack[1].m_obj;
lean_object* v___y_1997_ = stack[2].m_obj;
lean_object* v___y_1998_ = stack[3].m_obj;
lean_object* v___y_1999_ = stack[4].m_obj;
lean_object* v___y_2000_ = stack[5].m_obj;
lean_object* v___y_2001_ = stack[6].m_obj;
lean_object* v___y_2002_ = stack[7].m_obj;
lean_object* v___y_2003_ = stack[8].m_obj;
lean_object* v___y_2004_ = stack[9].m_obj;
lean_object* v_res_2035_;
v_res_2035_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_mvarId_1995_, v_e_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
stack->m_obj
 = v_res_2035_;
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_mvarId_2036_, lean_object* v_e_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_mvarId_2036_, v_e_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v_mvarId_2036_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v_ks_2052_; lean_object* v_vs_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2077_; 
v_ks_2052_ = lean_ctor_get(v_x_2048_, 0);
v_vs_2053_ = lean_ctor_get(v_x_2048_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2048_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2055_ = v_x_2048_;
v_isShared_2056_ = v_isSharedCheck_2077_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_vs_2053_);
lean_inc(v_ks_2052_);
lean_dec(v_x_2048_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2077_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = lean_array_get_size(v_ks_2052_);
v___x_2058_ = lean_nat_dec_lt(v_x_2049_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_dec(v_x_2049_);
v___x_2059_ = lean_array_push(v_ks_2052_, v_x_2050_);
v___x_2060_ = lean_array_push(v_vs_2053_, v_x_2051_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v___x_2060_);
lean_ctor_set(v___x_2055_, 0, v___x_2059_);
v___x_2062_ = v___x_2055_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v_k_x27_2064_; uint8_t v___x_2065_; 
v_k_x27_2064_ = lean_array_fget_borrowed(v_ks_2052_, v_x_2049_);
v___x_2065_ = l_Lean_instBEqMVarId_beq(v_x_2050_, v_k_x27_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2067_; 
if (v_isShared_2056_ == 0)
{
v___x_2067_ = v___x_2055_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_ks_2052_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_vs_2053_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_add(v_x_2049_, v___x_2068_);
lean_dec(v_x_2049_);
v_x_2048_ = v___x_2067_;
v_x_2049_ = v___x_2069_;
goto _start;
}
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2072_ = lean_array_fset(v_ks_2052_, v_x_2049_, v_x_2050_);
v___x_2073_ = lean_array_fset(v_vs_2053_, v_x_2049_, v_x_2051_);
lean_dec(v_x_2049_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v___x_2073_);
lean_ctor_set(v___x_2055_, 0, v___x_2072_);
v___x_2075_ = v___x_2055_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2073_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_n_2078_, lean_object* v_k_2079_, lean_object* v_v_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_n_2078_, v___x_2081_, v_k_2079_, v_v_2080_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2083_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_x_2084_, size_t v_x_2085_, size_t v_x_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_){
_start:
{
if (lean_obj_tag(v_x_2084_) == 0)
{
lean_object* v_es_2089_; size_t v___x_2090_; size_t v___x_2091_; lean_object* v_j_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_es_2089_ = lean_ctor_get(v_x_2084_, 0);
v___x_2090_ = ((size_t)31ULL);
v___x_2091_ = lean_usize_land(v_x_2085_, v___x_2090_);
v_j_2092_ = lean_usize_to_nat(v___x_2091_);
v___x_2093_ = lean_array_get_size(v_es_2089_);
v___x_2094_ = lean_nat_dec_lt(v_j_2092_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_dec(v_j_2092_);
lean_dec(v_x_2088_);
lean_dec(v_x_2087_);
return v_x_2084_;
}
else
{
lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2133_; 
lean_inc_ref(v_es_2089_);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_x_2084_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v_x_2084_, 0);
lean_dec(v_unused_2134_);
v___x_2096_ = v_x_2084_;
v_isShared_2097_ = v_isSharedCheck_2133_;
goto v_resetjp_2095_;
}
else
{
lean_dec(v_x_2084_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2133_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_v_2098_; lean_object* v___x_2099_; lean_object* v_xs_x27_2100_; lean_object* v___y_2102_; 
v_v_2098_ = lean_array_fget(v_es_2089_, v_j_2092_);
v___x_2099_ = lean_box(0);
v_xs_x27_2100_ = lean_array_fset(v_es_2089_, v_j_2092_, v___x_2099_);
switch(lean_obj_tag(v_v_2098_))
{
case 0:
{
lean_object* v_key_2107_; lean_object* v_val_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2118_; 
v_key_2107_ = lean_ctor_get(v_v_2098_, 0);
v_val_2108_ = lean_ctor_get(v_v_2098_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_v_2098_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2110_ = v_v_2098_;
v_isShared_2111_ = v_isSharedCheck_2118_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_val_2108_);
lean_inc(v_key_2107_);
lean_dec(v_v_2098_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2118_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
uint8_t v___x_2112_; 
v___x_2112_ = l_Lean_instBEqMVarId_beq(v_x_2087_, v_key_2107_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_del_object(v___x_2110_);
v___x_2113_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2107_, v_val_2108_, v_x_2087_, v_x_2088_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___y_2102_ = v___x_2114_;
goto v___jp_2101_;
}
else
{
lean_object* v___x_2116_; 
lean_dec(v_val_2108_);
lean_dec(v_key_2107_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v_x_2088_);
lean_ctor_set(v___x_2110_, 0, v_x_2087_);
v___x_2116_ = v___x_2110_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_x_2087_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_x_2088_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
v___y_2102_ = v___x_2116_;
goto v___jp_2101_;
}
}
}
}
case 1:
{
lean_object* v_node_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2131_; 
v_node_2119_ = lean_ctor_get(v_v_2098_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_v_2098_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2121_ = v_v_2098_;
v_isShared_2122_ = v_isSharedCheck_2131_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_node_2119_);
lean_dec(v_v_2098_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2131_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
size_t v___x_2123_; size_t v___x_2124_; size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2123_ = ((size_t)5ULL);
v___x_2124_ = lean_usize_shift_right(v_x_2085_, v___x_2123_);
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_add(v_x_2086_, v___x_2125_);
v___x_2127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_node_2119_, v___x_2124_, v___x_2126_, v_x_2087_, v_x_2088_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2127_);
v___x_2129_ = v___x_2121_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
v___y_2102_ = v___x_2129_;
goto v___jp_2101_;
}
}
}
default: 
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_x_2087_);
lean_ctor_set(v___x_2132_, 1, v_x_2088_);
v___y_2102_ = v___x_2132_;
goto v___jp_2101_;
}
}
v___jp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_array_fset(v_xs_x27_2100_, v_j_2092_, v___y_2102_);
lean_dec(v_j_2092_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2103_);
v___x_2105_ = v___x_2096_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
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
}
else
{
lean_object* v_ks_2135_; lean_object* v_vs_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2154_; 
v_ks_2135_ = lean_ctor_get(v_x_2084_, 0);
v_vs_2136_ = lean_ctor_get(v_x_2084_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_x_2084_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2138_ = v_x_2084_;
v_isShared_2139_ = v_isSharedCheck_2154_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_vs_2136_);
lean_inc(v_ks_2135_);
lean_dec(v_x_2084_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2154_;
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
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_ks_2135_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_vs_2136_);
v___x_2141_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v_newNode_2142_; size_t v___x_2143_; uint8_t v___x_2144_; 
v_newNode_2142_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v___x_2141_, v_x_2087_, v_x_2088_);
v___x_2143_ = ((size_t)7ULL);
v___x_2144_ = lean_usize_dec_le(v___x_2143_, v_x_2086_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2145_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2142_);
v___x_2146_ = lean_unsigned_to_nat(4u);
v___x_2147_ = lean_nat_dec_lt(v___x_2145_, v___x_2146_);
lean_dec(v___x_2145_);
if (v___x_2147_ == 0)
{
lean_object* v_ks_2148_; lean_object* v_vs_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_ks_2148_ = lean_ctor_get(v_newNode_2142_, 0);
lean_inc_ref(v_ks_2148_);
v_vs_2149_ = lean_ctor_get(v_newNode_2142_, 1);
lean_inc_ref(v_vs_2149_);
lean_dec_ref(v_newNode_2142_);
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0);
v___x_2152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_x_2086_, v_ks_2148_, v_vs_2149_, v___x_2150_, v___x_2151_);
lean_dec_ref(v_vs_2149_);
lean_dec_ref(v_ks_2148_);
return v___x_2152_;
}
else
{
return v_newNode_2142_;
}
}
else
{
return v_newNode_2142_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2084_ = stack[0].m_obj;
size_t v_x_2085_ = stack[1].m_num;
size_t v_x_2086_ = stack[2].m_num;
lean_object* v_x_2087_ = stack[3].m_obj;
lean_object* v_x_2088_ = stack[4].m_obj;
lean_object* v_res_2155_;
v_res_2155_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2084_, v_x_2085_, v_x_2086_, v_x_2087_, v_x_2088_);
stack->m_obj
 = v_res_2155_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(size_t v_depth_2156_, lean_object* v_keys_2157_, lean_object* v_vals_2158_, lean_object* v_i_2159_, lean_object* v_entries_2160_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_array_get_size(v_keys_2157_);
v___x_2162_ = lean_nat_dec_lt(v_i_2159_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_dec(v_i_2159_);
return v_entries_2160_;
}
else
{
lean_object* v_k_2163_; lean_object* v_v_2164_; uint64_t v___x_2165_; size_t v_h_2166_; size_t v___x_2167_; lean_object* v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; size_t v_h_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_k_2163_ = lean_array_fget_borrowed(v_keys_2157_, v_i_2159_);
v_v_2164_ = lean_array_fget_borrowed(v_vals_2158_, v_i_2159_);
v___x_2165_ = l_Lean_instHashableMVarId_hash(v_k_2163_);
v_h_2166_ = lean_uint64_to_usize(v___x_2165_);
v___x_2167_ = ((size_t)5ULL);
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_sub(v_depth_2156_, v___x_2169_);
v___x_2171_ = lean_usize_mul(v___x_2167_, v___x_2170_);
v_h_2172_ = lean_usize_shift_right(v_h_2166_, v___x_2171_);
v___x_2173_ = lean_nat_add(v_i_2159_, v___x_2168_);
lean_dec(v_i_2159_);
lean_inc(v_v_2164_);
lean_inc(v_k_2163_);
v___x_2174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_entries_2160_, v_h_2172_, v_depth_2156_, v_k_2163_, v_v_2164_);
v_i_2159_ = v___x_2173_;
v_entries_2160_ = v___x_2174_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2156_ = stack[0].m_num;
lean_object* v_keys_2157_ = stack[1].m_obj;
lean_object* v_vals_2158_ = stack[2].m_obj;
lean_object* v_i_2159_ = stack[3].m_obj;
lean_object* v_entries_2160_ = stack[4].m_obj;
lean_object* v_res_2176_;
v_res_2176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_2156_, v_keys_2157_, v_vals_2158_, v_i_2159_, v_entries_2160_);
stack->m_obj
 = v_res_2176_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_depth_2177_, lean_object* v_keys_2178_, lean_object* v_vals_2179_, lean_object* v_i_2180_, lean_object* v_entries_2181_){
_start:
{
size_t v_depth_boxed_2182_; lean_object* v_res_2183_; 
v_depth_boxed_2182_ = lean_unbox_usize(v_depth_2177_);
lean_dec(v_depth_2177_);
v_res_2183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_boxed_2182_, v_keys_2178_, v_vals_2179_, v_i_2180_, v_entries_2181_);
lean_dec_ref(v_vals_2179_);
lean_dec_ref(v_keys_2178_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_2184_, lean_object* v_x_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
size_t v_x_96778__boxed_2189_; size_t v_x_96779__boxed_2190_; lean_object* v_res_2191_; 
v_x_96778__boxed_2189_ = lean_unbox_usize(v_x_2185_);
lean_dec(v_x_2185_);
v_x_96779__boxed_2190_ = lean_unbox_usize(v_x_2186_);
lean_dec(v_x_2186_);
v_res_2191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2184_, v_x_96778__boxed_2189_, v_x_96779__boxed_2190_, v_x_2187_, v_x_2188_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_){
_start:
{
uint64_t v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2195_ = l_Lean_instHashableMVarId_hash(v_x_2193_);
v___x_2196_ = lean_uint64_to_usize(v___x_2195_);
v___x_2197_ = ((size_t)1ULL);
v___x_2198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2192_, v___x_2196_, v___x_2197_, v_x_2193_, v_x_2194_);
return v___x_2198_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(lean_object* v_mvarId_2199_, lean_object* v_val_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v_mctx_2204_; lean_object* v_cache_2205_; lean_object* v_zetaDeltaFVarIds_2206_; lean_object* v_postponed_2207_; lean_object* v_diag_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2238_; 
v___x_2203_ = lean_st_ref_take(v___y_2201_);
v_mctx_2204_ = lean_ctor_get(v___x_2203_, 0);
v_cache_2205_ = lean_ctor_get(v___x_2203_, 1);
v_zetaDeltaFVarIds_2206_ = lean_ctor_get(v___x_2203_, 2);
v_postponed_2207_ = lean_ctor_get(v___x_2203_, 3);
v_diag_2208_ = lean_ctor_get(v___x_2203_, 4);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2210_ = v___x_2203_;
v_isShared_2211_ = v_isSharedCheck_2238_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_diag_2208_);
lean_inc(v_postponed_2207_);
lean_inc(v_zetaDeltaFVarIds_2206_);
lean_inc(v_cache_2205_);
lean_inc(v_mctx_2204_);
lean_dec(v___x_2203_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2238_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_depth_2212_; lean_object* v_levelAssignDepth_2213_; lean_object* v_lmvarCounter_2214_; lean_object* v_mvarCounter_2215_; lean_object* v_lDecls_2216_; lean_object* v_decls_2217_; lean_object* v_userNames_2218_; lean_object* v_lAssignment_2219_; lean_object* v_eAssignment_2220_; lean_object* v_dAssignment_2221_; lean_object* v_instanceTypedMVars_2222_; lean_object* v_synthNormMemo_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2237_; 
v_depth_2212_ = lean_ctor_get(v_mctx_2204_, 0);
v_levelAssignDepth_2213_ = lean_ctor_get(v_mctx_2204_, 1);
v_lmvarCounter_2214_ = lean_ctor_get(v_mctx_2204_, 2);
v_mvarCounter_2215_ = lean_ctor_get(v_mctx_2204_, 3);
v_lDecls_2216_ = lean_ctor_get(v_mctx_2204_, 4);
v_decls_2217_ = lean_ctor_get(v_mctx_2204_, 5);
v_userNames_2218_ = lean_ctor_get(v_mctx_2204_, 6);
v_lAssignment_2219_ = lean_ctor_get(v_mctx_2204_, 7);
v_eAssignment_2220_ = lean_ctor_get(v_mctx_2204_, 8);
v_dAssignment_2221_ = lean_ctor_get(v_mctx_2204_, 9);
v_instanceTypedMVars_2222_ = lean_ctor_get(v_mctx_2204_, 10);
v_synthNormMemo_2223_ = lean_ctor_get(v_mctx_2204_, 11);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_mctx_2204_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2225_ = v_mctx_2204_;
v_isShared_2226_ = v_isSharedCheck_2237_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_synthNormMemo_2223_);
lean_inc(v_instanceTypedMVars_2222_);
lean_inc(v_dAssignment_2221_);
lean_inc(v_eAssignment_2220_);
lean_inc(v_lAssignment_2219_);
lean_inc(v_userNames_2218_);
lean_inc(v_decls_2217_);
lean_inc(v_lDecls_2216_);
lean_inc(v_mvarCounter_2215_);
lean_inc(v_lmvarCounter_2214_);
lean_inc(v_levelAssignDepth_2213_);
lean_inc(v_depth_2212_);
lean_dec(v_mctx_2204_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2237_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = lean_box(0);
v___x_2228_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_eAssignment_2220_, v_mvarId_2199_, v_val_2200_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 8, v___x_2228_);
v___x_2230_ = v___x_2225_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_depth_2212_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_levelAssignDepth_2213_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_lmvarCounter_2214_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_mvarCounter_2215_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_lDecls_2216_);
lean_ctor_set(v_reuseFailAlloc_2236_, 5, v_decls_2217_);
lean_ctor_set(v_reuseFailAlloc_2236_, 6, v_userNames_2218_);
lean_ctor_set(v_reuseFailAlloc_2236_, 7, v_lAssignment_2219_);
lean_ctor_set(v_reuseFailAlloc_2236_, 8, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 9, v_dAssignment_2221_);
lean_ctor_set(v_reuseFailAlloc_2236_, 10, v_instanceTypedMVars_2222_);
lean_ctor_set(v_reuseFailAlloc_2236_, 11, v_synthNormMemo_2223_);
v___x_2230_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2230_);
v___x_2232_ = v___x_2210_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_cache_2205_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_zetaDeltaFVarIds_2206_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_postponed_2207_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_diag_2208_);
v___x_2232_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_st_ref_put(v___y_2201_, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2227_);
return v___x_2234_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2199_ = stack[0].m_obj;
lean_object* v_val_2200_ = stack[1].m_obj;
lean_object* v___y_2201_ = stack[2].m_obj;
lean_object* v_res_2239_;
v_res_2239_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_2199_, v_val_2200_, v___y_2201_);
stack->m_obj
 = v_res_2239_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg___boxed(lean_object* v_mvarId_2240_, lean_object* v_val_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_2240_, v_val_2241_, v___y_2242_);
lean_dec(v___y_2242_);
return v_res_2244_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_o_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_env_2250_; lean_object* v___x_2251_; lean_object* v_toEnvExtension_2252_; lean_object* v_asyncMode_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v_merged_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2265_; 
v___x_2248_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2249_ = lean_st_ref_get(v___y_2246_);
v_env_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_ref(v_env_2250_);
lean_dec(v___x_2249_);
v___x_2251_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2252_ = lean_ctor_get(v___x_2251_, 0);
v_asyncMode_2253_ = lean_ctor_get(v_toEnvExtension_2252_, 2);
v___x_2254_ = lean_box(0);
v___x_2255_ = 0;
v___x_2256_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2248_, v___x_2251_, v_env_2250_, v_asyncMode_2253_, v___x_2254_, v___x_2255_);
v_merged_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2265_ == 0)
{
lean_object* v_unused_2266_; 
v_unused_2266_ = lean_ctor_get(v___x_2256_, 1);
lean_dec(v_unused_2266_);
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_merged_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v_merged_2257_);
lean_ctor_set(v___x_2259_, 0, v_o_2245_);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_o_2245_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_merged_2257_);
v___x_2262_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2245_ = stack[0].m_obj;
lean_object* v___y_2246_ = stack[1].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_2245_, v___y_2246_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg___boxed(lean_object* v_o_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_2268_, v___y_2269_);
lean_dec(v___y_2269_);
return v_res_2271_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2278_);
v___x_2282_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v___x_2281_, v___y_2279_);
return v___x_2282_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2272_ = stack[0].m_obj;
lean_object* v___y_2273_ = stack[1].m_obj;
lean_object* v___y_2274_ = stack[2].m_obj;
lean_object* v___y_2275_ = stack[3].m_obj;
lean_object* v___y_2276_ = stack[4].m_obj;
lean_object* v___y_2277_ = stack[5].m_obj;
lean_object* v___y_2278_ = stack[6].m_obj;
lean_object* v___y_2279_ = stack[7].m_obj;
lean_object* v_res_2283_;
v_res_2283_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
stack->m_obj
 = v_res_2283_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2293_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
return v___x_2305_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2309_, lean_object* v_snd_2310_, uint8_t v___x_2311_, lean_object* v___x_2312_, uint8_t v___x_2313_, uint8_t v_useReducible_2314_, uint8_t v___x_2315_, lean_object* v___x_2316_, lean_object* v___x_2317_, lean_object* v_simprocs_2318_, lean_object* v_discharge_x3f_2319_, lean_object* v_snd_2320_, lean_object* v___f_2321_, lean_object* v___x_2322_, lean_object* v___x_2323_, lean_object* v___x_2324_, lean_object* v___x_2325_, lean_object* v___f_2326_, lean_object* v_a_2327_, lean_object* v___x_2328_, lean_object* v___f_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; 
if (lean_obj_tag(v_usingArg_2309_) == 1)
{
lean_object* v_val_2552_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___x_2604_; lean_object* v_infoState_2605_; uint8_t v_enabled_2606_; 
v_val_2552_ = lean_ctor_get(v_usingArg_2309_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v_usingArg_2309_, 1);
v___x_2604_ = lean_st_ref_get(v___y_2337_);
v_infoState_2605_ = lean_ctor_get(v___x_2604_, 8);
lean_inc_ref(v_infoState_2605_);
lean_dec(v___x_2604_);
v_enabled_2606_ = lean_ctor_get_uint8(v_infoState_2605_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2605_);
if (v_enabled_2606_ == 0)
{
lean_dec_ref(v___f_2329_);
v___y_2554_ = v___y_2330_;
v___y_2555_ = v___y_2331_;
v___y_2556_ = v___y_2332_;
v___y_2557_ = v___y_2333_;
v___y_2558_ = v___y_2334_;
v___y_2559_ = v___y_2335_;
v___y_2560_ = v___y_2336_;
v___y_2561_ = v___y_2337_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2607_; lean_object* v_a_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; 
v___x_2607_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2337_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref(v___x_2607_);
v___f_2609_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2609_, 0, v_a_2608_);
v___x_2610_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2609_, v___f_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_dec_ref_known(v___x_2610_, 1);
v___y_2554_ = v___y_2330_;
v___y_2555_ = v___y_2331_;
v___y_2556_ = v___y_2332_;
v___y_2557_ = v___y_2333_;
v___y_2558_ = v___y_2334_;
v___y_2559_ = v___y_2335_;
v___y_2560_ = v___y_2336_;
v___y_2561_ = v___y_2337_;
goto v___jp_2553_;
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_val_2552_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
v___jp_2553_:
{
lean_object* v___x_2562_; lean_object* v_mctx_2563_; lean_object* v_mvarCounter_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2562_ = lean_st_ref_get(v___y_2559_);
v_mctx_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc_ref(v_mctx_2563_);
lean_dec(v___x_2562_);
v_mvarCounter_2564_ = lean_ctor_get(v_mctx_2563_, 3);
lean_inc(v_mvarCounter_2564_);
lean_dec_ref(v_mctx_2563_);
v___x_2565_ = lean_box(0);
v___x_2566_ = l_Lean_Elab_Tactic_elabTerm(v_val_2552_, v___x_2565_, v___x_2311_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc_n(v_a_2567_, 2);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_snd_2310_, v_a_2567_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; uint8_t v___x_2570_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = lean_unbox(v_a_2569_);
lean_dec(v_a_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_mvarCounter_2564_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
v___x_2571_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2572_ = l_Lean_indentExpr(v_a_2567_);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l_Lean_Expr_mvar___override(v_snd_2310_);
v___x_2577_ = l_Lean_MessageData_ofExpr(v___x_2576_);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2575_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2578_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
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
v___y_2404_ = v_mvarCounter_2564_;
v___y_2405_ = v___x_2565_;
v___y_2406_ = v_a_2567_;
v___y_2407_ = v___x_2565_;
v___y_2408_ = v___y_2554_;
v___y_2409_ = v___y_2555_;
v___y_2410_ = v___y_2556_;
v___y_2411_ = v___y_2557_;
v___y_2412_ = v___y_2558_;
v___y_2413_ = v___y_2559_;
v___y_2414_ = v___y_2560_;
v___y_2415_ = v___y_2561_;
goto v___jp_2403_;
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_a_2567_);
lean_dec(v_mvarCounter_2564_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2588_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2568_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2568_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_mvarCounter_2564_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2596_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2566_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2566_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_object* v_lctx_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec_ref(v___f_2329_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v___x_2312_);
lean_dec(v_usingArg_2309_);
v_lctx_2619_ = lean_ctor_get(v___y_2334_, 2);
v___x_2620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10));
v___x_2621_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2619_, v___x_2620_);
if (lean_obj_tag(v___x_2621_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_val_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = l_Lean_LocalDecl_fvarId(v_val_2622_);
lean_dec(v_val_2622_);
v___x_2624_ = lean_mk_empty_array_with_capacity(v___x_2316_);
v___x_2625_ = lean_array_push(v___x_2624_, v___x_2623_);
lean_inc_ref(v_snd_2320_);
v___x_2626_ = l_Lean_Meta_simpGoal(v_snd_2310_, v___x_2317_, v_simprocs_2318_, v_discharge_x3f_2319_, v___x_2313_, v___x_2625_, v_snd_2320_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2655_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2655_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2655_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_fst_2631_; 
v_fst_2631_ = lean_ctor_get(v_a_2627_, 0);
if (lean_obj_tag(v_fst_2631_) == 1)
{
lean_object* v_val_2632_; lean_object* v_snd_2633_; lean_object* v_snd_2634_; lean_object* v___x_2635_; 
lean_del_object(v___x_2629_);
lean_dec_ref(v_snd_2320_);
v_val_2632_ = lean_ctor_get(v_fst_2631_, 0);
lean_inc(v_val_2632_);
v_snd_2633_ = lean_ctor_get(v_a_2627_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_a_2627_);
v_snd_2634_ = lean_ctor_get(v_val_2632_, 1);
lean_inc(v_snd_2634_);
lean_dec(v_val_2632_);
v___x_2635_ = l_Lean_MVarId_assumption(v_snd_2634_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2643_);
v___x_2637_ = v___x_2635_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v___x_2635_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_snd_2633_);
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_snd_2633_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_snd_2633_);
v_a_2644_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2635_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2635_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_object* v___x_2653_; 
lean_dec(v_a_2627_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v_snd_2320_);
v___x_2653_ = v___x_2629_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_snd_2320_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref(v_snd_2320_);
v_a_2656_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2626_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2626_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v___x_2664_; 
lean_dec(v___x_2621_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
v___x_2664_ = l_Lean_MVarId_assumption(v_snd_2310_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___x_2664_, 0);
lean_dec(v_unused_2672_);
v___x_2666_ = v___x_2664_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v___x_2664_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v_snd_2320_);
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_snd_2320_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v_snd_2320_);
v_a_2673_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2664_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2664_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
v___jp_2339_:
{
lean_object* v___x_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
v___x_2343_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_snd_2310_, v___y_2341_, v___y_2342_);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v___x_2343_, 0);
lean_dec(v_unused_2351_);
v___x_2345_ = v___x_2343_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_dec(v___x_2343_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___y_2340_);
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___y_2340_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
v___jp_2352_:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Core_mkFreshUserName(v___y_2366_, v___y_2361_, v___y_2367_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc_n(v_a_2370_, 2);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2371_ = l_Lean_MVarId_rename(v___y_2364_, v___y_2368_, v_a_2370_, v___y_2365_, v___y_2357_, v___y_2361_, v___y_2367_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc_n(v_a_2372_, 2);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = lean_box(v___x_2311_);
v___x_2374_ = lean_box(v___x_2313_);
v___x_2375_ = lean_box(v_useReducible_2314_);
v___x_2376_ = lean_box(v___x_2315_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2377_, 0, v_a_2372_);
lean_closure_set(v___f_2377_, 1, v_a_2370_);
lean_closure_set(v___f_2377_, 2, v___x_2373_);
lean_closure_set(v___f_2377_, 3, v___y_2355_);
lean_closure_set(v___f_2377_, 4, v___y_2354_);
lean_closure_set(v___f_2377_, 5, v___x_2312_);
lean_closure_set(v___f_2377_, 6, v___x_2374_);
lean_closure_set(v___f_2377_, 7, v___y_2353_);
lean_closure_set(v___f_2377_, 8, v___x_2375_);
lean_closure_set(v___f_2377_, 9, v___x_2376_);
v___x_2378_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_a_2372_, v___f_2377_, v___y_2363_, v___y_2360_, v___y_2358_, v___y_2359_, v___y_2365_, v___y_2357_, v___y_2361_, v___y_2367_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_dec_ref_known(v___x_2378_, 1);
v___y_2340_ = v___y_2356_;
v___y_2341_ = v___y_2362_;
v___y_2342_ = v___y_2357_;
goto v___jp_2339_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref(v___y_2362_);
lean_dec_ref(v___y_2356_);
lean_dec(v_snd_2310_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2370_);
lean_dec_ref(v___y_2362_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2387_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2371_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2371_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v___y_2368_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2362_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2395_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2369_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2369_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
v___jp_2403_:
{
lean_object* v___x_2416_; 
lean_inc(v_snd_2310_);
v___x_2416_ = l_Lean_MVarId_getType(v_snd_2310_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
lean_inc(v_snd_2310_);
v___x_2418_ = l_Lean_MVarId_getTag(v_snd_2310_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
v___x_2420_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2417_, v_a_2419_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = l_Lean_Expr_mvarId_x21(v_a_2421_);
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1));
lean_inc_ref(v___y_2406_);
v___x_2424_ = l_Lean_MVarId_note(v___x_2422_, v___x_2423_, v___y_2406_, v___y_2407_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v_fst_2426_; lean_object* v_snd_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v_fst_2426_ = lean_ctor_get(v_a_2425_, 0);
lean_inc_n(v_fst_2426_, 2);
v_snd_2427_ = lean_ctor_get(v_a_2425_, 1);
lean_inc(v_snd_2427_);
lean_dec(v_a_2425_);
v___x_2428_ = lean_mk_empty_array_with_capacity(v___x_2316_);
v___x_2429_ = lean_array_push(v___x_2428_, v_fst_2426_);
v___x_2430_ = l_Lean_Meta_simpGoal(v_snd_2427_, v___x_2317_, v_simprocs_2318_, v_discharge_x3f_2319_, v___x_2313_, v___x_2429_, v_snd_2320_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v_fst_2432_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v_fst_2432_ = lean_ctor_get(v_a_2431_, 0);
if (lean_obj_tag(v_fst_2432_) == 0)
{
lean_object* v_snd_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_fst_2426_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___x_2312_);
v_snd_2433_ = lean_ctor_get(v_a_2431_, 1);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_a_2431_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v_a_2431_, 0);
lean_dec(v_unused_2504_);
v___x_2435_ = v_a_2431_;
v_isShared_2436_ = v_isSharedCheck_2503_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_snd_2433_);
lean_dec(v_a_2431_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2503_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v_a_2438_; uint8_t v___x_2439_; 
v___x_2437_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2438_);
lean_dec(v_a_2438_);
if (v___x_2439_ == 0)
{
lean_del_object(v___x_2435_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
v___y_2340_ = v_snd_2433_;
v___y_2341_ = v_a_2421_;
v___y_2342_ = v___y_2413_;
goto v___jp_2339_;
}
else
{
if (lean_obj_tag(v___y_2406_) == 1)
{
lean_object* v_fvarId_2440_; lean_object* v_lctx_2441_; lean_object* v___x_2442_; 
v_fvarId_2440_ = lean_ctor_get(v___y_2406_, 0);
lean_inc(v_fvarId_2440_);
lean_dec_ref_known(v___y_2406_, 1);
v_lctx_2441_ = lean_ctor_get(v___y_2412_, 2);
lean_inc_ref(v_lctx_2441_);
v___x_2442_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2441_, v_fvarId_2440_);
if (lean_obj_tag(v___x_2442_) == 1)
{
lean_object* v_val_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2502_; 
v_val_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2502_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_val_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2502_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = l_Lean_mkIdent(v_val_2443_);
lean_inc_ref(v___f_2321_);
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
v___x_2448_ = lean_apply_9(v___f_2321_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc_n(v_a_2449_, 2);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2324_);
lean_inc_ref(v___x_2323_);
lean_inc_ref(v___x_2322_);
v___x_2451_ = l_Lean_Name_mkStr4(v___x_2322_, v___x_2323_, v___x_2324_, v___x_2450_);
v___x_2452_ = l_Lean_Syntax_node1(v_a_2449_, v___x_2325_, v___x_2447_);
v___x_2453_ = l_Lean_Syntax_node1(v_a_2449_, v___x_2451_, v___x_2452_);
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
v___x_2454_ = lean_apply_9(v___f_2321_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_ref_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc_n(v_a_2455_, 2);
lean_dec_ref_known(v___x_2454_, 1);
v_ref_2456_ = lean_ctor_get(v___y_2414_, 2);
v___x_2457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 2);
lean_ctor_set(v___x_2435_, 1, v___x_2457_);
lean_ctor_set(v___x_2435_, 0, v_a_2455_);
v___x_2459_ = v___x_2435_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2455_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2461_ = l_Lean_Name_mkStr4(v___x_2322_, v___x_2323_, v___x_2324_, v___x_2460_);
v___x_2462_ = l_Lean_Syntax_node2(v_a_2455_, v___x_2461_, v___x_2459_, v___x_2453_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2462_);
v___x_2464_ = v___x_2445_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; 
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
v___x_2465_ = lean_apply_10(v___f_2326_, v___x_2464_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, lean_box(0));
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
lean_inc(v_ref_2456_);
v___x_2467_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2327_, v_ref_2456_, v_a_2466_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_dec_ref_known(v___x_2467_, 1);
v___y_2340_ = v_snd_2433_;
v___y_2341_ = v_a_2421_;
v___y_2342_ = v___y_2413_;
goto v___jp_2339_;
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_snd_2433_);
lean_dec(v_a_2421_);
lean_dec(v_snd_2310_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec(v_snd_2433_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2327_);
lean_dec(v_snd_2310_);
v_a_2476_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2465_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2465_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v___x_2453_);
lean_del_object(v___x_2445_);
lean_del_object(v___x_2435_);
lean_dec(v_snd_2433_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec(v_snd_2310_);
v_a_2486_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2454_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2454_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v___x_2447_);
lean_del_object(v___x_2445_);
lean_del_object(v___x_2435_);
lean_dec(v_snd_2433_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec(v_snd_2310_);
v_a_2494_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2448_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2448_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
else
{
lean_dec(v___x_2442_);
lean_del_object(v___x_2435_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
v___y_2340_ = v_snd_2433_;
v___y_2341_ = v_a_2421_;
v___y_2342_ = v___y_2413_;
goto v___jp_2339_;
}
}
else
{
lean_del_object(v___x_2435_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
v___y_2340_ = v_snd_2433_;
v___y_2341_ = v_a_2421_;
v___y_2342_ = v___y_2413_;
goto v___jp_2339_;
}
}
}
}
else
{
lean_object* v_val_2505_; lean_object* v_snd_2506_; lean_object* v_fst_2507_; lean_object* v_snd_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
v_val_2505_ = lean_ctor_get(v_fst_2432_, 0);
lean_inc(v_val_2505_);
v_snd_2506_ = lean_ctor_get(v_a_2431_, 1);
lean_inc(v_snd_2506_);
lean_dec(v_a_2431_);
v_fst_2507_ = lean_ctor_get(v_val_2505_, 0);
lean_inc(v_fst_2507_);
v_snd_2508_ = lean_ctor_get(v_val_2505_, 1);
lean_inc(v_snd_2508_);
lean_dec(v_val_2505_);
v___x_2509_ = lean_array_get_size(v_fst_2507_);
v___x_2510_ = lean_nat_dec_lt(v___x_2328_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_dec(v_fst_2507_);
v___y_2353_ = v___y_2405_;
v___y_2354_ = v___y_2404_;
v___y_2355_ = v___y_2406_;
v___y_2356_ = v_snd_2506_;
v___y_2357_ = v___y_2413_;
v___y_2358_ = v___y_2410_;
v___y_2359_ = v___y_2411_;
v___y_2360_ = v___y_2409_;
v___y_2361_ = v___y_2414_;
v___y_2362_ = v_a_2421_;
v___y_2363_ = v___y_2408_;
v___y_2364_ = v_snd_2508_;
v___y_2365_ = v___y_2412_;
v___y_2366_ = v___x_2423_;
v___y_2367_ = v___y_2415_;
v___y_2368_ = v_fst_2426_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2511_; 
lean_dec(v_fst_2426_);
v___x_2511_ = lean_array_fget(v_fst_2507_, v___x_2328_);
lean_dec(v_fst_2507_);
v___y_2353_ = v___y_2405_;
v___y_2354_ = v___y_2404_;
v___y_2355_ = v___y_2406_;
v___y_2356_ = v_snd_2506_;
v___y_2357_ = v___y_2413_;
v___y_2358_ = v___y_2410_;
v___y_2359_ = v___y_2411_;
v___y_2360_ = v___y_2409_;
v___y_2361_ = v___y_2414_;
v___y_2362_ = v_a_2421_;
v___y_2363_ = v___y_2408_;
v___y_2364_ = v_snd_2508_;
v___y_2365_ = v___y_2412_;
v___y_2366_ = v___x_2423_;
v___y_2367_ = v___y_2415_;
v___y_2368_ = v___x_2511_;
goto v___jp_2352_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v_fst_2426_);
lean_dec(v_a_2421_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2512_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2430_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2430_);
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
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_a_2421_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2520_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2424_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2424_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2528_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2420_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2420_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_a_2417_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2536_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2418_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2418_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v___f_2326_);
lean_dec(v___x_2325_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___f_2321_);
lean_dec_ref(v_snd_2320_);
lean_dec(v_discharge_x3f_2319_);
lean_dec_ref(v_simprocs_2318_);
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2312_);
lean_dec(v_snd_2310_);
v_a_2544_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2416_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2416_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_usingArg_2309_ = stack[0].m_obj;
lean_object* v_snd_2310_ = stack[1].m_obj;
uint8_t v___x_2311_ = stack[2].m_num;
lean_object* v___x_2312_ = stack[3].m_obj;
uint8_t v___x_2313_ = stack[4].m_num;
uint8_t v_useReducible_2314_ = stack[5].m_num;
uint8_t v___x_2315_ = stack[6].m_num;
lean_object* v___x_2316_ = stack[7].m_obj;
lean_object* v___x_2317_ = stack[8].m_obj;
lean_object* v_simprocs_2318_ = stack[9].m_obj;
lean_object* v_discharge_x3f_2319_ = stack[10].m_obj;
lean_object* v_snd_2320_ = stack[11].m_obj;
lean_object* v___f_2321_ = stack[12].m_obj;
lean_object* v___x_2322_ = stack[13].m_obj;
lean_object* v___x_2323_ = stack[14].m_obj;
lean_object* v___x_2324_ = stack[15].m_obj;
lean_object* v___x_2325_ = stack[16].m_obj;
lean_object* v___f_2326_ = stack[17].m_obj;
lean_object* v_a_2327_ = stack[18].m_obj;
lean_object* v___x_2328_ = stack[19].m_obj;
lean_object* v___f_2329_ = stack[20].m_obj;
lean_object* v___y_2330_ = stack[21].m_obj;
lean_object* v___y_2331_ = stack[22].m_obj;
lean_object* v___y_2332_ = stack[23].m_obj;
lean_object* v___y_2333_ = stack[24].m_obj;
lean_object* v___y_2334_ = stack[25].m_obj;
lean_object* v___y_2335_ = stack[26].m_obj;
lean_object* v___y_2336_ = stack[27].m_obj;
lean_object* v___y_2337_ = stack[28].m_obj;
lean_object* v_res_2681_;
v_res_2681_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2309_, v_snd_2310_, v___x_2311_, v___x_2312_, v___x_2313_, v_useReducible_2314_, v___x_2315_, v___x_2316_, v___x_2317_, v_simprocs_2318_, v_discharge_x3f_2319_, v_snd_2320_, v___f_2321_, v___x_2322_, v___x_2323_, v___x_2324_, v___x_2325_, v___f_2326_, v_a_2327_, v___x_2328_, v___f_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
stack->m_obj
 = v_res_2681_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v_usingArg_2682_ = _args[0];
lean_object* v_snd_2683_ = _args[1];
lean_object* v___x_2684_ = _args[2];
lean_object* v___x_2685_ = _args[3];
lean_object* v___x_2686_ = _args[4];
lean_object* v_useReducible_2687_ = _args[5];
lean_object* v___x_2688_ = _args[6];
lean_object* v___x_2689_ = _args[7];
lean_object* v___x_2690_ = _args[8];
lean_object* v_simprocs_2691_ = _args[9];
lean_object* v_discharge_x3f_2692_ = _args[10];
lean_object* v_snd_2693_ = _args[11];
lean_object* v___f_2694_ = _args[12];
lean_object* v___x_2695_ = _args[13];
lean_object* v___x_2696_ = _args[14];
lean_object* v___x_2697_ = _args[15];
lean_object* v___x_2698_ = _args[16];
lean_object* v___f_2699_ = _args[17];
lean_object* v_a_2700_ = _args[18];
lean_object* v___x_2701_ = _args[19];
lean_object* v___f_2702_ = _args[20];
lean_object* v___y_2703_ = _args[21];
lean_object* v___y_2704_ = _args[22];
lean_object* v___y_2705_ = _args[23];
lean_object* v___y_2706_ = _args[24];
lean_object* v___y_2707_ = _args[25];
lean_object* v___y_2708_ = _args[26];
lean_object* v___y_2709_ = _args[27];
lean_object* v___y_2710_ = _args[28];
lean_object* v___y_2711_ = _args[29];
_start:
{
uint8_t v___x_97244__boxed_2712_; uint8_t v___x_97246__boxed_2713_; uint8_t v_useReducible_boxed_2714_; uint8_t v___x_97247__boxed_2715_; lean_object* v_res_2716_; 
v___x_97244__boxed_2712_ = lean_unbox(v___x_2684_);
v___x_97246__boxed_2713_ = lean_unbox(v___x_2686_);
v_useReducible_boxed_2714_ = lean_unbox(v_useReducible_2687_);
v___x_97247__boxed_2715_ = lean_unbox(v___x_2688_);
v_res_2716_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2682_, v_snd_2683_, v___x_97244__boxed_2712_, v___x_2685_, v___x_97246__boxed_2713_, v_useReducible_boxed_2714_, v___x_97247__boxed_2715_, v___x_2689_, v___x_2690_, v_simprocs_2691_, v_discharge_x3f_2692_, v_snd_2693_, v___f_2694_, v___x_2695_, v___x_2696_, v___x_2697_, v___x_2698_, v___f_2699_, v_a_2700_, v___x_2701_, v___f_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___x_2701_);
lean_dec(v___x_2689_);
return v_res_2716_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0(void){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2717_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_unsigned_to_nat(32u);
v___x_2721_ = lean_mk_empty_array_with_capacity(v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2723_, lean_object* v_tk_2724_, lean_object* v___x_2725_, lean_object* v___x_2726_, lean_object* v___x_2727_, lean_object* v_simprocs_2728_, uint8_t v___x_2729_, lean_object* v_usingArg_2730_, lean_object* v___x_2731_, uint8_t v___x_2732_, uint8_t v_useReducible_2733_, uint8_t v___x_2734_, lean_object* v___x_2735_, lean_object* v___f_2736_, lean_object* v___x_2737_, lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v___f_2740_, lean_object* v_a_2741_, lean_object* v_usingTk_x3f_2742_, lean_object* v_discharge_x3f_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___y_2754_; 
if (lean_obj_tag(v_usingTk_x3f_2742_) == 0)
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_box(0);
v___y_2754_ = v___x_2868_;
goto v___jp_2753_;
}
else
{
lean_object* v_val_2869_; 
v_val_2869_ = lean_ctor_get(v_usingTk_x3f_2742_, 0);
lean_inc(v_val_2869_);
lean_dec_ref_known(v_usingTk_x3f_2742_, 1);
v___y_2754_ = v_val_2869_;
goto v___jp_2753_;
}
v___jp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2755_ = lean_mk_empty_array_with_capacity(v___x_2723_);
v___x_2756_ = lean_array_push(v___x_2755_, v_tk_2724_);
v___x_2757_ = lean_array_push(v___x_2756_, v___y_2754_);
v___x_2758_ = lean_box(2);
lean_inc(v___x_2725_);
v___x_2759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___x_2725_);
lean_ctor_set(v___x_2759_, 2, v___x_2757_);
v___x_2760_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2759_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___f_2762_; lean_object* v___x_2763_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v___f_2762_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2762_, 0, v_a_2761_);
v___x_2763_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2745_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; size_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = lean_mk_empty_array_with_capacity(v___x_2726_);
v___x_2766_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2726_, 3);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___x_2726_);
v___x_2768_ = lean_unsigned_to_nat(32u);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2768_);
v___x_2770_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2771_ = ((size_t)5ULL);
v___x_2772_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2772_, 0, v___x_2770_);
lean_ctor_set(v___x_2772_, 1, v___x_2769_);
lean_ctor_set(v___x_2772_, 2, v___x_2726_);
lean_ctor_set(v___x_2772_, 3, v___x_2726_);
lean_ctor_set_usize(v___x_2772_, 4, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2766_);
lean_ctor_set(v___x_2773_, 1, v___x_2766_);
lean_ctor_set(v___x_2773_, 2, v___x_2766_);
lean_ctor_set(v___x_2773_, 3, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2767_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
lean_inc_ref(v___x_2774_);
lean_inc(v_discharge_x3f_2743_);
lean_inc_ref(v_simprocs_2728_);
lean_inc_ref(v___x_2727_);
v___x_2775_ = l_Lean_Meta_simpGoal(v_a_2764_, v___x_2727_, v_simprocs_2728_, v_discharge_x3f_2743_, v___x_2729_, v___x_2765_, v___x_2774_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v_fst_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v_fst_2777_ = lean_ctor_get(v_a_2776_, 0);
if (lean_obj_tag(v_fst_2777_) == 1)
{
lean_object* v_val_2778_; lean_object* v_snd_2779_; lean_object* v_snd_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref_known(v___x_2774_, 2);
v_val_2778_ = lean_ctor_get(v_fst_2777_, 0);
lean_inc(v_val_2778_);
v_snd_2779_ = lean_ctor_get(v_a_2776_, 1);
lean_inc(v_snd_2779_);
lean_dec(v_a_2776_);
v_snd_2780_ = lean_ctor_get(v_val_2778_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_val_2778_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v_val_2778_, 0);
lean_dec(v_unused_2804_);
v___x_2782_ = v_val_2778_;
v_isShared_2783_ = v_isSharedCheck_2803_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_snd_2780_);
lean_dec(v_val_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2803_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___y_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2784_ = lean_box(v___x_2729_);
v___x_2785_ = lean_box(v___x_2732_);
v___x_2786_ = lean_box(v_useReducible_2733_);
v___x_2787_ = lean_box(v___x_2734_);
lean_inc_n(v_snd_2780_, 2);
v___y_2788_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2788_, 0, v_usingArg_2730_);
lean_closure_set(v___y_2788_, 1, v_snd_2780_);
lean_closure_set(v___y_2788_, 2, v___x_2784_);
lean_closure_set(v___y_2788_, 3, v___x_2731_);
lean_closure_set(v___y_2788_, 4, v___x_2785_);
lean_closure_set(v___y_2788_, 5, v___x_2786_);
lean_closure_set(v___y_2788_, 6, v___x_2787_);
lean_closure_set(v___y_2788_, 7, v___x_2735_);
lean_closure_set(v___y_2788_, 8, v___x_2727_);
lean_closure_set(v___y_2788_, 9, v_simprocs_2728_);
lean_closure_set(v___y_2788_, 10, v_discharge_x3f_2743_);
lean_closure_set(v___y_2788_, 11, v_snd_2779_);
lean_closure_set(v___y_2788_, 12, v___f_2736_);
lean_closure_set(v___y_2788_, 13, v___x_2737_);
lean_closure_set(v___y_2788_, 14, v___x_2738_);
lean_closure_set(v___y_2788_, 15, v___x_2739_);
lean_closure_set(v___y_2788_, 16, v___x_2725_);
lean_closure_set(v___y_2788_, 17, v___f_2740_);
lean_closure_set(v___y_2788_, 18, v_a_2741_);
lean_closure_set(v___y_2788_, 19, v___x_2726_);
lean_closure_set(v___y_2788_, 20, v___f_2762_);
v___x_2789_ = lean_box(0);
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 1);
lean_ctor_set(v___x_2782_, 1, v___x_2789_);
lean_ctor_set(v___x_2782_, 0, v_snd_2780_);
v___x_2791_ = v___x_2782_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_snd_2780_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2791_, v___y_2745_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v___x_2793_; 
lean_dec_ref_known(v___x_2792_, 1);
v___x_2793_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_snd_2780_, v___y_2788_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
return v___x_2793_;
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v___y_2788_);
lean_dec(v_snd_2780_);
v_a_2794_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2792_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2792_);
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
else
{
lean_object* v___x_2805_; lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2776_);
lean_dec_ref(v___f_2762_);
lean_dec(v_discharge_x3f_2743_);
lean_dec_ref(v___x_2739_);
lean_dec_ref(v___x_2738_);
lean_dec_ref(v___x_2737_);
lean_dec_ref(v___f_2736_);
lean_dec(v___x_2735_);
lean_dec_ref(v___x_2731_);
lean_dec(v_usingArg_2730_);
lean_dec_ref(v_simprocs_2728_);
lean_dec_ref(v___x_2727_);
lean_dec(v___x_2726_);
lean_dec(v___x_2725_);
v___x_2805_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2843_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2843_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
uint8_t v___x_2810_; 
v___x_2810_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2806_);
lean_dec(v_a_2806_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref(v_a_2741_);
lean_dec_ref(v___f_2740_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2774_);
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2774_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
else
{
lean_object* v_ref_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_del_object(v___x_2808_);
v_ref_2814_ = lean_ctor_get(v___y_2750_, 2);
v___x_2815_ = lean_box(0);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
v___x_2816_ = lean_apply_10(v___f_2740_, v___x_2815_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, lean_box(0));
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
lean_inc(v_ref_2814_);
v___x_2818_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2741_, v_ref_2814_, v_a_2817_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2818_, 0);
lean_dec(v_unused_2826_);
v___x_2820_ = v___x_2818_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_dec(v___x_2818_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2774_);
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2774_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref_known(v___x_2774_, 2);
v_a_2827_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2818_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2818_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref_known(v___x_2774_, 2);
lean_dec_ref(v_a_2741_);
v_a_2835_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2816_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2816_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref_known(v___x_2774_, 2);
lean_dec_ref(v___f_2762_);
lean_dec(v_discharge_x3f_2743_);
lean_dec_ref(v_a_2741_);
lean_dec_ref(v___f_2740_);
lean_dec_ref(v___x_2739_);
lean_dec_ref(v___x_2738_);
lean_dec_ref(v___x_2737_);
lean_dec_ref(v___f_2736_);
lean_dec(v___x_2735_);
lean_dec_ref(v___x_2731_);
lean_dec(v_usingArg_2730_);
lean_dec_ref(v_simprocs_2728_);
lean_dec_ref(v___x_2727_);
lean_dec(v___x_2726_);
lean_dec(v___x_2725_);
v_a_2844_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2775_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2775_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v___f_2762_);
lean_dec(v_discharge_x3f_2743_);
lean_dec_ref(v_a_2741_);
lean_dec_ref(v___f_2740_);
lean_dec_ref(v___x_2739_);
lean_dec_ref(v___x_2738_);
lean_dec_ref(v___x_2737_);
lean_dec_ref(v___f_2736_);
lean_dec(v___x_2735_);
lean_dec_ref(v___x_2731_);
lean_dec(v_usingArg_2730_);
lean_dec_ref(v_simprocs_2728_);
lean_dec_ref(v___x_2727_);
lean_dec(v___x_2726_);
lean_dec(v___x_2725_);
v_a_2852_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2763_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2763_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_discharge_x3f_2743_);
lean_dec_ref(v_a_2741_);
lean_dec_ref(v___f_2740_);
lean_dec_ref(v___x_2739_);
lean_dec_ref(v___x_2738_);
lean_dec_ref(v___x_2737_);
lean_dec_ref(v___f_2736_);
lean_dec(v___x_2735_);
lean_dec_ref(v___x_2731_);
lean_dec(v_usingArg_2730_);
lean_dec_ref(v_simprocs_2728_);
lean_dec_ref(v___x_2727_);
lean_dec(v___x_2726_);
lean_dec(v___x_2725_);
v_a_2860_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2760_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2760_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2723_ = stack[0].m_obj;
lean_object* v_tk_2724_ = stack[1].m_obj;
lean_object* v___x_2725_ = stack[2].m_obj;
lean_object* v___x_2726_ = stack[3].m_obj;
lean_object* v___x_2727_ = stack[4].m_obj;
lean_object* v_simprocs_2728_ = stack[5].m_obj;
uint8_t v___x_2729_ = stack[6].m_num;
lean_object* v_usingArg_2730_ = stack[7].m_obj;
lean_object* v___x_2731_ = stack[8].m_obj;
uint8_t v___x_2732_ = stack[9].m_num;
uint8_t v_useReducible_2733_ = stack[10].m_num;
uint8_t v___x_2734_ = stack[11].m_num;
lean_object* v___x_2735_ = stack[12].m_obj;
lean_object* v___f_2736_ = stack[13].m_obj;
lean_object* v___x_2737_ = stack[14].m_obj;
lean_object* v___x_2738_ = stack[15].m_obj;
lean_object* v___x_2739_ = stack[16].m_obj;
lean_object* v___f_2740_ = stack[17].m_obj;
lean_object* v_a_2741_ = stack[18].m_obj;
lean_object* v_usingTk_x3f_2742_ = stack[19].m_obj;
lean_object* v_discharge_x3f_2743_ = stack[20].m_obj;
lean_object* v___y_2744_ = stack[21].m_obj;
lean_object* v___y_2745_ = stack[22].m_obj;
lean_object* v___y_2746_ = stack[23].m_obj;
lean_object* v___y_2747_ = stack[24].m_obj;
lean_object* v___y_2748_ = stack[25].m_obj;
lean_object* v___y_2749_ = stack[26].m_obj;
lean_object* v___y_2750_ = stack[27].m_obj;
lean_object* v___y_2751_ = stack[28].m_obj;
lean_object* v_res_2870_;
v_res_2870_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2723_, v_tk_2724_, v___x_2725_, v___x_2726_, v___x_2727_, v_simprocs_2728_, v___x_2729_, v_usingArg_2730_, v___x_2731_, v___x_2732_, v_useReducible_2733_, v___x_2734_, v___x_2735_, v___f_2736_, v___x_2737_, v___x_2738_, v___x_2739_, v___f_2740_, v_a_2741_, v_usingTk_x3f_2742_, v_discharge_x3f_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
stack->m_obj
 = v_res_2870_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v___x_2871_ = _args[0];
lean_object* v_tk_2872_ = _args[1];
lean_object* v___x_2873_ = _args[2];
lean_object* v___x_2874_ = _args[3];
lean_object* v___x_2875_ = _args[4];
lean_object* v_simprocs_2876_ = _args[5];
lean_object* v___x_2877_ = _args[6];
lean_object* v_usingArg_2878_ = _args[7];
lean_object* v___x_2879_ = _args[8];
lean_object* v___x_2880_ = _args[9];
lean_object* v_useReducible_2881_ = _args[10];
lean_object* v___x_2882_ = _args[11];
lean_object* v___x_2883_ = _args[12];
lean_object* v___f_2884_ = _args[13];
lean_object* v___x_2885_ = _args[14];
lean_object* v___x_2886_ = _args[15];
lean_object* v___x_2887_ = _args[16];
lean_object* v___f_2888_ = _args[17];
lean_object* v_a_2889_ = _args[18];
lean_object* v_usingTk_x3f_2890_ = _args[19];
lean_object* v_discharge_x3f_2891_ = _args[20];
lean_object* v___y_2892_ = _args[21];
lean_object* v___y_2893_ = _args[22];
lean_object* v___y_2894_ = _args[23];
lean_object* v___y_2895_ = _args[24];
lean_object* v___y_2896_ = _args[25];
lean_object* v___y_2897_ = _args[26];
lean_object* v___y_2898_ = _args[27];
lean_object* v___y_2899_ = _args[28];
lean_object* v___y_2900_ = _args[29];
_start:
{
uint8_t v___x_98441__boxed_2901_; uint8_t v___x_98443__boxed_2902_; uint8_t v_useReducible_boxed_2903_; uint8_t v___x_98444__boxed_2904_; lean_object* v_res_2905_; 
v___x_98441__boxed_2901_ = lean_unbox(v___x_2877_);
v___x_98443__boxed_2902_ = lean_unbox(v___x_2880_);
v_useReducible_boxed_2903_ = lean_unbox(v_useReducible_2881_);
v___x_98444__boxed_2904_ = lean_unbox(v___x_2882_);
v_res_2905_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2871_, v_tk_2872_, v___x_2873_, v___x_2874_, v___x_2875_, v_simprocs_2876_, v___x_98441__boxed_2901_, v_usingArg_2878_, v___x_2879_, v___x_98443__boxed_2902_, v_useReducible_boxed_2903_, v___x_98444__boxed_2904_, v___x_2883_, v___f_2884_, v___x_2885_, v___x_2886_, v___x_2887_, v___f_2888_, v_a_2889_, v_usingTk_x3f_2890_, v_discharge_x3f_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___x_2871_);
return v_res_2905_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2911_ = lean_unsigned_to_nat(38u);
v___x_2912_ = lean_unsigned_to_nat(159u);
v___x_2913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2915_ = l_mkPanicMessageWithDecl(v___x_2914_, v___x_2913_, v___x_2912_, v___x_2911_, v___x_2910_);
return v___x_2915_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2924_ = lean_unsigned_to_nat(15u);
v___x_2925_ = lean_unsigned_to_nat(160u);
v___x_2926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2928_ = l_mkPanicMessageWithDecl(v___x_2927_, v___x_2926_, v___x_2925_, v___x_2924_, v___x_2923_);
return v___x_2928_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object* v_tk_2930_, lean_object* v___x_2931_, lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v___x_2934_, uint8_t v___x_2935_, lean_object* v___x_2936_, lean_object* v___x_2937_, uint8_t v_useReducible_2938_, lean_object* v___f_2939_, lean_object* v___x_2940_, lean_object* v___x_2941_, lean_object* v___x_2942_, lean_object* v___x_2943_, lean_object* v___x_2944_, lean_object* v___x_2945_, lean_object* v_usingArg_2946_, lean_object* v___x_2947_, uint8_t v___x_2948_, lean_object* v___f_2949_, lean_object* v_usingTk_x3f_2950_, lean_object* v_squeeze_2951_, lean_object* v_unfold_2952_, lean_object* v_args_2953_, lean_object* v_only_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___y_2966_; lean_object* v___y_2970_; lean_object* v_stx_2971_; lean_object* v___y_2972_; lean_object* v_ref_2973_; lean_object* v___y_2974_; lean_object* v___y_2993_; lean_object* v_stx_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2957_, v___y_2959_, v___y_2961_, v___y_2963_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v_ref_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; uint8_t v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; uint8_t v___y_3435_; lean_object* v___y_3436_; lean_object* v_args_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; uint8_t v___y_3475_; lean_object* v___y_3476_; lean_object* v_only_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3505_; lean_object* v___y_3506_; uint8_t v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3565_; lean_object* v___y_3566_; uint8_t v___y_3567_; lean_object* v___y_3578_; lean_object* v___y_3579_; uint8_t v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3583_; lean_object* v___y_3584_; uint8_t v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3656_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v_ref_3021_ = lean_ctor_get(v___y_2962_, 2);
v___x_3022_ = 0;
v___x_3023_ = l_Lean_SourceInfo_fromRef(v_ref_3021_, v___x_3022_);
v___x_3024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
lean_inc_ref(v___x_2933_);
lean_inc_ref(v___x_2932_);
lean_inc_ref(v___x_2931_);
v___x_3025_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3024_);
lean_inc(v___x_3023_);
v___x_3026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3023_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
v___x_3027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_3028_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_2955_) == 0)
{
lean_object* v___x_3665_; 
v___x_3665_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3656_ = v___x_3665_;
goto v___jp_3655_;
}
else
{
lean_object* v_val_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_val_3666_ = lean_ctor_get(v___y_2955_, 0);
lean_inc(v_val_3666_);
lean_dec_ref_known(v___y_2955_, 1);
v___x_3667_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_3668_ = lean_array_push(v___x_3667_, v_val_3666_);
v___y_3656_ = v___x_3668_;
goto v___jp_3655_;
}
v___jp_3029_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3041_ = l_Array_append___redArg(v___x_3028_, v___y_3040_);
lean_dec_ref(v___y_3040_);
lean_inc_n(v___y_3033_, 2);
v___x_3042_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3042_, 0, v___y_3033_);
lean_ctor_set(v___x_3042_, 1, v___x_3027_);
lean_ctor_set(v___x_3042_, 2, v___x_3041_);
v___x_3043_ = l_Lean_Syntax_node5(v___y_3033_, v___x_2936_, v___y_3030_, v___y_3036_, v___y_3035_, v___y_3039_, v___x_3042_);
v___x_3044_ = l_Lean_Syntax_node2(v___y_3033_, v___y_3038_, v___y_3031_, v___x_3043_);
v___y_2993_ = v___y_3032_;
v_stx_2994_ = v___x_3044_;
v___y_2995_ = v___y_3034_;
v___y_2996_ = v___y_3037_;
goto v___jp_2992_;
}
v___jp_3045_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = l_Array_append___redArg(v___x_3028_, v___y_3056_);
lean_dec_ref(v___y_3056_);
lean_inc(v___y_3049_);
v___x_3058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3058_, 0, v___y_3049_);
lean_ctor_set(v___x_3058_, 1, v___x_3027_);
lean_ctor_set(v___x_3058_, 2, v___x_3057_);
if (lean_obj_tag(v___y_3055_) == 1)
{
lean_object* v_val_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
lean_dec(v___x_2934_);
v_val_3059_ = lean_ctor_get(v___y_3055_, 0);
lean_inc(v_val_3059_);
lean_dec_ref_known(v___y_3055_, 1);
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3049_);
v___x_3061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___y_3049_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_Array_mkArray2___redArg(v___x_3061_, v_val_3059_);
v___y_3030_ = v___y_3046_;
v___y_3031_ = v___y_3047_;
v___y_3032_ = v___y_3048_;
v___y_3033_ = v___y_3049_;
v___y_3034_ = v___y_3051_;
v___y_3035_ = v___y_3050_;
v___y_3036_ = v___y_3052_;
v___y_3037_ = v___y_3054_;
v___y_3038_ = v___y_3053_;
v___y_3039_ = v___x_3058_;
v___y_3040_ = v___x_3062_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3063_; 
lean_dec(v___y_3055_);
v___x_3063_ = lean_mk_empty_array_with_capacity(v___x_2934_);
lean_dec(v___x_2934_);
v___y_3030_ = v___y_3046_;
v___y_3031_ = v___y_3047_;
v___y_3032_ = v___y_3048_;
v___y_3033_ = v___y_3049_;
v___y_3034_ = v___y_3051_;
v___y_3035_ = v___y_3050_;
v___y_3036_ = v___y_3052_;
v___y_3037_ = v___y_3054_;
v___y_3038_ = v___y_3053_;
v___y_3039_ = v___x_3058_;
v___y_3040_ = v___x_3063_;
goto v___jp_3029_;
}
}
v___jp_3064_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = l_Array_append___redArg(v___x_3028_, v___y_3075_);
lean_dec_ref(v___y_3075_);
lean_inc(v___y_3068_);
v___x_3077_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3077_, 0, v___y_3068_);
lean_ctor_set(v___x_3077_, 1, v___x_3027_);
lean_ctor_set(v___x_3077_, 2, v___x_3076_);
if (lean_obj_tag(v___y_3069_) == 1)
{
lean_object* v_val_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_val_3078_ = lean_ctor_get(v___y_3069_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v___y_3069_, 1);
v___x_3079_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3080_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3079_);
v___x_3081_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3068_, 4);
v___x_3082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___y_3068_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = l_Array_append___redArg(v___x_3028_, v_val_3078_);
lean_dec(v_val_3078_);
v___x_3084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3084_, 0, v___y_3068_);
lean_ctor_set(v___x_3084_, 1, v___x_3027_);
lean_ctor_set(v___x_3084_, 2, v___x_3083_);
v___x_3085_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___y_3068_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = l_Lean_Syntax_node3(v___y_3068_, v___x_3080_, v___x_3082_, v___x_3084_, v___x_3086_);
v___x_3088_ = l_Array_mkArray1___redArg(v___x_3087_);
v___y_3046_ = v___y_3065_;
v___y_3047_ = v___y_3066_;
v___y_3048_ = v___y_3067_;
v___y_3049_ = v___y_3068_;
v___y_3050_ = v___x_3077_;
v___y_3051_ = v___y_3070_;
v___y_3052_ = v___y_3071_;
v___y_3053_ = v___y_3073_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3074_;
v___y_3056_ = v___x_3088_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3089_; 
lean_dec(v___y_3069_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3089_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3046_ = v___y_3065_;
v___y_3047_ = v___y_3066_;
v___y_3048_ = v___y_3067_;
v___y_3049_ = v___y_3068_;
v___y_3050_ = v___x_3077_;
v___y_3051_ = v___y_3070_;
v___y_3052_ = v___y_3071_;
v___y_3053_ = v___y_3073_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3074_;
v___y_3056_ = v___x_3089_;
goto v___jp_3045_;
}
}
v___jp_3090_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = l_Array_append___redArg(v___x_3028_, v___y_3101_);
lean_dec_ref(v___y_3101_);
lean_inc(v___y_3095_);
v___x_3103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3103_, 0, v___y_3095_);
lean_ctor_set(v___x_3103_, 1, v___x_3027_);
lean_ctor_set(v___x_3103_, 2, v___x_3102_);
if (lean_obj_tag(v___y_3091_) == 1)
{
lean_object* v_val_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_val_3104_ = lean_ctor_get(v___y_3091_, 0);
lean_inc(v_val_3104_);
lean_dec_ref_known(v___y_3091_, 1);
v___x_3105_ = l_Lean_SourceInfo_fromRef(v_val_3104_, v___x_2935_);
lean_dec(v_val_3104_);
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3105_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = l_Array_mkArray1___redArg(v___x_3107_);
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___y_3094_;
v___y_3068_ = v___y_3095_;
v___y_3069_ = v___y_3096_;
v___y_3070_ = v___y_3097_;
v___y_3071_ = v___x_3103_;
v___y_3072_ = v___y_3099_;
v___y_3073_ = v___y_3098_;
v___y_3074_ = v___y_3100_;
v___y_3075_ = v___x_3108_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3109_; 
lean_dec(v___y_3091_);
v___x_3109_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3065_ = v___y_3092_;
v___y_3066_ = v___y_3093_;
v___y_3067_ = v___y_3094_;
v___y_3068_ = v___y_3095_;
v___y_3069_ = v___y_3096_;
v___y_3070_ = v___y_3097_;
v___y_3071_ = v___x_3103_;
v___y_3072_ = v___y_3099_;
v___y_3073_ = v___y_3098_;
v___y_3074_ = v___y_3100_;
v___y_3075_ = v___x_3109_;
goto v___jp_3064_;
}
}
v___jp_3110_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3125_ = l_Array_append___redArg(v___x_3028_, v___y_3124_);
lean_dec_ref(v___y_3124_);
lean_inc_n(v___y_3123_, 3);
v___x_3126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3126_, 0, v___y_3123_);
lean_ctor_set(v___x_3126_, 1, v___x_3027_);
lean_ctor_set(v___x_3126_, 2, v___x_3125_);
v___x_3127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___y_3123_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = l_Lean_Syntax_node6(v___y_3123_, v___y_3113_, v___y_3111_, v___y_3118_, v___y_3120_, v___x_3126_, v___x_3128_, v___y_3116_);
v___x_3130_ = l_Lean_Syntax_node4(v___y_3123_, v___y_3114_, v___y_3117_, v___y_3115_, v___y_3119_, v___x_3129_);
v___y_2993_ = v___y_3112_;
v_stx_2994_ = v___x_3130_;
v___y_2995_ = v___y_3121_;
v___y_2996_ = v___y_3122_;
goto v___jp_2992_;
}
v___jp_3131_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = l_Array_append___redArg(v___x_3028_, v___y_3145_);
lean_dec_ref(v___y_3145_);
lean_inc(v___y_3144_);
v___x_3147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3147_, 0, v___y_3144_);
lean_ctor_set(v___x_3147_, 1, v___x_3027_);
lean_ctor_set(v___x_3147_, 2, v___x_3146_);
if (lean_obj_tag(v___y_3134_) == 1)
{
lean_object* v_val_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec(v___x_2934_);
v_val_3148_ = lean_ctor_get(v___y_3134_, 0);
lean_inc(v_val_3148_);
lean_dec_ref_known(v___y_3134_, 1);
v___x_3149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3150_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3149_);
v___x_3151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3144_, 4);
v___x_3152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___y_3144_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Array_append___redArg(v___x_3028_, v_val_3148_);
lean_dec(v_val_3148_);
v___x_3154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3154_, 0, v___y_3144_);
lean_ctor_set(v___x_3154_, 1, v___x_3027_);
lean_ctor_set(v___x_3154_, 2, v___x_3153_);
v___x_3155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___y_3144_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l_Lean_Syntax_node3(v___y_3144_, v___x_3150_, v___x_3152_, v___x_3154_, v___x_3156_);
v___x_3158_ = l_Array_mkArray1___redArg(v___x_3157_);
v___y_3111_ = v___y_3132_;
v___y_3112_ = v___y_3133_;
v___y_3113_ = v___y_3135_;
v___y_3114_ = v___y_3136_;
v___y_3115_ = v___y_3137_;
v___y_3116_ = v___y_3138_;
v___y_3117_ = v___y_3139_;
v___y_3118_ = v___y_3140_;
v___y_3119_ = v___y_3141_;
v___y_3120_ = v___x_3147_;
v___y_3121_ = v___y_3142_;
v___y_3122_ = v___y_3143_;
v___y_3123_ = v___y_3144_;
v___y_3124_ = v___x_3158_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3159_; 
lean_dec(v___y_3134_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3159_ = lean_mk_empty_array_with_capacity(v___x_2934_);
lean_dec(v___x_2934_);
v___y_3111_ = v___y_3132_;
v___y_3112_ = v___y_3133_;
v___y_3113_ = v___y_3135_;
v___y_3114_ = v___y_3136_;
v___y_3115_ = v___y_3137_;
v___y_3116_ = v___y_3138_;
v___y_3117_ = v___y_3139_;
v___y_3118_ = v___y_3140_;
v___y_3119_ = v___y_3141_;
v___y_3120_ = v___x_3147_;
v___y_3121_ = v___y_3142_;
v___y_3122_ = v___y_3143_;
v___y_3123_ = v___y_3144_;
v___y_3124_ = v___x_3159_;
goto v___jp_3110_;
}
}
v___jp_3160_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = l_Array_append___redArg(v___x_3028_, v___y_3174_);
lean_dec_ref(v___y_3174_);
lean_inc(v___y_3173_);
v___x_3176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3173_);
lean_ctor_set(v___x_3176_, 1, v___x_3027_);
lean_ctor_set(v___x_3176_, 2, v___x_3175_);
if (lean_obj_tag(v___y_3161_) == 1)
{
lean_object* v_val_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_val_3177_ = lean_ctor_get(v___y_3161_, 0);
lean_inc(v_val_3177_);
lean_dec_ref_known(v___y_3161_, 1);
v___x_3178_ = l_Lean_SourceInfo_fromRef(v_val_3177_, v___x_2935_);
lean_dec(v_val_3177_);
v___x_3179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = l_Array_mkArray1___redArg(v___x_3180_);
v___y_3132_ = v___y_3162_;
v___y_3133_ = v___y_3163_;
v___y_3134_ = v___y_3164_;
v___y_3135_ = v___y_3165_;
v___y_3136_ = v___y_3166_;
v___y_3137_ = v___y_3167_;
v___y_3138_ = v___y_3168_;
v___y_3139_ = v___y_3169_;
v___y_3140_ = v___x_3176_;
v___y_3141_ = v___y_3170_;
v___y_3142_ = v___y_3171_;
v___y_3143_ = v___y_3172_;
v___y_3144_ = v___y_3173_;
v___y_3145_ = v___x_3181_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3182_; 
lean_dec(v___y_3161_);
v___x_3182_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3132_ = v___y_3162_;
v___y_3133_ = v___y_3163_;
v___y_3134_ = v___y_3164_;
v___y_3135_ = v___y_3165_;
v___y_3136_ = v___y_3166_;
v___y_3137_ = v___y_3167_;
v___y_3138_ = v___y_3168_;
v___y_3139_ = v___y_3169_;
v___y_3140_ = v___x_3176_;
v___y_3141_ = v___y_3170_;
v___y_3142_ = v___y_3171_;
v___y_3143_ = v___y_3172_;
v___y_3144_ = v___y_3173_;
v___y_3145_ = v___x_3182_;
goto v___jp_3131_;
}
}
v___jp_3183_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3195_ = l_Array_append___redArg(v___x_3028_, v___y_3194_);
lean_dec_ref(v___y_3194_);
lean_inc_n(v___y_3191_, 2);
v___x_3196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3196_, 0, v___y_3191_);
lean_ctor_set(v___x_3196_, 1, v___x_3027_);
lean_ctor_set(v___x_3196_, 2, v___x_3195_);
v___x_3197_ = l_Lean_Syntax_node5(v___y_3191_, v___x_2936_, v___y_3186_, v___y_3188_, v___y_3189_, v___y_3193_, v___x_3196_);
lean_inc(v___y_3184_);
v___x_3198_ = l_Lean_Syntax_node4(v___y_3191_, v___x_2937_, v___y_3185_, v___y_3184_, v___y_3184_, v___x_3197_);
v___y_2993_ = v___y_3187_;
v_stx_2994_ = v___x_3198_;
v___y_2995_ = v___y_3190_;
v___y_2996_ = v___y_3192_;
goto v___jp_2992_;
}
v___jp_3199_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = l_Array_append___redArg(v___x_3028_, v___y_3210_);
lean_dec_ref(v___y_3210_);
lean_inc(v___y_3207_);
v___x_3212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3212_, 0, v___y_3207_);
lean_ctor_set(v___x_3212_, 1, v___x_3027_);
lean_ctor_set(v___x_3212_, 2, v___x_3211_);
if (lean_obj_tag(v___y_3209_) == 1)
{
lean_object* v_val_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec(v___x_2934_);
v_val_3213_ = lean_ctor_get(v___y_3209_, 0);
lean_inc(v_val_3213_);
lean_dec_ref_known(v___y_3209_, 1);
v___x_3214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3207_);
v___x_3215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___y_3207_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = l_Array_mkArray2___redArg(v___x_3215_, v_val_3213_);
v___y_3184_ = v___y_3200_;
v___y_3185_ = v___y_3202_;
v___y_3186_ = v___y_3201_;
v___y_3187_ = v___y_3203_;
v___y_3188_ = v___y_3204_;
v___y_3189_ = v___y_3205_;
v___y_3190_ = v___y_3206_;
v___y_3191_ = v___y_3207_;
v___y_3192_ = v___y_3208_;
v___y_3193_ = v___x_3212_;
v___y_3194_ = v___x_3216_;
goto v___jp_3183_;
}
else
{
lean_object* v___x_3217_; 
lean_dec(v___y_3209_);
v___x_3217_ = lean_mk_empty_array_with_capacity(v___x_2934_);
lean_dec(v___x_2934_);
v___y_3184_ = v___y_3200_;
v___y_3185_ = v___y_3202_;
v___y_3186_ = v___y_3201_;
v___y_3187_ = v___y_3203_;
v___y_3188_ = v___y_3204_;
v___y_3189_ = v___y_3205_;
v___y_3190_ = v___y_3206_;
v___y_3191_ = v___y_3207_;
v___y_3192_ = v___y_3208_;
v___y_3193_ = v___x_3212_;
v___y_3194_ = v___x_3217_;
goto v___jp_3183_;
}
}
v___jp_3218_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = l_Array_append___redArg(v___x_3028_, v___y_3229_);
lean_dec_ref(v___y_3229_);
lean_inc(v___y_3226_);
v___x_3231_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3231_, 0, v___y_3226_);
lean_ctor_set(v___x_3231_, 1, v___x_3027_);
lean_ctor_set(v___x_3231_, 2, v___x_3230_);
if (lean_obj_tag(v___y_3224_) == 1)
{
lean_object* v_val_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_val_3232_ = lean_ctor_get(v___y_3224_, 0);
lean_inc(v_val_3232_);
lean_dec_ref_known(v___y_3224_, 1);
v___x_3233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3234_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3233_);
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3226_, 4);
v___x_3236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___y_3226_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = l_Array_append___redArg(v___x_3028_, v_val_3232_);
lean_dec(v_val_3232_);
v___x_3238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3238_, 0, v___y_3226_);
lean_ctor_set(v___x_3238_, 1, v___x_3027_);
lean_ctor_set(v___x_3238_, 2, v___x_3237_);
v___x_3239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___y_3226_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = l_Lean_Syntax_node3(v___y_3226_, v___x_3234_, v___x_3236_, v___x_3238_, v___x_3240_);
v___x_3242_ = l_Array_mkArray1___redArg(v___x_3241_);
v___y_3200_ = v___y_3219_;
v___y_3201_ = v___y_3221_;
v___y_3202_ = v___y_3220_;
v___y_3203_ = v___y_3222_;
v___y_3204_ = v___y_3223_;
v___y_3205_ = v___x_3231_;
v___y_3206_ = v___y_3225_;
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___y_3227_;
v___y_3209_ = v___y_3228_;
v___y_3210_ = v___x_3242_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3243_; 
lean_dec(v___y_3224_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3243_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3200_ = v___y_3219_;
v___y_3201_ = v___y_3221_;
v___y_3202_ = v___y_3220_;
v___y_3203_ = v___y_3222_;
v___y_3204_ = v___y_3223_;
v___y_3205_ = v___x_3231_;
v___y_3206_ = v___y_3225_;
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___y_3227_;
v___y_3209_ = v___y_3228_;
v___y_3210_ = v___x_3243_;
goto v___jp_3199_;
}
}
v___jp_3244_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = l_Array_append___redArg(v___x_3028_, v___y_3255_);
lean_dec_ref(v___y_3255_);
lean_inc(v___y_3252_);
v___x_3257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3257_, 0, v___y_3252_);
lean_ctor_set(v___x_3257_, 1, v___x_3027_);
lean_ctor_set(v___x_3257_, 2, v___x_3256_);
if (lean_obj_tag(v___y_3246_) == 1)
{
lean_object* v_val_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_val_3258_ = lean_ctor_get(v___y_3246_, 0);
lean_inc(v_val_3258_);
lean_dec_ref_known(v___y_3246_, 1);
v___x_3259_ = l_Lean_SourceInfo_fromRef(v_val_3258_, v___x_2935_);
lean_dec(v_val_3258_);
v___x_3260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3259_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = l_Array_mkArray1___redArg(v___x_3261_);
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3248_;
v___y_3221_ = v___y_3247_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___x_3257_;
v___y_3224_ = v___y_3250_;
v___y_3225_ = v___y_3251_;
v___y_3226_ = v___y_3252_;
v___y_3227_ = v___y_3253_;
v___y_3228_ = v___y_3254_;
v___y_3229_ = v___x_3262_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3263_; 
lean_dec(v___y_3246_);
v___x_3263_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3219_ = v___y_3245_;
v___y_3220_ = v___y_3248_;
v___y_3221_ = v___y_3247_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___x_3257_;
v___y_3224_ = v___y_3250_;
v___y_3225_ = v___y_3251_;
v___y_3226_ = v___y_3252_;
v___y_3227_ = v___y_3253_;
v___y_3228_ = v___y_3254_;
v___y_3229_ = v___x_3263_;
goto v___jp_3218_;
}
}
v___jp_3264_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3278_ = l_Array_append___redArg(v___x_3028_, v___y_3277_);
lean_dec_ref(v___y_3277_);
lean_inc_n(v___y_3266_, 3);
v___x_3279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3279_, 0, v___y_3266_);
lean_ctor_set(v___x_3279_, 1, v___x_3027_);
lean_ctor_set(v___x_3279_, 2, v___x_3278_);
v___x_3280_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___y_3266_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_Syntax_node6(v___y_3266_, v___y_3272_, v___y_3265_, v___y_3274_, v___y_3269_, v___x_3279_, v___x_3281_, v___y_3270_);
lean_inc(v___y_3276_);
v___x_3283_ = l_Lean_Syntax_node4(v___y_3266_, v___y_3268_, v___y_3271_, v___y_3276_, v___y_3276_, v___x_3282_);
v___y_2993_ = v___y_3267_;
v_stx_2994_ = v___x_3283_;
v___y_2995_ = v___y_3273_;
v___y_2996_ = v___y_3275_;
goto v___jp_2992_;
}
v___jp_3284_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = l_Array_append___redArg(v___x_3028_, v___y_3297_);
lean_dec_ref(v___y_3297_);
lean_inc(v___y_3286_);
v___x_3299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3299_, 0, v___y_3286_);
lean_ctor_set(v___x_3299_, 1, v___x_3027_);
lean_ctor_set(v___x_3299_, 2, v___x_3298_);
if (lean_obj_tag(v___y_3288_) == 1)
{
lean_object* v_val_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
lean_dec(v___x_2934_);
v_val_3300_ = lean_ctor_get(v___y_3288_, 0);
lean_inc(v_val_3300_);
lean_dec_ref_known(v___y_3288_, 1);
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3302_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3301_);
v___x_3303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3286_, 4);
v___x_3304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___y_3286_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Array_append___redArg(v___x_3028_, v_val_3300_);
lean_dec(v_val_3300_);
v___x_3306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3306_, 0, v___y_3286_);
lean_ctor_set(v___x_3306_, 1, v___x_3027_);
lean_ctor_set(v___x_3306_, 2, v___x_3305_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___y_3286_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_Syntax_node3(v___y_3286_, v___x_3302_, v___x_3304_, v___x_3306_, v___x_3308_);
v___x_3310_ = l_Array_mkArray1___redArg(v___x_3309_);
v___y_3265_ = v___y_3285_;
v___y_3266_ = v___y_3286_;
v___y_3267_ = v___y_3287_;
v___y_3268_ = v___y_3289_;
v___y_3269_ = v___x_3299_;
v___y_3270_ = v___y_3290_;
v___y_3271_ = v___y_3291_;
v___y_3272_ = v___y_3292_;
v___y_3273_ = v___y_3293_;
v___y_3274_ = v___y_3294_;
v___y_3275_ = v___y_3295_;
v___y_3276_ = v___y_3296_;
v___y_3277_ = v___x_3310_;
goto v___jp_3264_;
}
else
{
lean_object* v___x_3311_; 
lean_dec(v___y_3288_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3311_ = lean_mk_empty_array_with_capacity(v___x_2934_);
lean_dec(v___x_2934_);
v___y_3265_ = v___y_3285_;
v___y_3266_ = v___y_3286_;
v___y_3267_ = v___y_3287_;
v___y_3268_ = v___y_3289_;
v___y_3269_ = v___x_3299_;
v___y_3270_ = v___y_3290_;
v___y_3271_ = v___y_3291_;
v___y_3272_ = v___y_3292_;
v___y_3273_ = v___y_3293_;
v___y_3274_ = v___y_3294_;
v___y_3275_ = v___y_3295_;
v___y_3276_ = v___y_3296_;
v___y_3277_ = v___x_3311_;
goto v___jp_3264_;
}
}
v___jp_3312_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = l_Array_append___redArg(v___x_3028_, v___y_3325_);
lean_dec_ref(v___y_3325_);
lean_inc(v___y_3315_);
v___x_3327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3327_, 0, v___y_3315_);
lean_ctor_set(v___x_3327_, 1, v___x_3027_);
lean_ctor_set(v___x_3327_, 2, v___x_3326_);
if (lean_obj_tag(v___y_3313_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_val_3328_ = lean_ctor_get(v___y_3313_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v___y_3313_, 1);
v___x_3329_ = l_Lean_SourceInfo_fromRef(v_val_3328_, v___x_2935_);
lean_dec(v_val_3328_);
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = l_Array_mkArray1___redArg(v___x_3331_);
v___y_3285_ = v___y_3314_;
v___y_3286_ = v___y_3315_;
v___y_3287_ = v___y_3316_;
v___y_3288_ = v___y_3317_;
v___y_3289_ = v___y_3318_;
v___y_3290_ = v___y_3319_;
v___y_3291_ = v___y_3320_;
v___y_3292_ = v___y_3321_;
v___y_3293_ = v___y_3322_;
v___y_3294_ = v___x_3327_;
v___y_3295_ = v___y_3323_;
v___y_3296_ = v___y_3324_;
v___y_3297_ = v___x_3332_;
goto v___jp_3284_;
}
else
{
lean_object* v___x_3333_; 
lean_dec(v___y_3313_);
v___x_3333_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3285_ = v___y_3314_;
v___y_3286_ = v___y_3315_;
v___y_3287_ = v___y_3316_;
v___y_3288_ = v___y_3317_;
v___y_3289_ = v___y_3318_;
v___y_3290_ = v___y_3319_;
v___y_3291_ = v___y_3320_;
v___y_3292_ = v___y_3321_;
v___y_3293_ = v___y_3322_;
v___y_3294_ = v___x_3327_;
v___y_3295_ = v___y_3323_;
v___y_3296_ = v___y_3324_;
v___y_3297_ = v___x_3333_;
goto v___jp_3284_;
}
}
v___jp_3334_:
{
if (v___y_3342_ == 0)
{
if (v_useReducible_2938_ == 0)
{
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
if (lean_obj_tag(v___y_3343_) == 0)
{
lean_dec(v___y_3349_);
lean_dec(v___y_3340_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___y_2999_ = v___y_3338_;
v___y_3000_ = v___y_3337_;
v___y_3001_ = v___y_3344_;
v___y_3002_ = v___y_3339_;
v___y_3003_ = v___y_3345_;
v___y_3004_ = v___y_3341_;
v___y_3005_ = v___y_3348_;
v___y_3006_ = v___y_3346_;
v___y_3007_ = v___y_3347_;
goto v___jp_2998_;
}
else
{
lean_object* v_val_3350_; lean_object* v___x_3351_; 
v_val_3350_ = lean_ctor_get(v___y_3343_, 0);
lean_inc(v_val_3350_);
lean_dec_ref_known(v___y_3343_, 1);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
v___x_3351_ = lean_apply_9(v___f_2939_, v___y_3337_, v___y_3344_, v___y_3339_, v___y_3345_, v___y_3341_, v___y_3348_, v___y_3346_, v___y_3347_, lean_box(0));
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc_n(v_a_3352_, 3);
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2933_, 2);
lean_inc_ref_n(v___x_2932_, 2);
lean_inc_ref_n(v___x_2931_, 2);
v___x_3354_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_a_3352_);
lean_ctor_set(v___x_3355_, 1, v___x_2940_);
v___x_3356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3356_, 0, v_a_3352_);
lean_ctor_set(v___x_3356_, 1, v___x_3027_);
lean_ctor_set(v___x_3356_, 2, v___x_3028_);
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3358_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3357_);
if (lean_obj_tag(v___y_3349_) == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3313_ = v___y_3335_;
v___y_3314_ = v___y_3336_;
v___y_3315_ = v_a_3352_;
v___y_3316_ = v___y_3338_;
v___y_3317_ = v___y_3340_;
v___y_3318_ = v___x_3354_;
v___y_3319_ = v_val_3350_;
v___y_3320_ = v___x_3355_;
v___y_3321_ = v___x_3358_;
v___y_3322_ = v___y_3346_;
v___y_3323_ = v___y_3347_;
v___y_3324_ = v___x_3356_;
v___y_3325_ = v___x_3359_;
goto v___jp_3312_;
}
else
{
lean_object* v_val_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_val_3360_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v___y_3349_, 1);
v___x_3361_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_3362_ = lean_array_push(v___x_3361_, v_val_3360_);
v___y_3313_ = v___y_3335_;
v___y_3314_ = v___y_3336_;
v___y_3315_ = v_a_3352_;
v___y_3316_ = v___y_3338_;
v___y_3317_ = v___y_3340_;
v___y_3318_ = v___x_3354_;
v___y_3319_ = v_val_3350_;
v___y_3320_ = v___x_3355_;
v___y_3321_ = v___x_3358_;
v___y_3322_ = v___y_3346_;
v___y_3323_ = v___y_3347_;
v___y_3324_ = v___x_3356_;
v___y_3325_ = v___x_3362_;
goto v___jp_3312_;
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v_val_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___x_2940_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3363_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3351_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3351_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
else
{
lean_object* v___x_3371_; 
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
v___x_3371_ = lean_apply_9(v___f_2939_, v___y_3337_, v___y_3344_, v___y_3339_, v___y_3345_, v___y_3341_, v___y_3348_, v___y_3346_, v___y_3347_, lean_box(0));
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc_n(v_a_3372_, 3);
lean_dec_ref_known(v___x_3371_, 1);
v___x_3373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3373_, 0, v_a_3372_);
lean_ctor_set(v___x_3373_, 1, v___x_2940_);
v___x_3374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3374_, 0, v_a_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3027_);
lean_ctor_set(v___x_3374_, 2, v___x_3028_);
if (lean_obj_tag(v___y_3349_) == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3245_ = v___x_3374_;
v___y_3246_ = v___y_3335_;
v___y_3247_ = v___y_3336_;
v___y_3248_ = v___x_3373_;
v___y_3249_ = v___y_3338_;
v___y_3250_ = v___y_3340_;
v___y_3251_ = v___y_3346_;
v___y_3252_ = v_a_3372_;
v___y_3253_ = v___y_3347_;
v___y_3254_ = v___y_3343_;
v___y_3255_ = v___x_3375_;
goto v___jp_3244_;
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_val_3376_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v___y_3349_, 1);
v___x_3377_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_3378_ = lean_array_push(v___x_3377_, v_val_3376_);
v___y_3245_ = v___x_3374_;
v___y_3246_ = v___y_3335_;
v___y_3247_ = v___y_3336_;
v___y_3248_ = v___x_3373_;
v___y_3249_ = v___y_3338_;
v___y_3250_ = v___y_3340_;
v___y_3251_ = v___y_3346_;
v___y_3252_ = v_a_3372_;
v___y_3253_ = v___y_3347_;
v___y_3254_ = v___y_3343_;
v___y_3255_ = v___x_3378_;
goto v___jp_3244_;
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v___y_3349_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3343_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___x_2940_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3379_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3371_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3371_);
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
else
{
lean_dec(v___x_2937_);
if (v_useReducible_2938_ == 0)
{
lean_dec(v___x_2936_);
if (lean_obj_tag(v___y_3343_) == 0)
{
lean_dec(v___y_3349_);
lean_dec(v___y_3340_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___y_2999_ = v___y_3338_;
v___y_3000_ = v___y_3337_;
v___y_3001_ = v___y_3344_;
v___y_3002_ = v___y_3339_;
v___y_3003_ = v___y_3345_;
v___y_3004_ = v___y_3341_;
v___y_3005_ = v___y_3348_;
v___y_3006_ = v___y_3346_;
v___y_3007_ = v___y_3347_;
goto v___jp_2998_;
}
else
{
lean_object* v_val_3387_; lean_object* v___x_3388_; 
v_val_3387_ = lean_ctor_get(v___y_3343_, 0);
lean_inc(v_val_3387_);
lean_dec_ref_known(v___y_3343_, 1);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
v___x_3388_ = lean_apply_9(v___f_2939_, v___y_3337_, v___y_3344_, v___y_3339_, v___y_3345_, v___y_3341_, v___y_3348_, v___y_3346_, v___y_3347_, lean_box(0));
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc_n(v_a_3389_, 5);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2933_, 2);
lean_inc_ref_n(v___x_2932_, 2);
lean_inc_ref_n(v___x_2931_, 2);
v___x_3391_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3392_, 0, v_a_3389_);
lean_ctor_set(v___x_3392_, 1, v___x_2940_);
v___x_3393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3393_, 0, v_a_3389_);
lean_ctor_set(v___x_3393_, 1, v___x_3027_);
lean_ctor_set(v___x_3393_, 2, v___x_3028_);
v___x_3394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_a_3389_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = l_Lean_Syntax_node1(v_a_3389_, v___x_3027_, v___x_3395_);
v___x_3397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3398_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3397_);
if (lean_obj_tag(v___y_3349_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3161_ = v___y_3335_;
v___y_3162_ = v___y_3336_;
v___y_3163_ = v___y_3338_;
v___y_3164_ = v___y_3340_;
v___y_3165_ = v___x_3398_;
v___y_3166_ = v___x_3391_;
v___y_3167_ = v___x_3393_;
v___y_3168_ = v_val_3387_;
v___y_3169_ = v___x_3392_;
v___y_3170_ = v___x_3396_;
v___y_3171_ = v___y_3346_;
v___y_3172_ = v___y_3347_;
v___y_3173_ = v_a_3389_;
v___y_3174_ = v___x_3399_;
goto v___jp_3160_;
}
else
{
lean_object* v_val_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_val_3400_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_val_3400_);
lean_dec_ref_known(v___y_3349_, 1);
v___x_3401_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_3402_ = lean_array_push(v___x_3401_, v_val_3400_);
v___y_3161_ = v___y_3335_;
v___y_3162_ = v___y_3336_;
v___y_3163_ = v___y_3338_;
v___y_3164_ = v___y_3340_;
v___y_3165_ = v___x_3398_;
v___y_3166_ = v___x_3391_;
v___y_3167_ = v___x_3393_;
v___y_3168_ = v_val_3387_;
v___y_3169_ = v___x_3392_;
v___y_3170_ = v___x_3396_;
v___y_3171_ = v___y_3346_;
v___y_3172_ = v___y_3347_;
v___y_3173_ = v_a_3389_;
v___y_3174_ = v___x_3402_;
goto v___jp_3160_;
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_val_3387_);
lean_dec(v___y_3349_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___x_2940_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3403_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3388_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3388_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
else
{
lean_object* v___x_3411_; 
lean_dec_ref(v___x_2940_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
v___x_3411_ = lean_apply_9(v___f_2939_, v___y_3337_, v___y_3344_, v___y_3339_, v___y_3345_, v___y_3341_, v___y_3348_, v___y_3346_, v___y_3347_, lean_box(0));
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc_n(v_a_3412_, 2);
lean_dec_ref_known(v___x_3411_, 1);
v___x_3413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2933_);
lean_inc_ref(v___x_2932_);
lean_inc_ref(v___x_2931_);
v___x_3414_ = l_Lean_Name_mkStr4(v___x_2931_, v___x_2932_, v___x_2933_, v___x_3413_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3416_, 0, v_a_3412_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
if (lean_obj_tag(v___y_3349_) == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3091_ = v___y_3335_;
v___y_3092_ = v___y_3336_;
v___y_3093_ = v___x_3416_;
v___y_3094_ = v___y_3338_;
v___y_3095_ = v_a_3412_;
v___y_3096_ = v___y_3340_;
v___y_3097_ = v___y_3346_;
v___y_3098_ = v___x_3414_;
v___y_3099_ = v___y_3347_;
v___y_3100_ = v___y_3343_;
v___y_3101_ = v___x_3417_;
goto v___jp_3090_;
}
else
{
lean_object* v_val_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_val_3418_ = lean_ctor_get(v___y_3349_, 0);
lean_inc(v_val_3418_);
lean_dec_ref_known(v___y_3349_, 1);
v___x_3419_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___x_3420_ = lean_array_push(v___x_3419_, v_val_3418_);
v___y_3091_ = v___y_3335_;
v___y_3092_ = v___y_3336_;
v___y_3093_ = v___x_3416_;
v___y_3094_ = v___y_3338_;
v___y_3095_ = v_a_3412_;
v___y_3096_ = v___y_3340_;
v___y_3097_ = v___y_3346_;
v___y_3098_ = v___x_3414_;
v___y_3099_ = v___y_3347_;
v___y_3100_ = v___y_3343_;
v___y_3101_ = v___x_3420_;
goto v___jp_3090_;
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v___y_3349_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3343_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3421_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3411_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3411_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
v___jp_3429_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v___x_3446_ = lean_unsigned_to_nat(5u);
v___x_3447_ = l_Lean_Syntax_getArg(v___y_3431_, v___x_3446_);
lean_dec(v___y_3431_);
v___x_3448_ = l_Lean_Syntax_matchesNull(v___x_3447_, v___x_2934_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_dec(v_args_3437_);
lean_dec(v___y_3436_);
lean_dec(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3430_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3449_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3450_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3449_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___y_2993_ = v___y_3434_;
v_stx_2994_ = v_a_3451_;
v___y_2995_ = v___y_3444_;
v___y_2996_ = v___y_3445_;
goto v___jp_2992_;
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3434_);
lean_dec(v_tk_2930_);
v_a_3452_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3450_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3450_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_Syntax_getOptional_x3f(v___y_3430_);
lean_dec(v___y_3430_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_box(0);
v___y_3335_ = v___y_3432_;
v___y_3336_ = v___y_3433_;
v___y_3337_ = v___y_3438_;
v___y_3338_ = v___y_3434_;
v___y_3339_ = v___y_3440_;
v___y_3340_ = v_args_3437_;
v___y_3341_ = v___y_3442_;
v___y_3342_ = v___y_3435_;
v___y_3343_ = v___y_3436_;
v___y_3344_ = v___y_3439_;
v___y_3345_ = v___y_3441_;
v___y_3346_ = v___y_3444_;
v___y_3347_ = v___y_3445_;
v___y_3348_ = v___y_3443_;
v___y_3349_ = v___x_3461_;
goto v___jp_3334_;
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
v_val_3462_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3460_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v___x_3460_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_val_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
v___y_3335_ = v___y_3432_;
v___y_3336_ = v___y_3433_;
v___y_3337_ = v___y_3438_;
v___y_3338_ = v___y_3434_;
v___y_3339_ = v___y_3440_;
v___y_3340_ = v_args_3437_;
v___y_3341_ = v___y_3442_;
v___y_3342_ = v___y_3435_;
v___y_3343_ = v___y_3436_;
v___y_3344_ = v___y_3439_;
v___y_3345_ = v___y_3441_;
v___y_3346_ = v___y_3444_;
v___y_3347_ = v___y_3445_;
v___y_3348_ = v___y_3443_;
v___y_3349_ = v___x_3467_;
goto v___jp_3334_;
}
}
}
}
}
v___jp_3470_:
{
lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3486_ = l_Lean_Syntax_getArg(v___y_3471_, v___x_2941_);
v___x_3487_ = l_Lean_Syntax_isNone(v___x_3486_);
if (v___x_3487_ == 0)
{
uint8_t v___x_3488_; 
lean_inc(v___x_3486_);
v___x_3488_ = l_Lean_Syntax_matchesNull(v___x_3486_, v___x_2942_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec(v___x_3486_);
lean_dec(v_only_3477_);
lean_dec(v___y_3476_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3489_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3490_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3489_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___y_2993_ = v___y_3474_;
v_stx_2994_ = v_a_3491_;
v___y_2995_ = v___y_3484_;
v___y_2996_ = v___y_3485_;
goto v___jp_2992_;
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v___y_3474_);
lean_dec(v_tk_2930_);
v_a_3492_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3490_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = l_Lean_Syntax_getArg(v___x_3486_, v___x_2943_);
lean_dec(v___x_2943_);
lean_dec(v___x_3486_);
v___x_3501_ = l_Lean_Syntax_getArgs(v___x_3500_);
lean_dec(v___x_3500_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
v___y_3430_ = v___y_3472_;
v___y_3431_ = v___y_3471_;
v___y_3432_ = v_only_3477_;
v___y_3433_ = v___y_3473_;
v___y_3434_ = v___y_3474_;
v___y_3435_ = v___y_3475_;
v___y_3436_ = v___y_3476_;
v_args_3437_ = v___x_3502_;
v___y_3438_ = v___y_3478_;
v___y_3439_ = v___y_3479_;
v___y_3440_ = v___y_3480_;
v___y_3441_ = v___y_3481_;
v___y_3442_ = v___y_3482_;
v___y_3443_ = v___y_3483_;
v___y_3444_ = v___y_3484_;
v___y_3445_ = v___y_3485_;
goto v___jp_3429_;
}
}
else
{
lean_object* v___x_3503_; 
lean_dec(v___x_3486_);
lean_dec(v___x_2943_);
v___x_3503_ = lean_box(0);
v___y_3430_ = v___y_3472_;
v___y_3431_ = v___y_3471_;
v___y_3432_ = v_only_3477_;
v___y_3433_ = v___y_3473_;
v___y_3434_ = v___y_3474_;
v___y_3435_ = v___y_3475_;
v___y_3436_ = v___y_3476_;
v_args_3437_ = v___x_3503_;
v___y_3438_ = v___y_3478_;
v___y_3439_ = v___y_3479_;
v___y_3440_ = v___y_3480_;
v___y_3441_ = v___y_3481_;
v___y_3442_ = v___y_3482_;
v___y_3443_ = v___y_3483_;
v___y_3444_ = v___y_3484_;
v___y_3445_ = v___y_3485_;
goto v___jp_3429_;
}
}
v___jp_3504_:
{
lean_object* v_usedTheorems_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_usedTheorems_3509_ = lean_ctor_get(v___y_3505_, 0);
v___x_3510_ = l_Lean_Syntax_unsetTrailing(v___y_3506_);
v___x_3511_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3510_, v_usedTheorems_3509_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; uint8_t v___x_3513_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc_n(v_a_3512_, 2);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_Syntax_isOfKind(v_a_3512_, v___x_3025_);
lean_dec(v___x_3025_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_inc(v_ref_3021_);
lean_dec(v_a_3512_);
lean_dec(v___y_3508_);
lean_dec(v___x_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3514_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3515_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3514_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___y_2970_ = v___y_3505_;
v_stx_2971_ = v_a_3516_;
v___y_2972_ = v___y_2962_;
v_ref_2973_ = v_ref_3021_;
v___y_2974_ = v___y_2963_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v___y_3505_);
lean_dec(v_ref_3021_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v_tk_2930_);
v_a_3517_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3515_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3525_ = l_Lean_Syntax_getArg(v_a_3512_, v___x_2943_);
lean_inc(v___x_3525_);
v___x_3526_ = l_Lean_Syntax_isOfKind(v___x_3525_, v___x_2944_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_inc(v_ref_3021_);
lean_dec(v___x_3525_);
lean_dec(v_a_3512_);
lean_dec(v___y_3508_);
lean_dec(v___x_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3528_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3527_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___y_2970_ = v___y_3505_;
v_stx_2971_ = v_a_3529_;
v___y_2972_ = v___y_2962_;
v_ref_2973_ = v_ref_3021_;
v___y_2974_ = v___y_2963_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec_ref(v___y_3505_);
lean_dec(v_ref_3021_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v_tk_2930_);
v_a_3530_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3528_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3528_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3538_ = l_Lean_Syntax_getArg(v_a_3512_, v___x_2945_);
lean_dec(v___x_2945_);
v___x_3539_ = l_Lean_Syntax_getArg(v_a_3512_, v___x_2942_);
v___x_3540_ = l_Lean_Syntax_isNone(v___x_3539_);
if (v___x_3540_ == 0)
{
uint8_t v___x_3541_; 
lean_inc(v___x_3539_);
v___x_3541_ = l_Lean_Syntax_matchesNull(v___x_3539_, v___x_2943_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_inc(v_ref_3021_);
lean_dec(v___x_3539_);
lean_dec(v___x_3538_);
lean_dec(v___x_3525_);
lean_dec(v_a_3512_);
lean_dec(v___y_3508_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
v___x_3542_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3543_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3542_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___y_2970_ = v___y_3505_;
v_stx_2971_ = v_a_3544_;
v___y_2972_ = v___y_2962_;
v_ref_2973_ = v_ref_3021_;
v___y_2974_ = v___y_2963_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref(v___y_3505_);
lean_dec(v_ref_3021_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v_tk_2930_);
v_a_3545_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3543_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3543_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = l_Lean_Syntax_getArg(v___x_3539_, v___x_2934_);
lean_dec(v___x_3539_);
v___x_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
v___y_3471_ = v_a_3512_;
v___y_3472_ = v___x_3538_;
v___y_3473_ = v___x_3525_;
v___y_3474_ = v___y_3505_;
v___y_3475_ = v___y_3507_;
v___y_3476_ = v___y_3508_;
v_only_3477_ = v___x_3554_;
v___y_3478_ = v___y_2956_;
v___y_3479_ = v___y_2957_;
v___y_3480_ = v___y_2958_;
v___y_3481_ = v___y_2959_;
v___y_3482_ = v___y_2960_;
v___y_3483_ = v___y_2961_;
v___y_3484_ = v___y_2962_;
v___y_3485_ = v___y_2963_;
goto v___jp_3470_;
}
}
else
{
lean_object* v___x_3555_; 
lean_dec(v___x_3539_);
v___x_3555_ = lean_box(0);
v___y_3471_ = v_a_3512_;
v___y_3472_ = v___x_3538_;
v___y_3473_ = v___x_3525_;
v___y_3474_ = v___y_3505_;
v___y_3475_ = v___y_3507_;
v___y_3476_ = v___y_3508_;
v_only_3477_ = v___x_3555_;
v___y_3478_ = v___y_2956_;
v___y_3479_ = v___y_2957_;
v___y_3480_ = v___y_2958_;
v___y_3481_ = v___y_2959_;
v___y_3482_ = v___y_2960_;
v___y_3483_ = v___y_2961_;
v___y_3484_ = v___y_2962_;
v___y_3485_ = v___y_2963_;
goto v___jp_3470_;
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3505_);
lean_dec(v___x_3025_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___x_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3556_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3511_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3511_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
v___jp_3564_:
{
if (lean_obj_tag(v_usingArg_2946_) == 0)
{
v___y_3505_ = v___y_3565_;
v___y_3506_ = v___y_3566_;
v___y_3507_ = v___y_3567_;
v___y_3508_ = v_usingArg_2946_;
goto v___jp_3504_;
}
else
{
lean_object* v_val_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3576_; 
v_val_3568_ = lean_ctor_get(v_usingArg_2946_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_usingArg_2946_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3570_ = v_usingArg_2946_;
v_isShared_3571_ = v_isSharedCheck_3576_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_val_3568_);
lean_dec(v_usingArg_2946_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3576_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3572_ = l_Lean_Syntax_unsetTrailing(v_val_3568_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3572_);
v___x_3574_ = v___x_3570_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
v___y_3505_ = v___y_3565_;
v___y_3506_ = v___y_3566_;
v___y_3507_ = v___y_3567_;
v___y_3508_ = v___x_3574_;
goto v___jp_3504_;
}
}
}
}
v___jp_3577_:
{
if (v___y_3581_ == 0)
{
lean_dec(v___y_3579_);
lean_dec(v___x_3025_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_usingArg_2946_);
lean_dec(v___x_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v___y_2966_ = v___y_3578_;
goto v___jp_2965_;
}
else
{
v___y_3565_ = v___y_3578_;
v___y_3566_ = v___y_3579_;
v___y_3567_ = v___y_3580_;
goto v___jp_3564_;
}
}
v___jp_3582_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; 
v___x_3588_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3587_, v___x_3022_);
v___x_3589_ = lean_box(v___x_2935_);
v___x_3590_ = lean_box(v___x_3022_);
v___x_3591_ = lean_box(v_useReducible_2938_);
v___x_3592_ = lean_box(v___x_2948_);
lean_inc_ref(v___x_2933_);
lean_inc_ref(v___x_2932_);
lean_inc_ref(v___x_2931_);
lean_inc_ref(v___f_2939_);
lean_inc(v___x_2943_);
lean_inc_ref(v___x_2940_);
lean_inc(v_usingArg_2946_);
lean_inc(v___x_2934_);
lean_inc(v_tk_2930_);
lean_inc(v___x_2945_);
v___f_3593_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3593_, 0, v___x_2945_);
lean_closure_set(v___f_3593_, 1, v_tk_2930_);
lean_closure_set(v___f_3593_, 2, v___x_3027_);
lean_closure_set(v___f_3593_, 3, v___x_2934_);
lean_closure_set(v___f_3593_, 4, v___x_3588_);
lean_closure_set(v___f_3593_, 5, v___y_3583_);
lean_closure_set(v___f_3593_, 6, v___x_3589_);
lean_closure_set(v___f_3593_, 7, v_usingArg_2946_);
lean_closure_set(v___f_3593_, 8, v___x_2940_);
lean_closure_set(v___f_3593_, 9, v___x_3590_);
lean_closure_set(v___f_3593_, 10, v___x_3591_);
lean_closure_set(v___f_3593_, 11, v___x_3592_);
lean_closure_set(v___f_3593_, 12, v___x_2943_);
lean_closure_set(v___f_3593_, 13, v___f_2939_);
lean_closure_set(v___f_3593_, 14, v___x_2931_);
lean_closure_set(v___f_3593_, 15, v___x_2932_);
lean_closure_set(v___f_3593_, 16, v___x_2933_);
lean_closure_set(v___f_3593_, 17, v___f_2949_);
lean_closure_set(v___f_3593_, 18, v_a_3020_);
lean_closure_set(v___f_3593_, 19, v_usingTk_x3f_2950_);
v___x_3594_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3586_, v___f_3593_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_3586_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2962_);
v___x_3597_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3598_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_3596_, v___x_3597_);
lean_dec_ref(v___x_3596_);
if (v___x_3598_ == 0)
{
if (lean_obj_tag(v_squeeze_2951_) == 0)
{
v___y_3578_ = v_a_3595_;
v___y_3579_ = v___y_3584_;
v___y_3580_ = v___y_3585_;
v___y_3581_ = v___x_3598_;
goto v___jp_3577_;
}
else
{
v___y_3578_ = v_a_3595_;
v___y_3579_ = v___y_3584_;
v___y_3580_ = v___y_3585_;
v___y_3581_ = v___x_2948_;
goto v___jp_3577_;
}
}
else
{
v___y_3565_ = v_a_3595_;
v___y_3566_ = v___y_3584_;
v___y_3567_ = v___y_3585_;
goto v___jp_3564_;
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v___y_3584_);
lean_dec(v___x_3025_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_usingArg_2946_);
lean_dec(v___x_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3599_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3594_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3594_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
v___jp_3607_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3611_ = l_Array_append___redArg(v___x_3028_, v___y_3610_);
lean_dec_ref(v___y_3610_);
lean_inc_n(v___x_3023_, 2);
v___x_3612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3023_);
lean_ctor_set(v___x_3612_, 1, v___x_3027_);
lean_ctor_set(v___x_3612_, 2, v___x_3611_);
v___x_3613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3023_);
lean_ctor_set(v___x_3613_, 1, v___x_3027_);
lean_ctor_set(v___x_3613_, 2, v___x_3028_);
lean_inc(v___x_3025_);
v___x_3614_ = l_Lean_Syntax_node6(v___x_3023_, v___x_3025_, v___x_3026_, v___x_2947_, v___y_3609_, v___y_3608_, v___x_3612_, v___x_3613_);
v___x_3615_ = 0;
v___x_3616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3617_ = lean_box(v___x_3022_);
v___x_3618_ = lean_box(v___x_3615_);
v___x_3619_ = lean_box(v___x_3022_);
lean_inc(v___x_3614_);
v___x_3620_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3620_, 0, v___x_3614_);
lean_closure_set(v___x_3620_, 1, v___x_3617_);
lean_closure_set(v___x_3620_, 2, v___x_3618_);
lean_closure_set(v___x_3620_, 3, v___x_3619_);
lean_closure_set(v___x_3620_, 4, v___x_3616_);
v___x_3621_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3620_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3621_, 1);
if (lean_obj_tag(v_unfold_2952_) == 0)
{
lean_object* v_ctx_3623_; lean_object* v_simprocs_3624_; lean_object* v_dischargeWrapper_3625_; 
v_ctx_3623_ = lean_ctor_get(v_a_3622_, 0);
lean_inc_ref(v_ctx_3623_);
v_simprocs_3624_ = lean_ctor_get(v_a_3622_, 1);
lean_inc_ref(v_simprocs_3624_);
v_dischargeWrapper_3625_ = lean_ctor_get(v_a_3622_, 2);
lean_inc(v_dischargeWrapper_3625_);
lean_dec(v_a_3622_);
v___y_3583_ = v_simprocs_3624_;
v___y_3584_ = v___x_3614_;
v___y_3585_ = v___x_3022_;
v___y_3586_ = v_dischargeWrapper_3625_;
v___y_3587_ = v_ctx_3623_;
goto v___jp_3582_;
}
else
{
if (v___x_2948_ == 0)
{
lean_object* v_ctx_3626_; lean_object* v_simprocs_3627_; lean_object* v_dischargeWrapper_3628_; 
v_ctx_3626_ = lean_ctor_get(v_a_3622_, 0);
lean_inc_ref(v_ctx_3626_);
v_simprocs_3627_ = lean_ctor_get(v_a_3622_, 1);
lean_inc_ref(v_simprocs_3627_);
v_dischargeWrapper_3628_ = lean_ctor_get(v_a_3622_, 2);
lean_inc(v_dischargeWrapper_3628_);
lean_dec(v_a_3622_);
v___y_3583_ = v_simprocs_3627_;
v___y_3584_ = v___x_3614_;
v___y_3585_ = v___x_2948_;
v___y_3586_ = v_dischargeWrapper_3628_;
v___y_3587_ = v_ctx_3626_;
goto v___jp_3582_;
}
else
{
lean_object* v_ctx_3629_; lean_object* v_simprocs_3630_; lean_object* v_dischargeWrapper_3631_; lean_object* v___x_3632_; 
v_ctx_3629_ = lean_ctor_get(v_a_3622_, 0);
lean_inc_ref(v_ctx_3629_);
v_simprocs_3630_ = lean_ctor_get(v_a_3622_, 1);
lean_inc_ref(v_simprocs_3630_);
v_dischargeWrapper_3631_ = lean_ctor_get(v_a_3622_, 2);
lean_inc(v_dischargeWrapper_3631_);
lean_dec(v_a_3622_);
v___x_3632_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3629_);
v___y_3583_ = v_simprocs_3630_;
v___y_3584_ = v___x_3614_;
v___y_3585_ = v___x_2948_;
v___y_3586_ = v_dischargeWrapper_3631_;
v___y_3587_ = v___x_3632_;
goto v___jp_3582_;
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___x_3614_);
lean_dec(v___x_3025_);
lean_dec(v_a_3020_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v_usingTk_x3f_2950_);
lean_dec_ref(v___f_2949_);
lean_dec(v_usingArg_2946_);
lean_dec(v___x_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3633_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3621_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3621_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
v___jp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = l_Array_append___redArg(v___x_3028_, v___y_3643_);
lean_dec_ref(v___y_3643_);
lean_inc(v___x_3023_);
v___x_3645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3023_);
lean_ctor_set(v___x_3645_, 1, v___x_3027_);
lean_ctor_set(v___x_3645_, 2, v___x_3644_);
if (lean_obj_tag(v_args_2953_) == 1)
{
lean_object* v_val_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v_val_3646_ = lean_ctor_get(v_args_2953_, 0);
v___x_3647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_3023_, 3);
v___x_3648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3023_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = l_Array_append___redArg(v___x_3028_, v_val_3646_);
v___x_3650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3023_);
lean_ctor_set(v___x_3650_, 1, v___x_3027_);
lean_ctor_set(v___x_3650_, 2, v___x_3649_);
v___x_3651_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3023_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = l_Array_mkArray3___redArg(v___x_3648_, v___x_3650_, v___x_3652_);
v___y_3608_ = v___x_3645_;
v___y_3609_ = v___y_3642_;
v___y_3610_ = v___x_3653_;
goto v___jp_3607_;
}
else
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3608_ = v___x_3645_;
v___y_3609_ = v___y_3642_;
v___y_3610_ = v___x_3654_;
goto v___jp_3607_;
}
}
v___jp_3655_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = l_Array_append___redArg(v___x_3028_, v___y_3656_);
lean_dec_ref(v___y_3656_);
lean_inc(v___x_3023_);
v___x_3658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3023_);
lean_ctor_set(v___x_3658_, 1, v___x_3027_);
lean_ctor_set(v___x_3658_, 2, v___x_3657_);
if (lean_obj_tag(v_only_2954_) == 1)
{
lean_object* v_val_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_val_3659_ = lean_ctor_get(v_only_2954_, 0);
v___x_3660_ = l_Lean_SourceInfo_fromRef(v_val_3659_, v___x_2935_);
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = l_Array_mkArray1___redArg(v___x_3662_);
v___y_3642_ = v___x_3658_;
v___y_3643_ = v___x_3663_;
goto v___jp_3641_;
}
else
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_mk_empty_array_with_capacity(v___x_2934_);
v___y_3642_ = v___x_3658_;
v___y_3643_ = v___x_3664_;
goto v___jp_3641_;
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec(v_usingTk_x3f_2950_);
lean_dec_ref(v___f_2949_);
lean_dec(v___x_2947_);
lean_dec(v_usingArg_2946_);
lean_dec(v___x_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v___x_2940_);
lean_dec_ref(v___f_2939_);
lean_dec(v___x_2937_);
lean_dec(v___x_2936_);
lean_dec(v___x_2934_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v___x_2932_);
lean_dec_ref(v___x_2931_);
lean_dec(v_tk_2930_);
v_a_3669_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3019_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3019_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
v___jp_2965_:
{
lean_object* v_diag_2967_; lean_object* v___x_2968_; 
v_diag_2967_ = lean_ctor_get(v___y_2966_, 1);
lean_inc_ref(v_diag_2967_);
lean_dec_ref(v___y_2966_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v_diag_2967_);
return v___x_2968_;
}
v___jp_2969_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v_stx_2971_);
v___x_2977_ = lean_box(0);
v___x_2978_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
lean_ctor_set(v___x_2978_, 2, v___x_2977_);
lean_ctor_set(v___x_2978_, 3, v___x_2977_);
lean_ctor_set(v___x_2978_, 4, v___x_2977_);
lean_ctor_set(v___x_2978_, 5, v___x_2977_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_ref_2973_);
v___x_2980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0));
v___x_2981_ = 4;
v___x_2982_ = l_Lean_MessageData_nil;
v___x_2983_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2930_, v___x_2978_, v___x_2979_, v___x_2980_, v___x_2977_, v___x_2981_, v___x_2982_, v___y_2972_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2972_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_dec_ref_known(v___x_2983_, 1);
v___y_2966_ = v___y_2970_;
goto v___jp_2965_;
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v___y_2970_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
v___jp_2992_:
{
lean_object* v_ref_2997_; 
v_ref_2997_ = lean_ctor_get(v___y_2995_, 2);
lean_inc(v_ref_2997_);
v___y_2970_ = v___y_2993_;
v_stx_2971_ = v_stx_2994_;
v___y_2972_ = v___y_2995_;
v_ref_2973_ = v_ref_2997_;
v___y_2974_ = v___y_2996_;
goto v___jp_2969_;
}
v___jp_2998_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4);
v___x_3009_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3008_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___y_2993_ = v___y_2999_;
v_stx_2994_ = v_a_3010_;
v___y_2995_ = v___y_3006_;
v___y_2996_ = v___y_3007_;
goto v___jp_2992_;
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v___y_2999_);
lean_dec(v_tk_2930_);
v_a_3011_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_2930_ = stack[0].m_obj;
lean_object* v___x_2931_ = stack[1].m_obj;
lean_object* v___x_2932_ = stack[2].m_obj;
lean_object* v___x_2933_ = stack[3].m_obj;
lean_object* v___x_2934_ = stack[4].m_obj;
uint8_t v___x_2935_ = stack[5].m_num;
lean_object* v___x_2936_ = stack[6].m_obj;
lean_object* v___x_2937_ = stack[7].m_obj;
uint8_t v_useReducible_2938_ = stack[8].m_num;
lean_object* v___f_2939_ = stack[9].m_obj;
lean_object* v___x_2940_ = stack[10].m_obj;
lean_object* v___x_2941_ = stack[11].m_obj;
lean_object* v___x_2942_ = stack[12].m_obj;
lean_object* v___x_2943_ = stack[13].m_obj;
lean_object* v___x_2944_ = stack[14].m_obj;
lean_object* v___x_2945_ = stack[15].m_obj;
lean_object* v_usingArg_2946_ = stack[16].m_obj;
lean_object* v___x_2947_ = stack[17].m_obj;
uint8_t v___x_2948_ = stack[18].m_num;
lean_object* v___f_2949_ = stack[19].m_obj;
lean_object* v_usingTk_x3f_2950_ = stack[20].m_obj;
lean_object* v_squeeze_2951_ = stack[21].m_obj;
lean_object* v_unfold_2952_ = stack[22].m_obj;
lean_object* v_args_2953_ = stack[23].m_obj;
lean_object* v_only_2954_ = stack[24].m_obj;
lean_object* v___y_2955_ = stack[25].m_obj;
lean_object* v___y_2956_ = stack[26].m_obj;
lean_object* v___y_2957_ = stack[27].m_obj;
lean_object* v___y_2958_ = stack[28].m_obj;
lean_object* v___y_2959_ = stack[29].m_obj;
lean_object* v___y_2960_ = stack[30].m_obj;
lean_object* v___y_2961_ = stack[31].m_obj;
lean_object* v___y_2962_ = stack[32].m_obj;
lean_object* v___y_2963_ = stack[33].m_obj;
lean_object* v_res_3677_;
v_res_3677_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_2930_, v___x_2931_, v___x_2932_, v___x_2933_, v___x_2934_, v___x_2935_, v___x_2936_, v___x_2937_, v_useReducible_2938_, v___f_2939_, v___x_2940_, v___x_2941_, v___x_2942_, v___x_2943_, v___x_2944_, v___x_2945_, v_usingArg_2946_, v___x_2947_, v___x_2948_, v___f_2949_, v_usingTk_x3f_2950_, v_squeeze_2951_, v_unfold_2952_, v_args_2953_, v_only_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
stack->m_obj
 = v_res_3677_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object** _args){
lean_object* v_tk_3678_ = _args[0];
lean_object* v___x_3679_ = _args[1];
lean_object* v___x_3680_ = _args[2];
lean_object* v___x_3681_ = _args[3];
lean_object* v___x_3682_ = _args[4];
lean_object* v___x_3683_ = _args[5];
lean_object* v___x_3684_ = _args[6];
lean_object* v___x_3685_ = _args[7];
lean_object* v_useReducible_3686_ = _args[8];
lean_object* v___f_3687_ = _args[9];
lean_object* v___x_3688_ = _args[10];
lean_object* v___x_3689_ = _args[11];
lean_object* v___x_3690_ = _args[12];
lean_object* v___x_3691_ = _args[13];
lean_object* v___x_3692_ = _args[14];
lean_object* v___x_3693_ = _args[15];
lean_object* v_usingArg_3694_ = _args[16];
lean_object* v___x_3695_ = _args[17];
lean_object* v___x_3696_ = _args[18];
lean_object* v___f_3697_ = _args[19];
lean_object* v_usingTk_x3f_3698_ = _args[20];
lean_object* v_squeeze_3699_ = _args[21];
lean_object* v_unfold_3700_ = _args[22];
lean_object* v_args_3701_ = _args[23];
lean_object* v_only_3702_ = _args[24];
lean_object* v___y_3703_ = _args[25];
lean_object* v___y_3704_ = _args[26];
lean_object* v___y_3705_ = _args[27];
lean_object* v___y_3706_ = _args[28];
lean_object* v___y_3707_ = _args[29];
lean_object* v___y_3708_ = _args[30];
lean_object* v___y_3709_ = _args[31];
lean_object* v___y_3710_ = _args[32];
lean_object* v___y_3711_ = _args[33];
lean_object* v___y_3712_ = _args[34];
_start:
{
uint8_t v___x_99048__boxed_3713_; uint8_t v_useReducible_boxed_3714_; uint8_t v___x_99059__boxed_3715_; lean_object* v_res_3716_; 
v___x_99048__boxed_3713_ = lean_unbox(v___x_3683_);
v_useReducible_boxed_3714_ = lean_unbox(v_useReducible_3686_);
v___x_99059__boxed_3715_ = lean_unbox(v___x_3696_);
v_res_3716_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3678_, v___x_3679_, v___x_3680_, v___x_3681_, v___x_3682_, v___x_99048__boxed_3713_, v___x_3684_, v___x_3685_, v_useReducible_boxed_3714_, v___f_3687_, v___x_3688_, v___x_3689_, v___x_3690_, v___x_3691_, v___x_3692_, v___x_3693_, v_usingArg_3694_, v___x_3695_, v___x_99059__boxed_3715_, v___f_3697_, v_usingTk_x3f_3698_, v_squeeze_3699_, v_unfold_3700_, v_args_3701_, v_only_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v_only_3702_);
lean_dec(v_args_3701_);
lean_dec(v_unfold_3700_);
lean_dec(v_squeeze_3699_);
lean_dec(v___x_3692_);
lean_dec(v___x_3690_);
lean_dec(v___x_3689_);
return v_res_3716_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3742_, lean_object* v_stx_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3755_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_3756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3743_);
v___x_3758_ = l_Lean_Syntax_isOfKind(v_stx_3743_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; 
lean_dec(v_stx_3743_);
v___x_3759_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3759_;
}
else
{
lean_object* v___f_3760_; lean_object* v___x_3761_; lean_object* v_tk_3762_; lean_object* v___x_3763_; lean_object* v___y_3765_; uint8_t v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3797_; uint8_t v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v_usingTk_x3f_3817_; lean_object* v_usingArg_3818_; lean_object* v___y_3830_; uint8_t v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_args_3850_; uint8_t v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v_only_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v_unfold_3906_; lean_object* v_squeeze_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___f_3760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3761_ = lean_unsigned_to_nat(0u);
v_tk_3762_ = l_Lean_Syntax_getArg(v_stx_3743_, v___x_3761_);
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3942_ = l_Lean_Syntax_getArg(v_stx_3743_, v___x_3763_);
v___x_3943_ = l_Lean_Syntax_isNone(v___x_3942_);
if (v___x_3943_ == 0)
{
uint8_t v___x_3944_; 
lean_inc(v___x_3942_);
v___x_3944_ = l_Lean_Syntax_matchesNull(v___x_3942_, v___x_3763_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; 
lean_dec(v___x_3942_);
lean_dec(v_tk_3762_);
lean_dec(v_stx_3743_);
v___x_3945_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3945_;
}
else
{
lean_object* v_squeeze_3946_; lean_object* v___x_3947_; 
v_squeeze_3946_ = l_Lean_Syntax_getArg(v___x_3942_, v___x_3761_);
lean_dec(v___x_3942_);
v___x_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3947_, 0, v_squeeze_3946_);
v_squeeze_3925_ = v___x_3947_;
v___y_3926_ = v_a_3744_;
v___y_3927_ = v_a_3745_;
v___y_3928_ = v_a_3746_;
v___y_3929_ = v_a_3747_;
v___y_3930_ = v_a_3748_;
v___y_3931_ = v_a_3749_;
v___y_3932_ = v_a_3750_;
v___y_3933_ = v_a_3751_;
goto v___jp_3924_;
}
}
else
{
lean_object* v___x_3948_; 
lean_dec(v___x_3942_);
v___x_3948_ = lean_box(0);
v_squeeze_3925_ = v___x_3948_;
v___y_3926_ = v_a_3744_;
v___y_3927_ = v_a_3745_;
v___y_3928_ = v_a_3746_;
v___y_3929_ = v_a_3747_;
v___y_3930_ = v_a_3748_;
v___y_3931_ = v_a_3749_;
v___y_3932_ = v_a_3750_;
v___y_3933_ = v_a_3751_;
goto v___jp_3924_;
}
v___jp_3764_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___f_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___f_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3787_ = lean_box(v___x_3758_);
v___x_3788_ = lean_box(v___y_3766_);
lean_inc(v___y_3773_);
lean_inc(v___y_3781_);
lean_inc(v___y_3786_);
lean_inc(v___y_3777_);
lean_inc(v___y_3771_);
lean_inc(v___y_3768_);
v___f_3789_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 22, 12);
lean_closure_set(v___f_3789_, 0, v___y_3768_);
lean_closure_set(v___f_3789_, 1, v___x_3761_);
lean_closure_set(v___f_3789_, 2, v___y_3771_);
lean_closure_set(v___f_3789_, 3, v___y_3777_);
lean_closure_set(v___f_3789_, 4, v___x_3787_);
lean_closure_set(v___f_3789_, 5, v___x_3753_);
lean_closure_set(v___f_3789_, 6, v___x_3754_);
lean_closure_set(v___f_3789_, 7, v___x_3755_);
lean_closure_set(v___f_3789_, 8, v___y_3786_);
lean_closure_set(v___f_3789_, 9, v___y_3781_);
lean_closure_set(v___f_3789_, 10, v___x_3788_);
lean_closure_set(v___f_3789_, 11, v___y_3773_);
v___x_3790_ = lean_box(v___x_3758_);
v___x_3791_ = lean_box(v_useReducible_3742_);
v___x_3792_ = lean_box(v___y_3766_);
lean_inc(v___y_3770_);
lean_inc(v___y_3769_);
v___f_3793_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3793_, 0, v_tk_3762_);
lean_closure_set(v___f_3793_, 1, v___x_3753_);
lean_closure_set(v___f_3793_, 2, v___x_3754_);
lean_closure_set(v___f_3793_, 3, v___x_3755_);
lean_closure_set(v___f_3793_, 4, v___x_3761_);
lean_closure_set(v___f_3793_, 5, v___x_3790_);
lean_closure_set(v___f_3793_, 6, v___y_3769_);
lean_closure_set(v___f_3793_, 7, v___x_3757_);
lean_closure_set(v___f_3793_, 8, v___x_3791_);
lean_closure_set(v___f_3793_, 9, v___f_3760_);
lean_closure_set(v___f_3793_, 10, v___x_3756_);
lean_closure_set(v___f_3793_, 11, v___y_3784_);
lean_closure_set(v___f_3793_, 12, v___y_3774_);
lean_closure_set(v___f_3793_, 13, v___x_3763_);
lean_closure_set(v___f_3793_, 14, v___y_3770_);
lean_closure_set(v___f_3793_, 15, v___y_3783_);
lean_closure_set(v___f_3793_, 16, v___y_3767_);
lean_closure_set(v___f_3793_, 17, v___y_3768_);
lean_closure_set(v___f_3793_, 18, v___x_3792_);
lean_closure_set(v___f_3793_, 19, v___f_3789_);
lean_closure_set(v___f_3793_, 20, v___y_3778_);
lean_closure_set(v___f_3793_, 21, v___y_3773_);
lean_closure_set(v___f_3793_, 22, v___y_3781_);
lean_closure_set(v___f_3793_, 23, v___y_3771_);
lean_closure_set(v___f_3793_, 24, v___y_3777_);
lean_closure_set(v___f_3793_, 25, v___y_3786_);
v___x_3794_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3794_, 0, v___f_3793_);
v___x_3795_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3794_, v___y_3779_, v___y_3782_, v___y_3772_, v___y_3780_, v___y_3775_, v___y_3776_, v___y_3785_, v___y_3765_);
return v___x_3795_;
}
v___jp_3796_:
{
lean_object* v___x_3819_; 
v___x_3819_ = l_Lean_Syntax_getOptional_x3f(v___y_3816_);
lean_dec(v___y_3816_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_box(0);
v___y_3765_ = v___y_3797_;
v___y_3766_ = v___y_3798_;
v___y_3767_ = v_usingArg_3818_;
v___y_3768_ = v___y_3799_;
v___y_3769_ = v___y_3800_;
v___y_3770_ = v___y_3801_;
v___y_3771_ = v___y_3802_;
v___y_3772_ = v___y_3803_;
v___y_3773_ = v___y_3804_;
v___y_3774_ = v___y_3805_;
v___y_3775_ = v___y_3806_;
v___y_3776_ = v___y_3807_;
v___y_3777_ = v___y_3808_;
v___y_3778_ = v_usingTk_x3f_3817_;
v___y_3779_ = v___y_3809_;
v___y_3780_ = v___y_3811_;
v___y_3781_ = v___y_3810_;
v___y_3782_ = v___y_3813_;
v___y_3783_ = v___y_3812_;
v___y_3784_ = v___y_3814_;
v___y_3785_ = v___y_3815_;
v___y_3786_ = v___x_3820_;
goto v___jp_3764_;
}
else
{
lean_object* v_val_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
v_val_3821_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3819_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_val_3821_);
lean_dec(v___x_3819_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_val_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
v___y_3765_ = v___y_3797_;
v___y_3766_ = v___y_3798_;
v___y_3767_ = v_usingArg_3818_;
v___y_3768_ = v___y_3799_;
v___y_3769_ = v___y_3800_;
v___y_3770_ = v___y_3801_;
v___y_3771_ = v___y_3802_;
v___y_3772_ = v___y_3803_;
v___y_3773_ = v___y_3804_;
v___y_3774_ = v___y_3805_;
v___y_3775_ = v___y_3806_;
v___y_3776_ = v___y_3807_;
v___y_3777_ = v___y_3808_;
v___y_3778_ = v_usingTk_x3f_3817_;
v___y_3779_ = v___y_3809_;
v___y_3780_ = v___y_3811_;
v___y_3781_ = v___y_3810_;
v___y_3782_ = v___y_3813_;
v___y_3783_ = v___y_3812_;
v___y_3784_ = v___y_3814_;
v___y_3785_ = v___y_3815_;
v___y_3786_ = v___x_3826_;
goto v___jp_3764_;
}
}
}
}
v___jp_3829_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v___x_3851_ = lean_unsigned_to_nat(4u);
v___x_3852_ = l_Lean_Syntax_getArg(v___y_3847_, v___x_3851_);
lean_dec(v___y_3847_);
v___x_3853_ = l_Lean_Syntax_isNone(v___x_3852_);
if (v___x_3853_ == 0)
{
uint8_t v___x_3854_; 
lean_inc(v___x_3852_);
v___x_3854_ = l_Lean_Syntax_matchesNull(v___x_3852_, v___y_3841_);
lean_dec(v___y_3841_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; 
lean_dec(v___x_3852_);
lean_dec(v_args_3850_);
lean_dec(v___y_3849_);
lean_dec(v___y_3846_);
lean_dec(v___y_3844_);
lean_dec(v___y_3840_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3832_);
lean_dec(v_tk_3762_);
v___x_3855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3855_;
}
else
{
lean_object* v_usingTk_x3f_3856_; lean_object* v_usingArg_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_usingTk_x3f_3856_ = l_Lean_Syntax_getArg(v___x_3852_, v___x_3761_);
v_usingArg_3857_ = l_Lean_Syntax_getArg(v___x_3852_, v___x_3763_);
lean_dec(v___x_3852_);
v___x_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3858_, 0, v_usingTk_x3f_3856_);
v___x_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_usingArg_3857_);
v___y_3797_ = v___y_3830_;
v___y_3798_ = v___y_3831_;
v___y_3799_ = v___y_3832_;
v___y_3800_ = v___y_3833_;
v___y_3801_ = v___y_3834_;
v___y_3802_ = v_args_3850_;
v___y_3803_ = v___y_3835_;
v___y_3804_ = v___y_3836_;
v___y_3805_ = v___y_3837_;
v___y_3806_ = v___y_3838_;
v___y_3807_ = v___y_3839_;
v___y_3808_ = v___y_3840_;
v___y_3809_ = v___y_3842_;
v___y_3810_ = v___y_3844_;
v___y_3811_ = v___y_3843_;
v___y_3812_ = v___y_3846_;
v___y_3813_ = v___y_3845_;
v___y_3814_ = v___x_3851_;
v___y_3815_ = v___y_3848_;
v___y_3816_ = v___y_3849_;
v_usingTk_x3f_3817_ = v___x_3858_;
v_usingArg_3818_ = v___x_3859_;
goto v___jp_3796_;
}
}
else
{
lean_object* v___x_3860_; 
lean_dec(v___x_3852_);
lean_dec(v___y_3841_);
v___x_3860_ = lean_box(0);
v___y_3797_ = v___y_3830_;
v___y_3798_ = v___y_3831_;
v___y_3799_ = v___y_3832_;
v___y_3800_ = v___y_3833_;
v___y_3801_ = v___y_3834_;
v___y_3802_ = v_args_3850_;
v___y_3803_ = v___y_3835_;
v___y_3804_ = v___y_3836_;
v___y_3805_ = v___y_3837_;
v___y_3806_ = v___y_3838_;
v___y_3807_ = v___y_3839_;
v___y_3808_ = v___y_3840_;
v___y_3809_ = v___y_3842_;
v___y_3810_ = v___y_3844_;
v___y_3811_ = v___y_3843_;
v___y_3812_ = v___y_3846_;
v___y_3813_ = v___y_3845_;
v___y_3814_ = v___x_3851_;
v___y_3815_ = v___y_3848_;
v___y_3816_ = v___y_3849_;
v_usingTk_x3f_3817_ = v___x_3860_;
v_usingArg_3818_ = v___x_3860_;
goto v___jp_3796_;
}
}
v___jp_3861_:
{
lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3883_ = l_Lean_Syntax_getArg(v___y_3873_, v___y_3872_);
lean_dec(v___y_3872_);
v___x_3884_ = l_Lean_Syntax_isNone(v___x_3883_);
if (v___x_3884_ == 0)
{
uint8_t v___x_3885_; 
lean_inc(v___x_3883_);
v___x_3885_ = l_Lean_Syntax_matchesNull(v___x_3883_, v___x_3763_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; 
lean_dec(v___x_3883_);
lean_dec(v_only_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec(v___y_3863_);
lean_dec(v_tk_3762_);
v___x_3886_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3886_;
}
else
{
lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3887_ = l_Lean_Syntax_getArg(v___x_3883_, v___x_3761_);
lean_dec(v___x_3883_);
v___x_3888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3887_);
v___x_3889_ = l_Lean_Syntax_isOfKind(v___x_3887_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; 
lean_dec(v___x_3887_);
lean_dec(v_only_3874_);
lean_dec(v___y_3873_);
lean_dec(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec(v___y_3863_);
lean_dec(v_tk_3762_);
v___x_3890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3890_;
}
else
{
lean_object* v___x_3891_; lean_object* v_args_3892_; lean_object* v___x_3893_; 
v___x_3891_ = l_Lean_Syntax_getArg(v___x_3887_, v___x_3763_);
lean_dec(v___x_3887_);
v_args_3892_ = l_Lean_Syntax_getArgs(v___x_3891_);
lean_dec(v___x_3891_);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v_args_3892_);
v___y_3830_ = v___y_3882_;
v___y_3831_ = v___y_3862_;
v___y_3832_ = v___y_3863_;
v___y_3833_ = v___y_3864_;
v___y_3834_ = v___y_3865_;
v___y_3835_ = v___y_3877_;
v___y_3836_ = v___y_3868_;
v___y_3837_ = v___y_3869_;
v___y_3838_ = v___y_3879_;
v___y_3839_ = v___y_3880_;
v___y_3840_ = v_only_3874_;
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3875_;
v___y_3843_ = v___y_3878_;
v___y_3844_ = v___y_3866_;
v___y_3845_ = v___y_3876_;
v___y_3846_ = v___y_3867_;
v___y_3847_ = v___y_3873_;
v___y_3848_ = v___y_3881_;
v___y_3849_ = v___y_3871_;
v_args_3850_ = v___x_3893_;
goto v___jp_3829_;
}
}
}
else
{
lean_object* v___x_3894_; 
lean_dec(v___x_3883_);
v___x_3894_ = lean_box(0);
v___y_3830_ = v___y_3882_;
v___y_3831_ = v___y_3862_;
v___y_3832_ = v___y_3863_;
v___y_3833_ = v___y_3864_;
v___y_3834_ = v___y_3865_;
v___y_3835_ = v___y_3877_;
v___y_3836_ = v___y_3868_;
v___y_3837_ = v___y_3869_;
v___y_3838_ = v___y_3879_;
v___y_3839_ = v___y_3880_;
v___y_3840_ = v_only_3874_;
v___y_3841_ = v___y_3870_;
v___y_3842_ = v___y_3875_;
v___y_3843_ = v___y_3878_;
v___y_3844_ = v___y_3866_;
v___y_3845_ = v___y_3876_;
v___y_3846_ = v___y_3867_;
v___y_3847_ = v___y_3873_;
v___y_3848_ = v___y_3881_;
v___y_3849_ = v___y_3871_;
v_args_3850_ = v___x_3894_;
goto v___jp_3829_;
}
}
v___jp_3895_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3907_ = lean_unsigned_to_nat(3u);
v___x_3908_ = l_Lean_Syntax_getArg(v_stx_3743_, v___x_3907_);
lean_dec(v_stx_3743_);
v___x_3909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3908_);
v___x_3910_ = l_Lean_Syntax_isOfKind(v___x_3908_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; 
lean_dec(v___x_3908_);
lean_dec(v_unfold_3906_);
lean_dec(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec(v_tk_3762_);
v___x_3911_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3911_;
}
else
{
lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v___x_3912_ = l_Lean_Syntax_getArg(v___x_3908_, v___x_3761_);
v___x_3913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3912_);
v___x_3914_ = l_Lean_Syntax_isOfKind(v___x_3912_, v___x_3913_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; 
lean_dec(v___x_3912_);
lean_dec(v___x_3908_);
lean_dec(v_unfold_3906_);
lean_dec(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec(v_tk_3762_);
v___x_3915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3915_;
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; uint8_t v___x_3918_; 
v___x_3916_ = l_Lean_Syntax_getArg(v___x_3908_, v___x_3763_);
v___x_3917_ = l_Lean_Syntax_getArg(v___x_3908_, v___y_3901_);
v___x_3918_ = l_Lean_Syntax_isNone(v___x_3917_);
if (v___x_3918_ == 0)
{
uint8_t v___x_3919_; 
lean_inc(v___x_3917_);
v___x_3919_ = l_Lean_Syntax_matchesNull(v___x_3917_, v___x_3763_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; 
lean_dec(v___x_3917_);
lean_dec(v___x_3916_);
lean_dec(v___x_3912_);
lean_dec(v___x_3908_);
lean_dec(v_unfold_3906_);
lean_dec(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec(v_tk_3762_);
v___x_3920_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3920_;
}
else
{
lean_object* v_only_3921_; lean_object* v___x_3922_; 
v_only_3921_ = l_Lean_Syntax_getArg(v___x_3917_, v___x_3761_);
lean_dec(v___x_3917_);
v___x_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3922_, 0, v_only_3921_);
lean_inc(v___y_3901_);
v___y_3862_ = v___x_3910_;
v___y_3863_ = v___x_3912_;
v___y_3864_ = v___x_3909_;
v___y_3865_ = v___x_3913_;
v___y_3866_ = v_unfold_3906_;
v___y_3867_ = v___y_3901_;
v___y_3868_ = v___y_3900_;
v___y_3869_ = v___x_3907_;
v___y_3870_ = v___y_3901_;
v___y_3871_ = v___x_3916_;
v___y_3872_ = v___x_3907_;
v___y_3873_ = v___x_3908_;
v_only_3874_ = v___x_3922_;
v___y_3875_ = v___y_3905_;
v___y_3876_ = v___y_3903_;
v___y_3877_ = v___y_3904_;
v___y_3878_ = v___y_3897_;
v___y_3879_ = v___y_3898_;
v___y_3880_ = v___y_3899_;
v___y_3881_ = v___y_3896_;
v___y_3882_ = v___y_3902_;
goto v___jp_3861_;
}
}
else
{
lean_object* v___x_3923_; 
lean_dec(v___x_3917_);
v___x_3923_ = lean_box(0);
lean_inc(v___y_3901_);
v___y_3862_ = v___x_3910_;
v___y_3863_ = v___x_3912_;
v___y_3864_ = v___x_3909_;
v___y_3865_ = v___x_3913_;
v___y_3866_ = v_unfold_3906_;
v___y_3867_ = v___y_3901_;
v___y_3868_ = v___y_3900_;
v___y_3869_ = v___x_3907_;
v___y_3870_ = v___y_3901_;
v___y_3871_ = v___x_3916_;
v___y_3872_ = v___x_3907_;
v___y_3873_ = v___x_3908_;
v_only_3874_ = v___x_3923_;
v___y_3875_ = v___y_3905_;
v___y_3876_ = v___y_3903_;
v___y_3877_ = v___y_3904_;
v___y_3878_ = v___y_3897_;
v___y_3879_ = v___y_3898_;
v___y_3880_ = v___y_3899_;
v___y_3881_ = v___y_3896_;
v___y_3882_ = v___y_3902_;
goto v___jp_3861_;
}
}
}
}
v___jp_3924_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3934_ = lean_unsigned_to_nat(2u);
v___x_3935_ = l_Lean_Syntax_getArg(v_stx_3743_, v___x_3934_);
v___x_3936_ = l_Lean_Syntax_isNone(v___x_3935_);
if (v___x_3936_ == 0)
{
uint8_t v___x_3937_; 
lean_inc(v___x_3935_);
v___x_3937_ = l_Lean_Syntax_matchesNull(v___x_3935_, v___x_3763_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; 
lean_dec(v___x_3935_);
lean_dec(v_squeeze_3925_);
lean_dec(v_tk_3762_);
lean_dec(v_stx_3743_);
v___x_3938_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3938_;
}
else
{
lean_object* v_unfold_3939_; lean_object* v___x_3940_; 
v_unfold_3939_ = l_Lean_Syntax_getArg(v___x_3935_, v___x_3761_);
lean_dec(v___x_3935_);
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v_unfold_3939_);
v___y_3896_ = v___y_3932_;
v___y_3897_ = v___y_3929_;
v___y_3898_ = v___y_3930_;
v___y_3899_ = v___y_3931_;
v___y_3900_ = v_squeeze_3925_;
v___y_3901_ = v___x_3934_;
v___y_3902_ = v___y_3933_;
v___y_3903_ = v___y_3927_;
v___y_3904_ = v___y_3928_;
v___y_3905_ = v___y_3926_;
v_unfold_3906_ = v___x_3940_;
goto v___jp_3895_;
}
}
else
{
lean_object* v___x_3941_; 
lean_dec(v___x_3935_);
v___x_3941_ = lean_box(0);
v___y_3896_ = v___y_3932_;
v___y_3897_ = v___y_3929_;
v___y_3898_ = v___y_3930_;
v___y_3899_ = v___y_3931_;
v___y_3900_ = v_squeeze_3925_;
v___y_3901_ = v___x_3934_;
v___y_3902_ = v___y_3933_;
v___y_3903_ = v___y_3927_;
v___y_3904_ = v___y_3928_;
v___y_3905_ = v___y_3926_;
v_unfold_3906_ = v___x_3941_;
goto v___jp_3895_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_0interp(lean_interpreter_value* stack)
{
uint8_t v_useReducible_3742_ = stack[0].m_num;
lean_object* v_stx_3743_ = stack[1].m_obj;
lean_object* v_a_3744_ = stack[2].m_obj;
lean_object* v_a_3745_ = stack[3].m_obj;
lean_object* v_a_3746_ = stack[4].m_obj;
lean_object* v_a_3747_ = stack[5].m_obj;
lean_object* v_a_3748_ = stack[6].m_obj;
lean_object* v_a_3749_ = stack[7].m_obj;
lean_object* v_a_3750_ = stack[8].m_obj;
lean_object* v_a_3751_ = stack[9].m_obj;
lean_object* v_res_3949_;
v_res_3949_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_3742_, v_stx_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
stack->m_obj
 = v_res_3949_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3950_, lean_object* v_stx_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
uint8_t v_useReducible_boxed_3961_; lean_object* v_res_3962_; 
v_useReducible_boxed_3961_ = lean_unbox(v_useReducible_3950_);
v_res_3962_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3961_, v_stx_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
return v_res_3962_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_3963_, lean_object* v_val_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_3963_, v_val_3964_, v___y_3970_);
return v___x_3974_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3963_ = stack[0].m_obj;
lean_object* v_val_3964_ = stack[1].m_obj;
lean_object* v___y_3965_ = stack[2].m_obj;
lean_object* v___y_3966_ = stack[3].m_obj;
lean_object* v___y_3967_ = stack[4].m_obj;
lean_object* v___y_3968_ = stack[5].m_obj;
lean_object* v___y_3969_ = stack[6].m_obj;
lean_object* v___y_3970_ = stack[7].m_obj;
lean_object* v___y_3971_ = stack[8].m_obj;
lean_object* v___y_3972_ = stack[9].m_obj;
lean_object* v_res_3975_;
v_res_3975_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_3963_, v_val_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
stack->m_obj
 = v_res_3975_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_3976_, lean_object* v_val_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_3976_, v_val_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
return v_res_3987_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_o_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_3988_, v___y_3996_);
return v___x_3998_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_3988_ = stack[0].m_obj;
lean_object* v___y_3989_ = stack[1].m_obj;
lean_object* v___y_3990_ = stack[2].m_obj;
lean_object* v___y_3991_ = stack[3].m_obj;
lean_object* v___y_3992_ = stack[4].m_obj;
lean_object* v___y_3993_ = stack[5].m_obj;
lean_object* v___y_3994_ = stack[6].m_obj;
lean_object* v___y_3995_ = stack[7].m_obj;
lean_object* v___y_3996_ = stack[8].m_obj;
lean_object* v_res_3999_;
v_res_3999_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(v_o_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
stack->m_obj
 = v_res_3999_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___boxed(lean_object* v_o_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(v_o_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
return v_res_4010_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_4011_, lean_object* v_msg_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_4012_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
return v___x_4022_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4012_ = stack[1].m_obj;
lean_object* v___y_4013_ = stack[2].m_obj;
lean_object* v___y_4014_ = stack[3].m_obj;
lean_object* v___y_4015_ = stack[4].m_obj;
lean_object* v___y_4016_ = stack[5].m_obj;
lean_object* v___y_4017_ = stack[6].m_obj;
lean_object* v___y_4018_ = stack[7].m_obj;
lean_object* v___y_4019_ = stack[8].m_obj;
lean_object* v___y_4020_ = stack[9].m_obj;
lean_object* v_res_4023_;
v_res_4023_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_box(0), v_msg_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
stack->m_obj
 = v_res_4023_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_4024_, lean_object* v_msg_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_4024_, v_msg_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
return v_res_4035_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v_00_u03b1_4036_, lean_object* v_x_4037_, lean_object* v_mkInfoTree_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_4037_, v_mkInfoTree_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4048_;
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4037_ = stack[1].m_obj;
lean_object* v_mkInfoTree_4038_ = stack[2].m_obj;
lean_object* v___y_4039_ = stack[3].m_obj;
lean_object* v___y_4040_ = stack[4].m_obj;
lean_object* v___y_4041_ = stack[5].m_obj;
lean_object* v___y_4042_ = stack[6].m_obj;
lean_object* v___y_4043_ = stack[7].m_obj;
lean_object* v___y_4044_ = stack[8].m_obj;
lean_object* v___y_4045_ = stack[9].m_obj;
lean_object* v___y_4046_ = stack[10].m_obj;
lean_object* v_res_4049_;
v_res_4049_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_box(0), v_x_4037_, v_mkInfoTree_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
stack->m_obj
 = v_res_4049_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v_00_u03b1_4050_, lean_object* v_x_4051_, lean_object* v_mkInfoTree_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v_00_u03b1_4050_, v_x_4051_, v_mkInfoTree_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_00_u03b2_4063_, lean_object* v_x_4064_, lean_object* v_x_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_x_4064_, v_x_4065_, v_x_4066_);
return v___x_4067_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_4068_, lean_object* v_x_4069_, size_t v_x_4070_, size_t v_x_4071_, lean_object* v_x_4072_, lean_object* v_x_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_4069_, v_x_4070_, v_x_4071_, v_x_4072_, v_x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4069_ = stack[1].m_obj;
size_t v_x_4070_ = stack[2].m_num;
size_t v_x_4071_ = stack[3].m_num;
lean_object* v_x_4072_ = stack[4].m_obj;
lean_object* v_x_4073_ = stack[5].m_obj;
lean_object* v_res_4075_;
v_res_4075_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_box(0), v_x_4069_, v_x_4070_, v_x_4071_, v_x_4072_, v_x_4073_);
stack->m_obj
 = v_res_4075_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_4076_, lean_object* v_x_4077_, lean_object* v_x_4078_, lean_object* v_x_4079_, lean_object* v_x_4080_, lean_object* v_x_4081_){
_start:
{
size_t v_x_102283__boxed_4082_; size_t v_x_102284__boxed_4083_; lean_object* v_res_4084_; 
v_x_102283__boxed_4082_ = lean_unbox_usize(v_x_4078_);
lean_dec(v_x_4078_);
v_x_102284__boxed_4083_ = lean_unbox_usize(v_x_4079_);
lean_dec(v_x_4079_);
v_res_4084_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_4076_, v_x_4077_, v_x_102283__boxed_4082_, v_x_102284__boxed_4083_, v_x_4080_, v_x_4081_);
return v_res_4084_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_4085_, lean_object* v_m_4086_, lean_object* v_a_4087_){
_start:
{
uint8_t v___x_4088_; 
v___x_4088_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_4086_, v_a_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4086_ = stack[1].m_obj;
lean_object* v_a_4087_ = stack[2].m_obj;
uint8_t v_res_4089_;
v_res_4089_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(lean_box(0), v_m_4086_, v_a_4087_);
stack->m_num = v_res_4089_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_4090_, lean_object* v_m_4091_, lean_object* v_a_4092_){
_start:
{
uint8_t v_res_4093_; lean_object* v_r_4094_; 
v_res_4093_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(v_00_u03b2_4090_, v_m_4091_, v_a_4092_);
lean_dec_ref(v_a_4092_);
lean_dec_ref(v_m_4091_);
v_r_4094_ = lean_box(v_res_4093_);
return v_r_4094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_4095_, lean_object* v_m_4096_, lean_object* v_a_4097_, lean_object* v_b_4098_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_m_4096_, v_a_4097_, v_b_4098_);
return v___x_4099_;
}
}
lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(lean_object* v_mvarId_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_4100_, v___y_4101_, v___y_4107_);
return v___x_4111_;
}
}
LEAN_EXPORT void l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4100_ = stack[0].m_obj;
lean_object* v___y_4101_ = stack[1].m_obj;
lean_object* v___y_4102_ = stack[2].m_obj;
lean_object* v___y_4103_ = stack[3].m_obj;
lean_object* v___y_4104_ = stack[4].m_obj;
lean_object* v___y_4105_ = stack[5].m_obj;
lean_object* v___y_4106_ = stack[6].m_obj;
lean_object* v___y_4107_ = stack[7].m_obj;
lean_object* v___y_4108_ = stack[8].m_obj;
lean_object* v___y_4109_ = stack[9].m_obj;
lean_object* v_res_4112_;
v_res_4112_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(v_mvarId_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
stack->m_obj
 = v_res_4112_;
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___boxed(lean_object* v_mvarId_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(v_mvarId_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v_mvarId_4113_);
return v_res_4124_;
}
}
lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(lean_object* v_mvarId_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_4125_, v___y_4126_, v___y_4132_);
return v___x_4136_;
}
}
LEAN_EXPORT void l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4125_ = stack[0].m_obj;
lean_object* v___y_4126_ = stack[1].m_obj;
lean_object* v___y_4127_ = stack[2].m_obj;
lean_object* v___y_4128_ = stack[3].m_obj;
lean_object* v___y_4129_ = stack[4].m_obj;
lean_object* v___y_4130_ = stack[5].m_obj;
lean_object* v___y_4131_ = stack[6].m_obj;
lean_object* v___y_4132_ = stack[7].m_obj;
lean_object* v___y_4133_ = stack[8].m_obj;
lean_object* v___y_4134_ = stack[9].m_obj;
lean_object* v_res_4137_;
v_res_4137_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(v_mvarId_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
stack->m_obj
 = v_res_4137_;
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___boxed(lean_object* v_mvarId_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(v_mvarId_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v_mvarId_4138_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4150_, lean_object* v_n_4151_, lean_object* v_k_4152_, lean_object* v_v_4153_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_n_4151_, v_k_4152_, v_v_4153_);
return v___x_4154_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_4155_, size_t v_depth_4156_, lean_object* v_keys_4157_, lean_object* v_vals_4158_, lean_object* v_heq_4159_, lean_object* v_i_4160_, lean_object* v_entries_4161_){
_start:
{
lean_object* v___x_4162_; 
v___x_4162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_4156_, v_keys_4157_, v_vals_4158_, v_i_4160_, v_entries_4161_);
return v___x_4162_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12_0interp(lean_interpreter_value* stack)
{
size_t v_depth_4156_ = stack[1].m_num;
lean_object* v_keys_4157_ = stack[2].m_obj;
lean_object* v_vals_4158_ = stack[3].m_obj;
lean_object* v_i_4160_ = stack[5].m_obj;
lean_object* v_entries_4161_ = stack[6].m_obj;
lean_object* v_res_4163_;
v_res_4163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(lean_box(0), v_depth_4156_, v_keys_4157_, v_vals_4158_, lean_box(0), v_i_4160_, v_entries_4161_);
stack->m_obj
 = v_res_4163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_4164_, lean_object* v_depth_4165_, lean_object* v_keys_4166_, lean_object* v_vals_4167_, lean_object* v_heq_4168_, lean_object* v_i_4169_, lean_object* v_entries_4170_){
_start:
{
size_t v_depth_boxed_4171_; lean_object* v_res_4172_; 
v_depth_boxed_4171_ = lean_unbox_usize(v_depth_4165_);
lean_dec(v_depth_4165_);
v_res_4172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(v_00_u03b2_4164_, v_depth_boxed_4171_, v_keys_4166_, v_vals_4167_, v_heq_4168_, v_i_4169_, v_entries_4170_);
lean_dec_ref(v_vals_4167_);
lean_dec_ref(v_keys_4166_);
return v_res_4172_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(lean_object* v_00_u03b2_4173_, lean_object* v_a_4174_, lean_object* v_x_4175_){
_start:
{
uint8_t v___x_4176_; 
v___x_4176_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_4174_, v_x_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4174_ = stack[1].m_obj;
lean_object* v_x_4175_ = stack[2].m_obj;
uint8_t v_res_4177_;
v_res_4177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(lean_box(0), v_a_4174_, v_x_4175_);
stack->m_num = v_res_4177_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03b2_4178_, lean_object* v_a_4179_, lean_object* v_x_4180_){
_start:
{
uint8_t v_res_4181_; lean_object* v_r_4182_; 
v_res_4181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(v_00_u03b2_4178_, v_a_4179_, v_x_4180_);
lean_dec(v_x_4180_);
lean_dec_ref(v_a_4179_);
v_r_4182_ = lean_box(v_res_4181_);
return v_r_4182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17(lean_object* v_00_u03b2_4183_, lean_object* v_data_4184_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_data_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_4186_, lean_object* v_x_4187_, lean_object* v_x_4188_, lean_object* v_x_4189_, lean_object* v_x_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_x_4187_, v_x_4188_, v_x_4189_, v_x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19(lean_object* v_00_u03b2_4192_, lean_object* v_i_4193_, lean_object* v_source_4194_, lean_object* v_target_4195_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v_i_4193_, v_source_4194_, v_target_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23(lean_object* v_00_u03b2_4197_, lean_object* v_x_4198_, lean_object* v_x_4199_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_x_4198_, v_x_4199_);
return v___x_4200_;
}
}
lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
uint8_t v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = 1;
v___x_4212_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_4211_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
return v___x_4212_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Simpa_evalSimpa_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4201_ = stack[0].m_obj;
lean_object* v_a_4202_ = stack[1].m_obj;
lean_object* v_a_4203_ = stack[2].m_obj;
lean_object* v_a_4204_ = stack[3].m_obj;
lean_object* v_a_4205_ = stack[4].m_obj;
lean_object* v_a_4206_ = stack[5].m_obj;
lean_object* v_a_4207_ = stack[6].m_obj;
lean_object* v_a_4208_ = stack[7].m_obj;
lean_object* v_a_4209_ = stack[8].m_obj;
lean_object* v_res_4213_;
v_res_4213_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
stack->m_obj
 = v_res_4213_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
lean_dec(v_a_4222_);
lean_dec_ref(v_a_4221_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
return v_res_4224_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4234_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4236_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4237_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_4238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4234_, v___x_4235_, v___x_4236_, v___x_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4239_;
v_res_4239_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
stack->m_obj
 = v_res_4239_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_4241_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_4270_ = l_Lean_addBuiltinDeclarationRanges(v___x_4268_, v___x_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4271_;
v_res_4271_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
stack->m_obj
 = v_res_4271_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_4276_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_4278_);
lean_dec(v_x_4278_);
return v_res_4279_;
}
}
lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; uint8_t v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4332_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_4291_);
v___x_4333_ = l_Lean_Syntax_isOfKind(v_stx_4291_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
lean_dec(v_stx_4291_);
v___x_4334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; uint8_t v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; uint8_t v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; uint8_t v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v_tk_4462_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v_args_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___x_4522_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v_only_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v_unfold_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v_squeeze_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___x_4598_; uint8_t v___x_4599_; 
v___x_4335_ = lean_unsigned_to_nat(0u);
v_tk_4462_ = l_Lean_Syntax_getArg(v_stx_4291_, v___x_4335_);
v___x_4522_ = lean_unsigned_to_nat(1u);
v___x_4598_ = l_Lean_Syntax_getArg(v_stx_4291_, v___x_4522_);
v___x_4599_ = l_Lean_Syntax_isNone(v___x_4598_);
if (v___x_4599_ == 0)
{
uint8_t v___x_4600_; 
lean_inc(v___x_4598_);
v___x_4600_ = l_Lean_Syntax_matchesNull(v___x_4598_, v___x_4522_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; 
lean_dec(v___x_4598_);
lean_dec(v_tk_4462_);
lean_dec(v_stx_4291_);
v___x_4601_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4601_;
}
else
{
lean_object* v_squeeze_4602_; lean_object* v___x_4603_; 
v_squeeze_4602_ = l_Lean_Syntax_getArg(v___x_4598_, v___x_4335_);
lean_dec(v___x_4598_);
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v_squeeze_4602_);
v_squeeze_4581_ = v___x_4603_;
v___y_4582_ = v_a_4292_;
v___y_4583_ = v_a_4293_;
v___y_4584_ = v_a_4294_;
v___y_4585_ = v_a_4295_;
v___y_4586_ = v_a_4296_;
v___y_4587_ = v_a_4297_;
v___y_4588_ = v_a_4298_;
v___y_4589_ = v_a_4299_;
goto v___jp_4580_;
}
}
else
{
lean_object* v___x_4604_; 
lean_dec(v___x_4598_);
v___x_4604_ = lean_box(0);
v_squeeze_4581_ = v___x_4604_;
v___y_4582_ = v_a_4292_;
v___y_4583_ = v_a_4293_;
v___y_4584_ = v_a_4294_;
v___y_4585_ = v_a_4295_;
v___y_4586_ = v_a_4296_;
v___y_4587_ = v_a_4297_;
v___y_4588_ = v_a_4298_;
v___y_4589_ = v_a_4299_;
goto v___jp_4580_;
}
v___jp_4336_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_inc_ref(v___y_4356_);
v___x_4359_ = l_Array_append___redArg(v___y_4356_, v___y_4358_);
lean_dec_ref(v___y_4358_);
lean_inc(v___y_4347_);
lean_inc(v___y_4344_);
v___x_4360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4360_, 0, v___y_4344_);
lean_ctor_set(v___x_4360_, 1, v___y_4347_);
lean_ctor_set(v___x_4360_, 2, v___x_4359_);
if (lean_obj_tag(v___y_4340_) == 1)
{
lean_object* v_val_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v_val_4361_ = lean_ctor_get(v___y_4340_, 0);
lean_inc(v_val_4361_);
lean_dec_ref_known(v___y_4340_, 1);
v___x_4362_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_4344_, 4);
v___x_4364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___y_4344_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
lean_inc_ref(v___y_4356_);
v___x_4365_ = l_Array_append___redArg(v___y_4356_, v_val_4361_);
lean_dec(v_val_4361_);
lean_inc(v___y_4347_);
v___x_4366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4366_, 0, v___y_4344_);
lean_ctor_set(v___x_4366_, 1, v___y_4347_);
lean_ctor_set(v___x_4366_, 2, v___x_4365_);
v___x_4367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_4368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___y_4344_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = l_Lean_Syntax_node3(v___y_4344_, v___x_4362_, v___x_4364_, v___x_4366_, v___x_4368_);
v___x_4370_ = l_Array_mkArray1___redArg(v___x_4369_);
v___y_4302_ = v___y_4337_;
v___y_4303_ = v___y_4338_;
v___y_4304_ = v___y_4339_;
v___y_4305_ = v___y_4341_;
v___y_4306_ = v___y_4342_;
v___y_4307_ = v___y_4343_;
v___y_4308_ = v___y_4344_;
v___y_4309_ = v___x_4360_;
v___y_4310_ = v___y_4345_;
v___y_4311_ = v___y_4346_;
v___y_4312_ = v___y_4347_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4349_;
v___y_4315_ = v___y_4351_;
v___y_4316_ = v___y_4350_;
v___y_4317_ = v___y_4353_;
v___y_4318_ = v___y_4352_;
v___y_4319_ = v___y_4355_;
v___y_4320_ = v___y_4354_;
v___y_4321_ = v___y_4356_;
v___y_4322_ = v___y_4357_;
v___y_4323_ = v___x_4370_;
goto v___jp_4301_;
}
else
{
lean_object* v___x_4371_; 
lean_dec(v___y_4340_);
v___x_4371_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4302_ = v___y_4337_;
v___y_4303_ = v___y_4338_;
v___y_4304_ = v___y_4339_;
v___y_4305_ = v___y_4341_;
v___y_4306_ = v___y_4342_;
v___y_4307_ = v___y_4343_;
v___y_4308_ = v___y_4344_;
v___y_4309_ = v___x_4360_;
v___y_4310_ = v___y_4345_;
v___y_4311_ = v___y_4346_;
v___y_4312_ = v___y_4347_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4349_;
v___y_4315_ = v___y_4351_;
v___y_4316_ = v___y_4350_;
v___y_4317_ = v___y_4353_;
v___y_4318_ = v___y_4352_;
v___y_4319_ = v___y_4355_;
v___y_4320_ = v___y_4354_;
v___y_4321_ = v___y_4356_;
v___y_4322_ = v___y_4357_;
v___y_4323_ = v___x_4371_;
goto v___jp_4301_;
}
}
v___jp_4372_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
lean_inc_ref(v___y_4392_);
v___x_4395_ = l_Array_append___redArg(v___y_4392_, v___y_4394_);
lean_dec_ref(v___y_4394_);
lean_inc(v___y_4385_);
lean_inc(v___y_4381_);
v___x_4396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4396_, 0, v___y_4381_);
lean_ctor_set(v___x_4396_, 1, v___y_4385_);
lean_ctor_set(v___x_4396_, 2, v___x_4395_);
if (lean_obj_tag(v___y_4380_) == 1)
{
lean_object* v_val_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v_val_4397_ = lean_ctor_get(v___y_4380_, 0);
lean_inc(v_val_4397_);
lean_dec_ref_known(v___y_4380_, 1);
v___x_4398_ = l_Lean_SourceInfo_fromRef(v_val_4397_, v___x_4333_);
lean_dec(v_val_4397_);
v___x_4399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4400_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = l_Array_mkArray1___redArg(v___x_4400_);
v___y_4337_ = v___y_4373_;
v___y_4338_ = v___y_4374_;
v___y_4339_ = v___y_4375_;
v___y_4340_ = v___y_4376_;
v___y_4341_ = v___y_4377_;
v___y_4342_ = v___y_4378_;
v___y_4343_ = v___y_4379_;
v___y_4344_ = v___y_4381_;
v___y_4345_ = v___y_4382_;
v___y_4346_ = v___y_4383_;
v___y_4347_ = v___y_4385_;
v___y_4348_ = v___y_4384_;
v___y_4349_ = v___y_4386_;
v___y_4350_ = v___x_4396_;
v___y_4351_ = v___y_4387_;
v___y_4352_ = v___y_4389_;
v___y_4353_ = v___y_4388_;
v___y_4354_ = v___y_4391_;
v___y_4355_ = v___y_4390_;
v___y_4356_ = v___y_4392_;
v___y_4357_ = v___y_4393_;
v___y_4358_ = v___x_4401_;
goto v___jp_4336_;
}
else
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4380_);
lean_dec(v___y_4380_);
v___y_4337_ = v___y_4373_;
v___y_4338_ = v___y_4374_;
v___y_4339_ = v___y_4375_;
v___y_4340_ = v___y_4376_;
v___y_4341_ = v___y_4377_;
v___y_4342_ = v___y_4378_;
v___y_4343_ = v___y_4379_;
v___y_4344_ = v___y_4381_;
v___y_4345_ = v___y_4382_;
v___y_4346_ = v___y_4383_;
v___y_4347_ = v___y_4385_;
v___y_4348_ = v___y_4384_;
v___y_4349_ = v___y_4386_;
v___y_4350_ = v___x_4396_;
v___y_4351_ = v___y_4387_;
v___y_4352_ = v___y_4389_;
v___y_4353_ = v___y_4388_;
v___y_4354_ = v___y_4391_;
v___y_4355_ = v___y_4390_;
v___y_4356_ = v___y_4392_;
v___y_4357_ = v___y_4393_;
v___y_4358_ = v___x_4402_;
goto v___jp_4336_;
}
}
v___jp_4403_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
lean_inc_ref(v___y_4422_);
v___x_4425_ = l_Array_append___redArg(v___y_4422_, v___y_4424_);
lean_dec_ref(v___y_4424_);
lean_inc(v___y_4416_);
lean_inc(v___y_4412_);
v___x_4426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4426_, 0, v___y_4412_);
lean_ctor_set(v___x_4426_, 1, v___y_4416_);
lean_ctor_set(v___x_4426_, 2, v___x_4425_);
v___x_4427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4419_) == 0)
{
lean_object* v___x_4428_; 
v___x_4428_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4373_ = v___y_4404_;
v___y_4374_ = v___y_4405_;
v___y_4375_ = v___y_4406_;
v___y_4376_ = v___y_4407_;
v___y_4377_ = v___y_4408_;
v___y_4378_ = v___y_4409_;
v___y_4379_ = v___y_4410_;
v___y_4380_ = v___y_4411_;
v___y_4381_ = v___y_4412_;
v___y_4382_ = v___y_4414_;
v___y_4383_ = v___y_4413_;
v___y_4384_ = v___y_4415_;
v___y_4385_ = v___y_4416_;
v___y_4386_ = v___y_4417_;
v___y_4387_ = v___y_4418_;
v___y_4388_ = v___x_4427_;
v___y_4389_ = v___x_4426_;
v___y_4390_ = v___y_4421_;
v___y_4391_ = v___y_4420_;
v___y_4392_ = v___y_4422_;
v___y_4393_ = v___y_4423_;
v___y_4394_ = v___x_4428_;
goto v___jp_4372_;
}
else
{
lean_object* v_val_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_val_4429_ = lean_ctor_get(v___y_4419_, 0);
lean_inc(v_val_4429_);
lean_dec_ref_known(v___y_4419_, 1);
v___x_4430_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4431_ = lean_array_push(v___x_4430_, v_val_4429_);
v___y_4373_ = v___y_4404_;
v___y_4374_ = v___y_4405_;
v___y_4375_ = v___y_4406_;
v___y_4376_ = v___y_4407_;
v___y_4377_ = v___y_4408_;
v___y_4378_ = v___y_4409_;
v___y_4379_ = v___y_4410_;
v___y_4380_ = v___y_4411_;
v___y_4381_ = v___y_4412_;
v___y_4382_ = v___y_4414_;
v___y_4383_ = v___y_4413_;
v___y_4384_ = v___y_4415_;
v___y_4385_ = v___y_4416_;
v___y_4386_ = v___y_4417_;
v___y_4387_ = v___y_4418_;
v___y_4388_ = v___x_4427_;
v___y_4389_ = v___x_4426_;
v___y_4390_ = v___y_4421_;
v___y_4391_ = v___y_4420_;
v___y_4392_ = v___y_4422_;
v___y_4393_ = v___y_4423_;
v___y_4394_ = v___x_4431_;
goto v___jp_4372_;
}
}
v___jp_4432_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_inc_ref(v___y_4451_);
v___x_4454_ = l_Array_append___redArg(v___y_4451_, v___y_4453_);
lean_dec_ref(v___y_4453_);
lean_inc(v___y_4445_);
lean_inc(v___y_4441_);
v___x_4455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4455_, 0, v___y_4441_);
lean_ctor_set(v___x_4455_, 1, v___y_4445_);
lean_ctor_set(v___x_4455_, 2, v___x_4454_);
if (lean_obj_tag(v___y_4442_) == 1)
{
lean_object* v_val_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v_val_4456_ = lean_ctor_get(v___y_4442_, 0);
lean_inc(v_val_4456_);
lean_dec_ref_known(v___y_4442_, 1);
v___x_4457_ = l_Lean_SourceInfo_fromRef(v_val_4456_, v___x_4333_);
lean_dec(v_val_4456_);
v___x_4458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_4459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4457_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
v___x_4460_ = l_Array_mkArray1___redArg(v___x_4459_);
v___y_4404_ = v___y_4433_;
v___y_4405_ = v___y_4434_;
v___y_4406_ = v___y_4435_;
v___y_4407_ = v___y_4436_;
v___y_4408_ = v___y_4437_;
v___y_4409_ = v___y_4438_;
v___y_4410_ = v___y_4439_;
v___y_4411_ = v___y_4440_;
v___y_4412_ = v___y_4441_;
v___y_4413_ = v___x_4455_;
v___y_4414_ = v___y_4443_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___y_4445_;
v___y_4417_ = v___y_4446_;
v___y_4418_ = v___y_4447_;
v___y_4419_ = v___y_4448_;
v___y_4420_ = v___y_4450_;
v___y_4421_ = v___y_4449_;
v___y_4422_ = v___y_4451_;
v___y_4423_ = v___y_4452_;
v___y_4424_ = v___x_4460_;
goto v___jp_4403_;
}
else
{
lean_object* v___x_4461_; 
v___x_4461_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4442_);
lean_dec(v___y_4442_);
v___y_4404_ = v___y_4433_;
v___y_4405_ = v___y_4434_;
v___y_4406_ = v___y_4435_;
v___y_4407_ = v___y_4436_;
v___y_4408_ = v___y_4437_;
v___y_4409_ = v___y_4438_;
v___y_4410_ = v___y_4439_;
v___y_4411_ = v___y_4440_;
v___y_4412_ = v___y_4441_;
v___y_4413_ = v___x_4455_;
v___y_4414_ = v___y_4443_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___y_4445_;
v___y_4417_ = v___y_4446_;
v___y_4418_ = v___y_4447_;
v___y_4419_ = v___y_4448_;
v___y_4420_ = v___y_4450_;
v___y_4421_ = v___y_4449_;
v___y_4422_ = v___y_4451_;
v___y_4423_ = v___y_4452_;
v___y_4424_ = v___x_4461_;
goto v___jp_4403_;
}
}
v___jp_4463_:
{
lean_object* v_ref_4479_; uint8_t v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v_ref_4479_ = lean_ctor_get(v___y_4465_, 2);
v___x_4480_ = 0;
v___x_4481_ = l_Lean_SourceInfo_fromRef(v_ref_4479_, v___x_4480_);
v___x_4482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4484_ = l_Lean_SourceInfo_fromRef(v_tk_4462_, v___x_4333_);
lean_dec(v_tk_4462_);
v___x_4485_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
lean_ctor_set(v___x_4485_, 1, v___x_4482_);
v___x_4486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_4487_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_4476_) == 1)
{
lean_object* v_val_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v_val_4488_ = lean_ctor_get(v___y_4476_, 0);
lean_inc(v_val_4488_);
lean_dec_ref_known(v___y_4476_, 1);
v___x_4489_ = l_Lean_SourceInfo_fromRef(v_val_4488_, v___x_4333_);
lean_dec(v_val_4488_);
v___x_4490_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4489_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
v___x_4492_ = l_Array_mkArray1___redArg(v___x_4491_);
v___y_4433_ = v___y_4464_;
v___y_4434_ = v___x_4485_;
v___y_4435_ = v___x_4483_;
v___y_4436_ = v___y_4466_;
v___y_4437_ = v___y_4465_;
v___y_4438_ = v___y_4467_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4469_;
v___y_4441_ = v___x_4481_;
v___y_4442_ = v___y_4470_;
v___y_4443_ = v___y_4471_;
v___y_4444_ = v___x_4480_;
v___y_4445_ = v___x_4486_;
v___y_4446_ = v___y_4472_;
v___y_4447_ = v___y_4473_;
v___y_4448_ = v___y_4478_;
v___y_4449_ = v___y_4474_;
v___y_4450_ = v___y_4475_;
v___y_4451_ = v___x_4487_;
v___y_4452_ = v___y_4477_;
v___y_4453_ = v___x_4492_;
goto v___jp_4432_;
}
else
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4476_);
lean_dec(v___y_4476_);
v___y_4433_ = v___y_4464_;
v___y_4434_ = v___x_4485_;
v___y_4435_ = v___x_4483_;
v___y_4436_ = v___y_4466_;
v___y_4437_ = v___y_4465_;
v___y_4438_ = v___y_4467_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4469_;
v___y_4441_ = v___x_4481_;
v___y_4442_ = v___y_4470_;
v___y_4443_ = v___y_4471_;
v___y_4444_ = v___x_4480_;
v___y_4445_ = v___x_4486_;
v___y_4446_ = v___y_4472_;
v___y_4447_ = v___y_4473_;
v___y_4448_ = v___y_4478_;
v___y_4449_ = v___y_4474_;
v___y_4450_ = v___y_4475_;
v___y_4451_ = v___x_4487_;
v___y_4452_ = v___y_4477_;
v___y_4453_ = v___x_4493_;
goto v___jp_4432_;
}
}
v___jp_4494_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_unsigned_to_nat(5u);
v___x_4511_ = l_Lean_Syntax_getArg(v___y_4496_, v___x_4510_);
lean_dec(v___y_4496_);
v___x_4512_ = l_Lean_Syntax_getOptional_x3f(v___y_4495_);
lean_dec(v___y_4495_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_box(0);
v___y_4464_ = v___y_4502_;
v___y_4465_ = v___y_4508_;
v___y_4466_ = v_args_4501_;
v___y_4467_ = v___y_4507_;
v___y_4468_ = v___y_4505_;
v___y_4469_ = v___y_4497_;
v___y_4470_ = v___y_4498_;
v___y_4471_ = v___y_4504_;
v___y_4472_ = v___y_4509_;
v___y_4473_ = v___y_4503_;
v___y_4474_ = v___y_4506_;
v___y_4475_ = v___y_4499_;
v___y_4476_ = v___y_4500_;
v___y_4477_ = v___x_4511_;
v___y_4478_ = v___x_4513_;
goto v___jp_4463_;
}
else
{
lean_object* v_val_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
v_val_4514_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4512_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_val_4514_);
lean_dec(v___x_4512_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_val_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
v___y_4464_ = v___y_4502_;
v___y_4465_ = v___y_4508_;
v___y_4466_ = v_args_4501_;
v___y_4467_ = v___y_4507_;
v___y_4468_ = v___y_4505_;
v___y_4469_ = v___y_4497_;
v___y_4470_ = v___y_4498_;
v___y_4471_ = v___y_4504_;
v___y_4472_ = v___y_4509_;
v___y_4473_ = v___y_4503_;
v___y_4474_ = v___y_4506_;
v___y_4475_ = v___y_4499_;
v___y_4476_ = v___y_4500_;
v___y_4477_ = v___x_4511_;
v___y_4478_ = v___x_4519_;
goto v___jp_4463_;
}
}
}
}
v___jp_4523_:
{
lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4539_ = l_Lean_Syntax_getArg(v___y_4525_, v___y_4529_);
v___x_4540_ = l_Lean_Syntax_isNone(v___x_4539_);
if (v___x_4540_ == 0)
{
uint8_t v___x_4541_; 
lean_inc(v___x_4539_);
v___x_4541_ = l_Lean_Syntax_matchesNull(v___x_4539_, v___x_4522_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; 
lean_dec(v___x_4539_);
lean_dec(v_only_4530_);
lean_dec(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec(v_tk_4462_);
v___x_4542_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4542_;
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; uint8_t v___x_4545_; 
v___x_4543_ = l_Lean_Syntax_getArg(v___x_4539_, v___x_4335_);
lean_dec(v___x_4539_);
v___x_4544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4543_);
v___x_4545_ = l_Lean_Syntax_isOfKind(v___x_4543_, v___x_4544_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; 
lean_dec(v___x_4543_);
lean_dec(v_only_4530_);
lean_dec(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec(v_tk_4462_);
v___x_4546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4546_;
}
else
{
lean_object* v___x_4547_; lean_object* v_args_4548_; lean_object* v___x_4549_; 
v___x_4547_ = l_Lean_Syntax_getArg(v___x_4543_, v___x_4522_);
lean_dec(v___x_4543_);
v_args_4548_ = l_Lean_Syntax_getArgs(v___x_4547_);
lean_dec(v___x_4547_);
v___x_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4549_, 0, v_args_4548_);
v___y_4495_ = v___y_4524_;
v___y_4496_ = v___y_4525_;
v___y_4497_ = v_only_4530_;
v___y_4498_ = v___y_4526_;
v___y_4499_ = v___y_4527_;
v___y_4500_ = v___y_4528_;
v_args_4501_ = v___x_4549_;
v___y_4502_ = v___y_4531_;
v___y_4503_ = v___y_4532_;
v___y_4504_ = v___y_4533_;
v___y_4505_ = v___y_4534_;
v___y_4506_ = v___y_4535_;
v___y_4507_ = v___y_4536_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4538_;
goto v___jp_4494_;
}
}
}
else
{
lean_object* v___x_4550_; 
lean_dec(v___x_4539_);
v___x_4550_ = lean_box(0);
v___y_4495_ = v___y_4524_;
v___y_4496_ = v___y_4525_;
v___y_4497_ = v_only_4530_;
v___y_4498_ = v___y_4526_;
v___y_4499_ = v___y_4527_;
v___y_4500_ = v___y_4528_;
v_args_4501_ = v___x_4550_;
v___y_4502_ = v___y_4531_;
v___y_4503_ = v___y_4532_;
v___y_4504_ = v___y_4533_;
v___y_4505_ = v___y_4534_;
v___y_4506_ = v___y_4535_;
v___y_4507_ = v___y_4536_;
v___y_4508_ = v___y_4537_;
v___y_4509_ = v___y_4538_;
goto v___jp_4494_;
}
}
v___jp_4551_:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4563_ = lean_unsigned_to_nat(3u);
v___x_4564_ = l_Lean_Syntax_getArg(v_stx_4291_, v___x_4563_);
lean_dec(v_stx_4291_);
v___x_4565_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4564_);
v___x_4566_ = l_Lean_Syntax_isOfKind(v___x_4564_, v___x_4565_);
if (v___x_4566_ == 0)
{
lean_object* v___x_4567_; 
lean_dec(v___x_4564_);
lean_dec(v_unfold_4554_);
lean_dec(v___y_4553_);
lean_dec(v_tk_4462_);
v___x_4567_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4567_;
}
else
{
lean_object* v___x_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; 
v___x_4568_ = l_Lean_Syntax_getArg(v___x_4564_, v___x_4335_);
v___x_4569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4568_);
v___x_4570_ = l_Lean_Syntax_isOfKind(v___x_4568_, v___x_4569_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4571_; 
lean_dec(v___x_4568_);
lean_dec(v___x_4564_);
lean_dec(v_unfold_4554_);
lean_dec(v___y_4553_);
lean_dec(v_tk_4462_);
v___x_4571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4571_;
}
else
{
lean_object* v___x_4572_; lean_object* v___x_4573_; uint8_t v___x_4574_; 
v___x_4572_ = l_Lean_Syntax_getArg(v___x_4564_, v___x_4522_);
v___x_4573_ = l_Lean_Syntax_getArg(v___x_4564_, v___y_4552_);
v___x_4574_ = l_Lean_Syntax_isNone(v___x_4573_);
if (v___x_4574_ == 0)
{
uint8_t v___x_4575_; 
lean_inc(v___x_4573_);
v___x_4575_ = l_Lean_Syntax_matchesNull(v___x_4573_, v___x_4522_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; 
lean_dec(v___x_4573_);
lean_dec(v___x_4572_);
lean_dec(v___x_4568_);
lean_dec(v___x_4564_);
lean_dec(v_unfold_4554_);
lean_dec(v___y_4553_);
lean_dec(v_tk_4462_);
v___x_4576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4576_;
}
else
{
lean_object* v_only_4577_; lean_object* v___x_4578_; 
v_only_4577_ = l_Lean_Syntax_getArg(v___x_4573_, v___x_4335_);
lean_dec(v___x_4573_);
v___x_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4578_, 0, v_only_4577_);
v___y_4524_ = v___x_4572_;
v___y_4525_ = v___x_4564_;
v___y_4526_ = v_unfold_4554_;
v___y_4527_ = v___x_4568_;
v___y_4528_ = v___y_4553_;
v___y_4529_ = v___x_4563_;
v_only_4530_ = v___x_4578_;
v___y_4531_ = v___y_4555_;
v___y_4532_ = v___y_4556_;
v___y_4533_ = v___y_4557_;
v___y_4534_ = v___y_4558_;
v___y_4535_ = v___y_4559_;
v___y_4536_ = v___y_4560_;
v___y_4537_ = v___y_4561_;
v___y_4538_ = v___y_4562_;
goto v___jp_4523_;
}
}
else
{
lean_object* v___x_4579_; 
lean_dec(v___x_4573_);
v___x_4579_ = lean_box(0);
v___y_4524_ = v___x_4572_;
v___y_4525_ = v___x_4564_;
v___y_4526_ = v_unfold_4554_;
v___y_4527_ = v___x_4568_;
v___y_4528_ = v___y_4553_;
v___y_4529_ = v___x_4563_;
v_only_4530_ = v___x_4579_;
v___y_4531_ = v___y_4555_;
v___y_4532_ = v___y_4556_;
v___y_4533_ = v___y_4557_;
v___y_4534_ = v___y_4558_;
v___y_4535_ = v___y_4559_;
v___y_4536_ = v___y_4560_;
v___y_4537_ = v___y_4561_;
v___y_4538_ = v___y_4562_;
goto v___jp_4523_;
}
}
}
}
v___jp_4580_:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4590_ = lean_unsigned_to_nat(2u);
v___x_4591_ = l_Lean_Syntax_getArg(v_stx_4291_, v___x_4590_);
v___x_4592_ = l_Lean_Syntax_isNone(v___x_4591_);
if (v___x_4592_ == 0)
{
uint8_t v___x_4593_; 
lean_inc(v___x_4591_);
v___x_4593_ = l_Lean_Syntax_matchesNull(v___x_4591_, v___x_4522_);
if (v___x_4593_ == 0)
{
lean_object* v___x_4594_; 
lean_dec(v___x_4591_);
lean_dec(v_squeeze_4581_);
lean_dec(v_tk_4462_);
lean_dec(v_stx_4291_);
v___x_4594_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4594_;
}
else
{
lean_object* v_unfold_4595_; lean_object* v___x_4596_; 
v_unfold_4595_ = l_Lean_Syntax_getArg(v___x_4591_, v___x_4335_);
lean_dec(v___x_4591_);
v___x_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4596_, 0, v_unfold_4595_);
v___y_4552_ = v___x_4590_;
v___y_4553_ = v_squeeze_4581_;
v_unfold_4554_ = v___x_4596_;
v___y_4555_ = v___y_4582_;
v___y_4556_ = v___y_4583_;
v___y_4557_ = v___y_4584_;
v___y_4558_ = v___y_4585_;
v___y_4559_ = v___y_4586_;
v___y_4560_ = v___y_4587_;
v___y_4561_ = v___y_4588_;
v___y_4562_ = v___y_4589_;
goto v___jp_4551_;
}
}
else
{
lean_object* v___x_4597_; 
lean_dec(v___x_4591_);
v___x_4597_ = lean_box(0);
v___y_4552_ = v___x_4590_;
v___y_4553_ = v_squeeze_4581_;
v_unfold_4554_ = v___x_4597_;
v___y_4555_ = v___y_4582_;
v___y_4556_ = v___y_4583_;
v___y_4557_ = v___y_4584_;
v___y_4558_ = v___y_4585_;
v___y_4559_ = v___y_4586_;
v___y_4560_ = v___y_4587_;
v___y_4561_ = v___y_4588_;
v___y_4562_ = v___y_4589_;
goto v___jp_4551_;
}
}
}
v___jp_4301_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
lean_inc_ref(v___y_4321_);
v___x_4324_ = l_Array_append___redArg(v___y_4321_, v___y_4323_);
lean_dec_ref(v___y_4323_);
lean_inc_n(v___y_4312_, 2);
lean_inc_n(v___y_4308_, 4);
v___x_4325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4325_, 0, v___y_4308_);
lean_ctor_set(v___x_4325_, 1, v___y_4312_);
lean_ctor_set(v___x_4325_, 2, v___x_4324_);
v___x_4326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___y_4308_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = l_Lean_Syntax_node2(v___y_4308_, v___y_4312_, v___x_4327_, v___y_4322_);
lean_inc(v___y_4317_);
v___x_4329_ = l_Lean_Syntax_node5(v___y_4308_, v___y_4317_, v___y_4320_, v___y_4316_, v___y_4309_, v___x_4325_, v___x_4328_);
lean_inc(v___y_4304_);
v___x_4330_ = l_Lean_Syntax_node4(v___y_4308_, v___y_4304_, v___y_4303_, v___y_4311_, v___y_4318_, v___x_4329_);
v___x_4331_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4313_, v___x_4330_, v___y_4302_, v___y_4315_, v___y_4310_, v___y_4307_, v___y_4319_, v___y_4306_, v___y_4305_, v___y_4314_);
return v___x_4331_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_4291_ = stack[0].m_obj;
lean_object* v_a_4292_ = stack[1].m_obj;
lean_object* v_a_4293_ = stack[2].m_obj;
lean_object* v_a_4294_ = stack[3].m_obj;
lean_object* v_a_4295_ = stack[4].m_obj;
lean_object* v_a_4296_ = stack[5].m_obj;
lean_object* v_a_4297_ = stack[6].m_obj;
lean_object* v_a_4298_ = stack[7].m_obj;
lean_object* v_a_4299_ = stack[8].m_obj;
lean_object* v_res_4605_;
v_res_4605_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
stack->m_obj
 = v_res_4605_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v_res_4616_; 
v_res_4616_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
return v_res_4616_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4625_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4626_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4628_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4629_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4625_, v___x_4626_, v___x_4627_, v___x_4628_);
return v___x_4629_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4630_;
v_res_4630_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
stack->m_obj
 = v_res_4630_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4632_;
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
