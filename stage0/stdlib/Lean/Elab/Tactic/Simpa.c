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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_suppressElabErrors_boxed_116_; uint8_t v___y_4862__boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_suppressElabErrors_boxed_116_ = lean_unbox(v_suppressElabErrors_113_);
v___y_4862__boxed_117_ = lean_unbox(v___y_114_);
v_res_118_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_116_, v___y_4862__boxed_117_, v_x_115_);
lean_dec(v_x_115_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; lean_object* v_env_127_; lean_object* v___x_128_; lean_object* v_toCold_129_; lean_object* v_mctx_130_; lean_object* v_lctx_131_; lean_object* v_options_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_126_ = lean_st_ref_get(v___y_124_);
v_env_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_env_127_);
lean_dec(v___x_126_);
v___x_128_ = lean_st_ref_get(v___y_122_);
v_toCold_129_ = lean_ctor_get(v___y_123_, 0);
v_mctx_130_ = lean_ctor_get(v___x_128_, 0);
lean_inc_ref(v_mctx_130_);
lean_dec(v___x_128_);
v_lctx_131_ = lean_ctor_get(v___y_121_, 2);
v_options_132_ = lean_ctor_get(v_toCold_129_, 2);
lean_inc_ref(v_options_132_);
lean_inc_ref(v_lctx_131_);
v___x_133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_133_, 0, v_env_127_);
lean_ctor_set(v___x_133_, 1, v_mctx_130_);
lean_ctor_set(v___x_133_, 2, v_lctx_131_);
lean_ctor_set(v___x_133_, 3, v_options_132_);
v___x_134_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v_msgData_120_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msgData_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_144_, lean_object* v_msgData_145_, uint8_t v_severity_146_, uint8_t v_isSilent_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; uint8_t v___y_159_; uint8_t v___y_160_; lean_object* v_toCold_161_; lean_object* v___y_162_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; uint8_t v___y_196_; uint8_t v___y_197_; lean_object* v___y_198_; lean_object* v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; uint8_t v___y_222_; uint8_t v___y_223_; lean_object* v___y_224_; uint8_t v___y_228_; uint8_t v___y_229_; uint8_t v___y_230_; uint8_t v___x_241_; uint8_t v___y_243_; uint8_t v___y_244_; uint8_t v___y_245_; uint8_t v___y_247_; uint8_t v___x_255_; 
v___x_241_ = 2;
v___x_255_ = l_Lean_instBEqMessageSeverity_beq(v_severity_146_, v___x_241_);
if (v___x_255_ == 0)
{
v___y_247_ = v___x_255_;
goto v___jp_246_;
}
else
{
uint8_t v___x_256_; 
lean_inc_ref(v_msgData_145_);
v___x_256_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_145_);
v___y_247_ = v___x_256_;
goto v___jp_246_;
}
v___jp_153_:
{
lean_object* v_currNamespace_163_; lean_object* v_openDecls_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_env_169_; lean_object* v_nextMacroScope_170_; lean_object* v_ngen_171_; lean_object* v_auxDeclNGen_172_; lean_object* v_traceState_173_; lean_object* v_cache_174_; lean_object* v_recordedDeps_175_; lean_object* v_messages_176_; lean_object* v_infoState_177_; lean_object* v_snapshotTasks_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_189_; 
v_currNamespace_163_ = lean_ctor_get(v_toCold_161_, 4);
v_openDecls_164_ = lean_ctor_get(v_toCold_161_, 5);
lean_inc(v_openDecls_164_);
lean_inc(v_currNamespace_163_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_currNamespace_163_);
lean_ctor_set(v___x_165_, 1, v_openDecls_164_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___y_158_);
lean_inc_ref(v___y_157_);
lean_inc_ref(v___y_154_);
v___x_167_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_167_, 0, v___y_154_);
lean_ctor_set(v___x_167_, 1, v___y_155_);
lean_ctor_set(v___x_167_, 2, v___y_156_);
lean_ctor_set(v___x_167_, 3, v___y_157_);
lean_ctor_set(v___x_167_, 4, v___x_166_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*5, v___y_160_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*5 + 1, v___y_159_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*5 + 2, v_isSilent_147_);
v___x_168_ = lean_st_ref_take(v___y_162_);
v_env_169_ = lean_ctor_get(v___x_168_, 0);
v_nextMacroScope_170_ = lean_ctor_get(v___x_168_, 1);
v_ngen_171_ = lean_ctor_get(v___x_168_, 2);
v_auxDeclNGen_172_ = lean_ctor_get(v___x_168_, 3);
v_traceState_173_ = lean_ctor_get(v___x_168_, 4);
v_cache_174_ = lean_ctor_get(v___x_168_, 5);
v_recordedDeps_175_ = lean_ctor_get(v___x_168_, 6);
v_messages_176_ = lean_ctor_get(v___x_168_, 7);
v_infoState_177_ = lean_ctor_get(v___x_168_, 8);
v_snapshotTasks_178_ = lean_ctor_get(v___x_168_, 9);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_189_ == 0)
{
v___x_180_ = v___x_168_;
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_snapshotTasks_178_);
lean_inc(v_infoState_177_);
lean_inc(v_messages_176_);
lean_inc(v_recordedDeps_175_);
lean_inc(v_cache_174_);
lean_inc(v_traceState_173_);
lean_inc(v_auxDeclNGen_172_);
lean_inc(v_ngen_171_);
lean_inc(v_nextMacroScope_170_);
lean_inc(v_env_169_);
lean_dec(v___x_168_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_189_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_box(0);
v___x_183_ = l_Lean_MessageLog_add(v___x_167_, v_messages_176_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 7, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_env_169_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_nextMacroScope_170_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_ngen_171_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_auxDeclNGen_172_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v_traceState_173_);
lean_ctor_set(v_reuseFailAlloc_188_, 5, v_cache_174_);
lean_ctor_set(v_reuseFailAlloc_188_, 6, v_recordedDeps_175_);
lean_ctor_set(v_reuseFailAlloc_188_, 7, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_188_, 8, v_infoState_177_);
lean_ctor_set(v_reuseFailAlloc_188_, 9, v_snapshotTasks_178_);
v___x_185_ = v_reuseFailAlloc_188_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_st_ref_put(v___y_162_, v___x_185_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_182_);
return v___x_187_;
}
}
}
v___jp_190_:
{
lean_object* v_fileName_199_; lean_object* v_fileMap_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_216_; 
v_fileName_199_ = lean_ctor_get(v___y_193_, 0);
v_fileMap_200_ = lean_ctor_get(v___y_193_, 1);
v___x_201_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_145_);
v___x_202_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v___x_201_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_216_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_216_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_inc_ref_n(v_fileMap_200_, 2);
v___x_207_ = l_Lean_FileMap_toPosition(v_fileMap_200_, v___y_195_);
lean_dec(v___y_195_);
v___x_208_ = l_Lean_FileMap_toPosition(v_fileMap_200_, v___y_198_);
lean_dec(v___y_198_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___x_210_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0));
if (v___y_194_ == 0)
{
lean_del_object(v___x_205_);
lean_dec_ref(v___y_192_);
v___y_154_ = v_fileName_199_;
v___y_155_ = v___x_207_;
v___y_156_ = v___x_209_;
v___y_157_ = v___x_210_;
v___y_158_ = v_a_203_;
v___y_159_ = v___y_196_;
v___y_160_ = v___y_197_;
v_toCold_161_ = v___y_191_;
v___y_162_ = v___y_151_;
goto v___jp_153_;
}
else
{
uint8_t v___x_211_; 
lean_inc(v_a_203_);
v___x_211_ = l_Lean_MessageData_hasTag(v___y_192_, v_a_203_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_214_; 
lean_dec_ref_known(v___x_209_, 1);
lean_dec_ref(v___x_207_);
lean_dec(v_a_203_);
v___x_212_ = lean_box(0);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_212_);
v___x_214_ = v___x_205_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
else
{
lean_del_object(v___x_205_);
v___y_154_ = v_fileName_199_;
v___y_155_ = v___x_207_;
v___y_156_ = v___x_209_;
v___y_157_ = v___x_210_;
v___y_158_ = v_a_203_;
v___y_159_ = v___y_196_;
v___y_160_ = v___y_197_;
v_toCold_161_ = v___y_191_;
v___y_162_ = v___y_151_;
goto v___jp_153_;
}
}
}
}
v___jp_217_:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Syntax_getTailPos_x3f(v___y_221_, v___y_223_);
lean_dec(v___y_221_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_inc(v___y_224_);
v___y_191_ = v___y_218_;
v___y_192_ = v___y_220_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_219_;
v___y_195_ = v___y_224_;
v___y_196_ = v___y_222_;
v___y_197_ = v___y_223_;
v___y_198_ = v___y_224_;
goto v___jp_190_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___x_225_, 1);
v___y_191_ = v___y_218_;
v___y_192_ = v___y_220_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_219_;
v___y_195_ = v___y_224_;
v___y_196_ = v___y_222_;
v___y_197_ = v___y_223_;
v___y_198_ = v_val_226_;
goto v___jp_190_;
}
}
v___jp_227_:
{
lean_object* v_toCold_231_; lean_object* v_ref_232_; uint8_t v_suppressElabErrors_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___f_236_; lean_object* v_ref_237_; lean_object* v___x_238_; 
v_toCold_231_ = lean_ctor_get(v___y_150_, 0);
v_ref_232_ = lean_ctor_get(v___y_150_, 2);
v_suppressElabErrors_233_ = lean_ctor_get_uint8(v___y_150_, sizeof(void*)*3 + 2);
v___x_234_ = lean_box(v_suppressElabErrors_233_);
v___x_235_ = lean_box(v___y_228_);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_236_, 0, v___x_234_);
lean_closure_set(v___f_236_, 1, v___x_235_);
v_ref_237_ = l_Lean_replaceRef(v_ref_144_, v_ref_232_);
v___x_238_ = l_Lean_Syntax_getPos_x3f(v_ref_237_, v___y_229_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___y_218_ = v_toCold_231_;
v___y_219_ = v_suppressElabErrors_233_;
v___y_220_ = v___f_236_;
v___y_221_ = v_ref_237_;
v___y_222_ = v___y_230_;
v___y_223_ = v___y_229_;
v___y_224_ = v___x_239_;
goto v___jp_217_;
}
else
{
lean_object* v_val_240_; 
v_val_240_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v___x_238_, 1);
v___y_218_ = v_toCold_231_;
v___y_219_ = v_suppressElabErrors_233_;
v___y_220_ = v___f_236_;
v___y_221_ = v_ref_237_;
v___y_222_ = v___y_230_;
v___y_223_ = v___y_229_;
v___y_224_ = v_val_240_;
goto v___jp_217_;
}
}
v___jp_242_:
{
if (v___y_245_ == 0)
{
v___y_228_ = v___y_243_;
v___y_229_ = v___y_244_;
v___y_230_ = v_severity_146_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___y_243_;
v___y_229_ = v___y_244_;
v___y_230_ = v___x_241_;
goto v___jp_227_;
}
}
v___jp_246_:
{
if (v___y_247_ == 0)
{
uint8_t v___x_248_; uint8_t v___x_249_; 
v___x_248_ = 1;
v___x_249_ = l_Lean_instBEqMessageSeverity_beq(v_severity_146_, v___x_248_);
if (v___x_249_ == 0)
{
v___y_243_ = v___y_247_;
v___y_244_ = v___y_247_;
v___y_245_ = v___x_249_;
goto v___jp_242_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_150_);
v___x_251_ = l_Lean_warningAsError;
v___x_252_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_250_, v___x_251_);
lean_dec_ref(v___x_250_);
v___y_243_ = v___y_247_;
v___y_244_ = v___y_247_;
v___y_245_ = v___x_252_;
goto v___jp_242_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref(v_msgData_145_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_257_, lean_object* v_msgData_258_, lean_object* v_severity_259_, lean_object* v_isSilent_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v_severity_boxed_266_; uint8_t v_isSilent_boxed_267_; lean_object* v_res_268_; 
v_severity_boxed_266_ = lean_unbox(v_severity_259_);
v_isSilent_boxed_267_ = lean_unbox(v_isSilent_260_);
v_res_268_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_257_, v_msgData_258_, v_severity_boxed_266_, v_isSilent_boxed_267_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v_ref_257_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_269_, lean_object* v_msgData_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
uint8_t v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; 
v___x_280_ = 1;
v___x_281_ = 0;
v___x_282_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_269_, v_msgData_270_, v___x_280_, v___x_281_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_283_, lean_object* v_msgData_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_283_, v_msgData_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v_ref_283_);
return v_res_294_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_300_ = l_Lean_stringToMessageData(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_301_, lean_object* v_stx_302_, lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_name_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_331_; 
v_name_313_ = lean_ctor_get(v_linterOption_301_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_linterOption_301_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_linterOption_301_, 1);
lean_dec(v_unused_332_);
v___x_315_ = v_linterOption_301_;
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_name_313_);
lean_dec(v_linterOption_301_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_317_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_313_);
v___x_318_ = l_Lean_MessageData_ofName(v_name_313_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 7);
lean_ctor_set(v___x_315_, 1, v___x_318_);
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_330_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_disable_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_321_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v_disable_323_ = l_Lean_MessageData_note(v___x_322_);
v___x_324_ = l_Lean_Linter_linterMessageTag;
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v_msg_303_);
lean_ctor_set(v___x_325_, 1, v_disable_323_);
v___x_326_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_327_, 0, v_name_313_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
lean_inc(v_stx_302_);
v___x_328_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_328_, 0, v_stx_302_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_302_, v___x_328_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v_stx_302_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_333_, lean_object* v_stx_334_, lean_object* v_msg_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_333_, v_stx_334_, v_msg_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_345_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v_msg_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_348_ = l_Lean_stringToMessageData(v___x_347_);
return v_msg_348_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_356_ = l_Lean_MessageData_ofFormat(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_357_, lean_object* v_ref_358_, lean_object* v_replacement_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_msg_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v_msg_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_msg_381_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_382_ = lean_box(0);
lean_inc(v_replacement_359_);
v___x_383_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_357_, v_replacement_359_, v___x_382_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; uint8_t v___x_385_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v___x_385_ = lean_unbox(v_a_384_);
lean_dec(v_a_384_);
if (v___x_385_ == 0)
{
lean_dec(v_replacement_359_);
v_msg_370_ = v_msg_381_;
v___y_371_ = v_a_360_;
v___y_372_ = v_a_361_;
v___y_373_ = v_a_362_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
v___y_376_ = v_a_365_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
goto v___jp_369_;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_replacement_359_);
v___x_388_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_382_);
lean_ctor_set(v___x_388_, 2, v___x_382_);
lean_ctor_set(v___x_388_, 3, v___x_382_);
lean_ctor_set(v___x_388_, 4, v___x_382_);
lean_ctor_set(v___x_388_, 5, v___x_382_);
lean_inc(v_ref_358_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_ref_358_);
v___x_390_ = 4;
lean_inc_ref(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_391_, 0, v___x_388_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_382_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*3, v___x_390_);
v___x_392_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
v___x_395_ = lean_array_push(v___x_394_, v___x_391_);
v___x_396_ = 0;
v___x_397_ = l_Lean_MessageData_hint(v___x_392_, v___x_395_, v___x_389_, v___x_382_, v___x_396_, v_a_366_, v_a_367_);
lean_dec_ref(v___x_395_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v_msg_381_);
lean_ctor_set(v___x_399_, 1, v_a_398_);
v_msg_370_ = v___x_399_;
v___y_371_ = v_a_360_;
v___y_372_ = v_a_361_;
v___y_373_ = v_a_362_;
v___y_374_ = v_a_363_;
v___y_375_ = v_a_364_;
v___y_376_ = v_a_365_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
goto v___jp_369_;
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_ref_358_);
v_a_400_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_397_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_397_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec(v_replacement_359_);
lean_dec(v_ref_358_);
v_a_408_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_383_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_383_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
v___jp_369_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = l_Lean_linter_unnecessarySimpa;
v___x_380_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_379_, v_ref_358_, v_msg_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_416_, lean_object* v_ref_417_, lean_object* v_replacement_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_416_, v_ref_417_, v_replacement_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_429_, lean_object* v_msgData_430_, uint8_t v_severity_431_, uint8_t v_isSilent_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_429_, v_msgData_430_, v_severity_431_, v_isSilent_432_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_443_, lean_object* v_msgData_444_, lean_object* v_severity_445_, lean_object* v_isSilent_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v_severity_boxed_456_; uint8_t v_isSilent_boxed_457_; lean_object* v_res_458_; 
v_severity_boxed_456_ = lean_unbox(v_severity_445_);
v_isSilent_boxed_457_ = lean_unbox(v_isSilent_446_);
v_res_458_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_443_, v_msgData_444_, v_severity_boxed_456_, v_isSilent_boxed_457_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v_ref_443_);
return v_res_458_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
v___x_460_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(lean_object* v_x_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
v___x_499_ = lean_apply_9(v_x_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, lean_box(0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed(lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0(v_x_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(lean_object* v_mvarId_511_, lean_object* v_x_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___f_522_; lean_object* v___x_523_; 
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
v___f_522_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_522_, 0, v_x_512_);
lean_closure_set(v___f_522_, 1, v___y_513_);
lean_closure_set(v___f_522_, 2, v___y_514_);
lean_closure_set(v___f_522_, 3, v___y_515_);
lean_closure_set(v___f_522_, 4, v___y_516_);
v___x_523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_511_, v___f_522_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_523_) == 0)
{
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg___boxed(lean_object* v_mvarId_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_532_, v_x_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v_00_u03b1_544_, lean_object* v_mvarId_545_, lean_object* v_x_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_mvarId_545_, v_x_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v_00_u03b1_557_, lean_object* v_mvarId_558_, lean_object* v_x_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v_00_u03b1_557_, v_mvarId_558_, v_x_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_unsigned_to_nat(32u);
v___x_571_ = lean_mk_empty_array_with_capacity(v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_573_ = ((size_t)5ULL);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_unsigned_to_nat(32u);
v___x_576_ = lean_mk_empty_array_with_capacity(v___x_575_);
v___x_577_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_578_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_576_);
lean_ctor_set(v___x_578_, 2, v___x_574_);
lean_ctor_set(v___x_578_, 3, v___x_574_);
lean_ctor_set_usize(v___x_578_, 4, v___x_573_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; lean_object* v_infoState_582_; lean_object* v_trees_583_; lean_object* v___x_584_; lean_object* v_infoState_585_; lean_object* v_env_586_; lean_object* v_nextMacroScope_587_; lean_object* v_ngen_588_; lean_object* v_auxDeclNGen_589_; lean_object* v_traceState_590_; lean_object* v_cache_591_; lean_object* v_recordedDeps_592_; lean_object* v_messages_593_; lean_object* v_snapshotTasks_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_615_; 
v___x_581_ = lean_st_ref_get(v___y_579_);
v_infoState_582_ = lean_ctor_get(v___x_581_, 8);
lean_inc_ref(v_infoState_582_);
lean_dec(v___x_581_);
v_trees_583_ = lean_ctor_get(v_infoState_582_, 2);
lean_inc_ref(v_trees_583_);
lean_dec_ref(v_infoState_582_);
v___x_584_ = lean_st_ref_take(v___y_579_);
v_infoState_585_ = lean_ctor_get(v___x_584_, 8);
v_env_586_ = lean_ctor_get(v___x_584_, 0);
v_nextMacroScope_587_ = lean_ctor_get(v___x_584_, 1);
v_ngen_588_ = lean_ctor_get(v___x_584_, 2);
v_auxDeclNGen_589_ = lean_ctor_get(v___x_584_, 3);
v_traceState_590_ = lean_ctor_get(v___x_584_, 4);
v_cache_591_ = lean_ctor_get(v___x_584_, 5);
v_recordedDeps_592_ = lean_ctor_get(v___x_584_, 6);
v_messages_593_ = lean_ctor_get(v___x_584_, 7);
v_snapshotTasks_594_ = lean_ctor_get(v___x_584_, 9);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_615_ == 0)
{
v___x_596_ = v___x_584_;
v_isShared_597_ = v_isSharedCheck_615_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snapshotTasks_594_);
lean_inc(v_infoState_585_);
lean_inc(v_messages_593_);
lean_inc(v_recordedDeps_592_);
lean_inc(v_cache_591_);
lean_inc(v_traceState_590_);
lean_inc(v_auxDeclNGen_589_);
lean_inc(v_ngen_588_);
lean_inc(v_nextMacroScope_587_);
lean_inc(v_env_586_);
lean_dec(v___x_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_615_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
uint8_t v_enabled_598_; lean_object* v_assignment_599_; lean_object* v_lazyAssignment_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_613_; 
v_enabled_598_ = lean_ctor_get_uint8(v_infoState_585_, sizeof(void*)*3);
v_assignment_599_ = lean_ctor_get(v_infoState_585_, 0);
v_lazyAssignment_600_ = lean_ctor_get(v_infoState_585_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_infoState_585_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_infoState_585_, 2);
lean_dec(v_unused_614_);
v___x_602_ = v_infoState_585_;
v_isShared_603_ = v_isSharedCheck_613_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_lazyAssignment_600_);
lean_inc(v_assignment_599_);
lean_dec(v_infoState_585_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_613_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 2, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_assignment_599_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_lazyAssignment_600_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v___x_604_);
lean_ctor_set_uint8(v_reuseFailAlloc_612_, sizeof(void*)*3, v_enabled_598_);
v___x_606_ = v_reuseFailAlloc_612_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 8, v___x_606_);
v___x_608_ = v___x_596_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_env_586_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_nextMacroScope_587_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_ngen_588_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_auxDeclNGen_589_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_traceState_590_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v_cache_591_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_recordedDeps_592_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_messages_593_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_611_, 9, v_snapshotTasks_594_);
v___x_608_ = v_reuseFailAlloc_611_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_st_ref_put(v___y_579_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_trees_583_);
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_616_);
lean_dec(v___y_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___f_650_; lean_object* v___x_83957__overap_651_; lean_object* v___x_652_; 
v___f_650_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_83957__overap_651_ = lean_panic_fn_borrowed(v___f_650_, v_msg_640_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
v___x_652_ = lean_apply_9(v___x_83957__overap_651_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, lean_box(0));
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_ref_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_ref_673_ = lean_ctor_get(v___y_670_, 2);
v___x_674_ = 0;
v___x_675_ = l_Lean_SourceInfo_fromRef(v_ref_673_, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Array_mkArray0___redArg();
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v_args_705_, lean_object* v_only_706_, uint8_t v___x_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___y_711_, lean_object* v_unfold_712_, uint8_t v___x_713_, lean_object* v_squeeze_714_, lean_object* v_loc_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; uint8_t v___y_788_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; uint8_t v___y_863_; 
if (lean_obj_tag(v_squeeze_714_) == 0)
{
uint8_t v___x_876_; 
v___x_876_ = 0;
v___y_863_ = v___x_876_;
goto v___jp_862_;
}
else
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v_squeeze_714_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_squeeze_714_, 0);
lean_dec(v_unused_1013_);
v___x_878_ = v_squeeze_714_;
v_isShared_879_ = v_isSharedCheck_1012_;
goto v_resetjp_877_;
}
else
{
lean_dec(v_squeeze_714_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_1012_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
if (v___x_713_ == 0)
{
lean_del_object(v___x_878_);
v___y_863_ = v___x_713_;
goto v___jp_862_;
}
else
{
if (lean_obj_tag(v_unfold_712_) == 0)
{
lean_object* v_ref_880_; uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_931_; 
v_ref_880_ = lean_ctor_get(v___y_722_, 2);
v___x_881_ = 0;
v___x_882_ = l_Lean_SourceInfo_fromRef(v_ref_880_, v___x_881_);
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9));
lean_inc_ref_n(v___x_710_, 2);
lean_inc_ref_n(v___x_709_, 2);
lean_inc_ref_n(v___x_708_, 2);
v___x_884_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_883_);
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10));
lean_inc_n(v___x_882_, 2);
v___x_886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_882_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_888_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
v___x_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_889_, 0, v___x_882_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_891_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_890_);
if (lean_obj_tag(v___y_711_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_931_ = v___x_940_;
goto v___jp_930_;
}
else
{
lean_object* v_val_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_val_941_ = lean_ctor_get(v___y_711_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v___y_711_, 1);
v___x_942_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___x_943_ = lean_array_push(v___x_942_, v_val_941_);
v___y_931_ = v___x_943_;
goto v___jp_930_;
}
v___jp_892_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_897_ = l_Array_append___redArg(v___x_888_, v___y_896_);
lean_dec_ref(v___y_896_);
lean_inc_n(v___x_882_, 2);
v___x_898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_898_, 0, v___x_882_);
lean_ctor_set(v___x_898_, 1, v___x_887_);
lean_ctor_set(v___x_898_, 2, v___x_897_);
v___x_899_ = l_Lean_Syntax_node5(v___x_882_, v___x_891_, v___x_703_, v___y_895_, v___y_893_, v___y_894_, v___x_898_);
v___x_900_ = l_Lean_Syntax_node3(v___x_882_, v___x_884_, v___x_886_, v___x_889_, v___x_899_);
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 0);
lean_ctor_set(v___x_878_, 0, v___x_900_);
v___x_902_ = v___x_878_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
v___jp_904_:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = l_Array_append___redArg(v___x_888_, v___y_907_);
lean_dec_ref(v___y_907_);
lean_inc(v___x_882_);
v___x_909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_909_, 0, v___x_882_);
lean_ctor_set(v___x_909_, 1, v___x_887_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
if (lean_obj_tag(v_loc_715_) == 1)
{
lean_object* v_val_910_; lean_object* v___x_911_; 
v_val_910_ = lean_ctor_get(v_loc_715_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v_loc_715_, 1);
v___x_911_ = l_Array_mkArray1___redArg(v_val_910_);
v___y_893_ = v___y_905_;
v___y_894_ = v___x_909_;
v___y_895_ = v___y_906_;
v___y_896_ = v___x_911_;
goto v___jp_892_;
}
else
{
lean_object* v___x_912_; 
lean_dec(v_loc_715_);
v___x_912_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_893_ = v___y_905_;
v___y_894_ = v___x_909_;
v___y_895_ = v___y_906_;
v___y_896_ = v___x_912_;
goto v___jp_892_;
}
}
v___jp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = l_Array_append___redArg(v___x_888_, v___y_915_);
lean_dec_ref(v___y_915_);
lean_inc(v___x_882_);
v___x_917_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_917_, 0, v___x_882_);
lean_ctor_set(v___x_917_, 1, v___x_887_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
if (lean_obj_tag(v_args_705_) == 1)
{
lean_object* v_val_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_val_918_ = lean_ctor_get(v_args_705_, 0);
v___x_919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_920_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_919_);
v___x_921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_882_, 4);
v___x_922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_882_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Array_append___redArg(v___x_888_, v_val_918_);
v___x_924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_924_, 0, v___x_882_);
lean_ctor_set(v___x_924_, 1, v___x_887_);
lean_ctor_set(v___x_924_, 2, v___x_923_);
v___x_925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_882_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l_Lean_Syntax_node3(v___x_882_, v___x_920_, v___x_922_, v___x_924_, v___x_926_);
v___x_928_ = l_Array_mkArray1___redArg(v___x_927_);
v___y_905_ = v___x_917_;
v___y_906_ = v___y_914_;
v___y_907_ = v___x_928_;
goto v___jp_904_;
}
else
{
lean_object* v___x_929_; 
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
v___x_929_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_905_ = v___x_917_;
v___y_906_ = v___y_914_;
v___y_907_ = v___x_929_;
goto v___jp_904_;
}
}
v___jp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = l_Array_append___redArg(v___x_888_, v___y_931_);
lean_dec_ref(v___y_931_);
lean_inc(v___x_882_);
v___x_933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_933_, 0, v___x_882_);
lean_ctor_set(v___x_933_, 1, v___x_887_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
if (lean_obj_tag(v_only_706_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_val_934_ = lean_ctor_get(v_only_706_, 0);
v___x_935_ = l_Lean_SourceInfo_fromRef(v_val_934_, v___x_707_);
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Array_mkArray1___redArg(v___x_937_);
v___y_914_ = v___x_933_;
v___y_915_ = v___x_938_;
goto v___jp_913_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_914_ = v___x_933_;
v___y_915_ = v___x_939_;
goto v___jp_913_;
}
}
}
else
{
lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_878_);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_unfold_712_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_unfold_712_, 0);
lean_dec(v_unused_1011_);
v___x_945_ = v_unfold_712_;
v_isShared_946_ = v_isSharedCheck_1010_;
goto v_resetjp_944_;
}
else
{
lean_dec(v_unfold_712_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_1010_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_ref_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_997_; 
v_ref_947_ = lean_ctor_get(v___y_722_, 2);
v___x_948_ = 0;
v___x_949_ = l_Lean_SourceInfo_fromRef(v_ref_947_, v___x_948_);
v___x_950_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13));
lean_inc_ref_n(v___x_710_, 2);
lean_inc_ref_n(v___x_709_, 2);
lean_inc_ref_n(v___x_708_, 2);
v___x_951_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_950_);
v___x_952_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14));
lean_inc(v___x_949_);
v___x_953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_949_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_955_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_954_);
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_957_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_711_) == 0)
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_997_ = v___x_1006_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_val_1007_ = lean_ctor_get(v___y_711_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v___y_711_, 1);
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___x_1009_ = lean_array_push(v___x_1008_, v_val_1007_);
v___y_997_ = v___x_1009_;
goto v___jp_996_;
}
v___jp_958_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_963_ = l_Array_append___redArg(v___x_957_, v___y_962_);
lean_dec_ref(v___y_962_);
lean_inc_n(v___x_949_, 2);
v___x_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_949_);
lean_ctor_set(v___x_964_, 1, v___x_956_);
lean_ctor_set(v___x_964_, 2, v___x_963_);
v___x_965_ = l_Lean_Syntax_node5(v___x_949_, v___x_955_, v___x_703_, v___y_960_, v___y_959_, v___y_961_, v___x_964_);
v___x_966_ = l_Lean_Syntax_node2(v___x_949_, v___x_951_, v___x_953_, v___x_965_);
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 0);
lean_ctor_set(v___x_945_, 0, v___x_966_);
v___x_968_ = v___x_945_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
v___jp_970_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = l_Array_append___redArg(v___x_957_, v___y_973_);
lean_dec_ref(v___y_973_);
lean_inc(v___x_949_);
v___x_975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_975_, 0, v___x_949_);
lean_ctor_set(v___x_975_, 1, v___x_956_);
lean_ctor_set(v___x_975_, 2, v___x_974_);
if (lean_obj_tag(v_loc_715_) == 1)
{
lean_object* v_val_976_; lean_object* v___x_977_; 
v_val_976_ = lean_ctor_get(v_loc_715_, 0);
lean_inc(v_val_976_);
lean_dec_ref_known(v_loc_715_, 1);
v___x_977_ = l_Array_mkArray1___redArg(v_val_976_);
v___y_959_ = v___y_971_;
v___y_960_ = v___y_972_;
v___y_961_ = v___x_975_;
v___y_962_ = v___x_977_;
goto v___jp_958_;
}
else
{
lean_object* v___x_978_; 
lean_dec(v_loc_715_);
v___x_978_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_959_ = v___y_971_;
v___y_960_ = v___y_972_;
v___y_961_ = v___x_975_;
v___y_962_ = v___x_978_;
goto v___jp_958_;
}
}
v___jp_979_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = l_Array_append___redArg(v___x_957_, v___y_981_);
lean_dec_ref(v___y_981_);
lean_inc(v___x_949_);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v___x_949_);
lean_ctor_set(v___x_983_, 1, v___x_956_);
lean_ctor_set(v___x_983_, 2, v___x_982_);
if (lean_obj_tag(v_args_705_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_val_984_ = lean_ctor_get(v_args_705_, 0);
v___x_985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_986_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_985_);
v___x_987_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_949_, 4);
v___x_988_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_949_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = l_Array_append___redArg(v___x_957_, v_val_984_);
v___x_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_990_, 0, v___x_949_);
lean_ctor_set(v___x_990_, 1, v___x_956_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
v___x_991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_992_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_949_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_Syntax_node3(v___x_949_, v___x_986_, v___x_988_, v___x_990_, v___x_992_);
v___x_994_ = l_Array_mkArray1___redArg(v___x_993_);
v___y_971_ = v___x_983_;
v___y_972_ = v___y_980_;
v___y_973_ = v___x_994_;
goto v___jp_970_;
}
else
{
lean_object* v___x_995_; 
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v___x_708_);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_971_ = v___x_983_;
v___y_972_ = v___y_980_;
v___y_973_ = v___x_995_;
goto v___jp_970_;
}
}
v___jp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = l_Array_append___redArg(v___x_957_, v___y_997_);
lean_dec_ref(v___y_997_);
lean_inc(v___x_949_);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___x_949_);
lean_ctor_set(v___x_999_, 1, v___x_956_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
if (lean_obj_tag(v_only_706_) == 1)
{
lean_object* v_val_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_val_1000_ = lean_ctor_get(v_only_706_, 0);
v___x_1001_ = l_Lean_SourceInfo_fromRef(v_val_1000_, v___x_707_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Array_mkArray1___redArg(v___x_1003_);
v___y_980_ = v___x_999_;
v___y_981_ = v___x_1004_;
goto v___jp_979_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_980_ = v___x_999_;
v___y_981_ = v___x_1005_;
goto v___jp_979_;
}
}
}
}
}
}
}
v___jp_725_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_inc_ref(v___y_729_);
v___x_735_ = l_Array_append___redArg(v___y_729_, v___y_734_);
lean_dec_ref(v___y_734_);
lean_inc(v___y_727_);
lean_inc(v___y_731_);
v___x_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_736_, 0, v___y_731_);
lean_ctor_set(v___x_736_, 1, v___y_727_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = l_Lean_Syntax_node6(v___y_731_, v___y_728_, v___y_726_, v___x_703_, v___y_732_, v___y_730_, v___y_733_, v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
v___jp_739_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_inc_ref(v___y_743_);
v___x_748_ = l_Array_append___redArg(v___y_743_, v___y_747_);
lean_dec_ref(v___y_747_);
lean_inc(v___y_741_);
lean_inc(v___y_745_);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v___y_745_);
lean_ctor_set(v___x_749_, 1, v___y_741_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
if (lean_obj_tag(v_loc_715_) == 1)
{
lean_object* v_val_750_; lean_object* v___x_751_; 
v_val_750_ = lean_ctor_get(v_loc_715_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v_loc_715_, 1);
v___x_751_ = l_Array_mkArray1___redArg(v_val_750_);
v___y_726_ = v___y_740_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_742_;
v___y_729_ = v___y_743_;
v___y_730_ = v___y_744_;
v___y_731_ = v___y_745_;
v___y_732_ = v___y_746_;
v___y_733_ = v___x_749_;
v___y_734_ = v___x_751_;
goto v___jp_725_;
}
else
{
lean_object* v___x_752_; 
lean_dec(v_loc_715_);
v___x_752_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_726_ = v___y_740_;
v___y_727_ = v___y_741_;
v___y_728_ = v___y_742_;
v___y_729_ = v___y_743_;
v___y_730_ = v___y_744_;
v___y_731_ = v___y_745_;
v___y_732_ = v___y_746_;
v___y_733_ = v___x_749_;
v___y_734_ = v___x_752_;
goto v___jp_725_;
}
}
v___jp_753_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_inc_ref(v___y_757_);
v___x_761_ = l_Array_append___redArg(v___y_757_, v___y_760_);
lean_dec_ref(v___y_760_);
lean_inc(v___y_755_);
lean_inc(v___y_758_);
v___x_762_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_762_, 0, v___y_758_);
lean_ctor_set(v___x_762_, 1, v___y_755_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
if (lean_obj_tag(v_args_705_) == 1)
{
lean_object* v_val_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_val_763_ = lean_ctor_get(v_args_705_, 0);
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_758_, 3);
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v___y_758_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_inc_ref(v___y_757_);
v___x_766_ = l_Array_append___redArg(v___y_757_, v_val_763_);
lean_inc(v___y_755_);
v___x_767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_767_, 0, v___y_758_);
lean_ctor_set(v___x_767_, 1, v___y_755_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___y_758_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = l_Array_mkArray3___redArg(v___x_765_, v___x_767_, v___x_769_);
v___y_740_ = v___y_754_;
v___y_741_ = v___y_755_;
v___y_742_ = v___y_756_;
v___y_743_ = v___y_757_;
v___y_744_ = v___x_762_;
v___y_745_ = v___y_758_;
v___y_746_ = v___y_759_;
v___y_747_ = v___x_770_;
goto v___jp_739_;
}
else
{
lean_object* v___x_771_; 
v___x_771_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_740_ = v___y_754_;
v___y_741_ = v___y_755_;
v___y_742_ = v___y_756_;
v___y_743_ = v___y_757_;
v___y_744_ = v___x_762_;
v___y_745_ = v___y_758_;
v___y_746_ = v___y_759_;
v___y_747_ = v___x_771_;
goto v___jp_739_;
}
}
v___jp_772_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_inc_ref(v___y_776_);
v___x_779_ = l_Array_append___redArg(v___y_776_, v___y_778_);
lean_dec_ref(v___y_778_);
lean_inc(v___y_774_);
lean_inc(v___y_777_);
v___x_780_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_780_, 0, v___y_777_);
lean_ctor_set(v___x_780_, 1, v___y_774_);
lean_ctor_set(v___x_780_, 2, v___x_779_);
if (lean_obj_tag(v_only_706_) == 1)
{
lean_object* v_val_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_val_781_ = lean_ctor_get(v_only_706_, 0);
v___x_782_ = l_Lean_SourceInfo_fromRef(v_val_781_, v___x_707_);
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Array_mkArray1___redArg(v___x_784_);
v___y_754_ = v___y_773_;
v___y_755_ = v___y_774_;
v___y_756_ = v___y_775_;
v___y_757_ = v___y_776_;
v___y_758_ = v___y_777_;
v___y_759_ = v___x_780_;
v___y_760_ = v___x_785_;
goto v___jp_753_;
}
else
{
lean_object* v___x_786_; 
v___x_786_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_754_ = v___y_773_;
v___y_755_ = v___y_774_;
v___y_756_ = v___y_775_;
v___y_757_ = v___y_776_;
v___y_758_ = v___y_777_;
v___y_759_ = v___x_780_;
v___y_760_ = v___x_786_;
goto v___jp_753_;
}
}
v___jp_787_:
{
lean_object* v_ref_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_ref_789_ = lean_ctor_get(v___y_722_, 2);
v___x_790_ = l_Lean_SourceInfo_fromRef(v_ref_789_, v___y_788_);
v___x_791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
v___x_792_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_791_);
lean_inc(v___x_790_);
v___x_793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_790_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
v___x_794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_795_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_711_) == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_773_ = v___x_793_;
v___y_774_ = v___x_794_;
v___y_775_ = v___x_792_;
v___y_776_ = v___x_795_;
v___y_777_ = v___x_790_;
v___y_778_ = v___x_796_;
goto v___jp_772_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_val_797_ = lean_ctor_get(v___y_711_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___y_711_, 1);
v___x_798_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___x_799_ = lean_array_push(v___x_798_, v_val_797_);
v___y_773_ = v___x_793_;
v___y_774_ = v___x_794_;
v___y_775_ = v___x_792_;
v___y_776_ = v___x_795_;
v___y_777_ = v___x_790_;
v___y_778_ = v___x_799_;
goto v___jp_772_;
}
}
v___jp_800_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_inc_ref(v___y_806_);
v___x_810_ = l_Array_append___redArg(v___y_806_, v___y_809_);
lean_dec_ref(v___y_809_);
lean_inc(v___y_802_);
lean_inc(v___y_804_);
v___x_811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_811_, 0, v___y_804_);
lean_ctor_set(v___x_811_, 1, v___y_802_);
lean_ctor_set(v___x_811_, 2, v___x_810_);
v___x_812_ = l_Lean_Syntax_node6(v___y_804_, v___y_805_, v___y_807_, v___x_703_, v___y_803_, v___y_801_, v___y_808_, v___x_811_);
v___x_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
return v___x_813_;
}
v___jp_814_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc_ref(v___y_820_);
v___x_823_ = l_Array_append___redArg(v___y_820_, v___y_822_);
lean_dec_ref(v___y_822_);
lean_inc(v___y_816_);
lean_inc(v___y_818_);
v___x_824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_824_, 0, v___y_818_);
lean_ctor_set(v___x_824_, 1, v___y_816_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
if (lean_obj_tag(v_loc_715_) == 1)
{
lean_object* v_val_825_; lean_object* v___x_826_; 
v_val_825_ = lean_ctor_get(v_loc_715_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v_loc_715_, 1);
v___x_826_ = l_Array_mkArray1___redArg(v_val_825_);
v___y_801_ = v___y_815_;
v___y_802_ = v___y_816_;
v___y_803_ = v___y_817_;
v___y_804_ = v___y_818_;
v___y_805_ = v___y_819_;
v___y_806_ = v___y_820_;
v___y_807_ = v___y_821_;
v___y_808_ = v___x_824_;
v___y_809_ = v___x_826_;
goto v___jp_800_;
}
else
{
lean_object* v___x_827_; 
lean_dec(v_loc_715_);
v___x_827_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_801_ = v___y_815_;
v___y_802_ = v___y_816_;
v___y_803_ = v___y_817_;
v___y_804_ = v___y_818_;
v___y_805_ = v___y_819_;
v___y_806_ = v___y_820_;
v___y_807_ = v___y_821_;
v___y_808_ = v___x_824_;
v___y_809_ = v___x_827_;
goto v___jp_800_;
}
}
v___jp_828_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_inc_ref(v___y_833_);
v___x_836_ = l_Array_append___redArg(v___y_833_, v___y_835_);
lean_dec_ref(v___y_835_);
lean_inc(v___y_829_);
lean_inc(v___y_831_);
v___x_837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_837_, 0, v___y_831_);
lean_ctor_set(v___x_837_, 1, v___y_829_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
if (lean_obj_tag(v_args_705_) == 1)
{
lean_object* v_val_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_val_838_ = lean_ctor_get(v_args_705_, 0);
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_831_, 3);
v___x_840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_840_, 0, v___y_831_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
lean_inc_ref(v___y_833_);
v___x_841_ = l_Array_append___redArg(v___y_833_, v_val_838_);
lean_inc(v___y_829_);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___y_831_);
lean_ctor_set(v___x_842_, 1, v___y_829_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_844_, 0, v___y_831_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = l_Array_mkArray3___redArg(v___x_840_, v___x_842_, v___x_844_);
v___y_815_ = v___x_837_;
v___y_816_ = v___y_829_;
v___y_817_ = v___y_830_;
v___y_818_ = v___y_831_;
v___y_819_ = v___y_832_;
v___y_820_ = v___y_833_;
v___y_821_ = v___y_834_;
v___y_822_ = v___x_845_;
goto v___jp_814_;
}
else
{
lean_object* v___x_846_; 
v___x_846_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_815_ = v___x_837_;
v___y_816_ = v___y_829_;
v___y_817_ = v___y_830_;
v___y_818_ = v___y_831_;
v___y_819_ = v___y_832_;
v___y_820_ = v___y_833_;
v___y_821_ = v___y_834_;
v___y_822_ = v___x_846_;
goto v___jp_814_;
}
}
v___jp_847_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_inc_ref(v___y_851_);
v___x_854_ = l_Array_append___redArg(v___y_851_, v___y_853_);
lean_dec_ref(v___y_853_);
lean_inc(v___y_848_);
lean_inc(v___y_849_);
v___x_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_855_, 0, v___y_849_);
lean_ctor_set(v___x_855_, 1, v___y_848_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
if (lean_obj_tag(v_only_706_) == 1)
{
lean_object* v_val_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_val_856_ = lean_ctor_get(v_only_706_, 0);
v___x_857_ = l_Lean_SourceInfo_fromRef(v_val_856_, v___x_707_);
v___x_858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = l_Array_mkArray1___redArg(v___x_859_);
v___y_829_ = v___y_848_;
v___y_830_ = v___x_855_;
v___y_831_ = v___y_849_;
v___y_832_ = v___y_850_;
v___y_833_ = v___y_851_;
v___y_834_ = v___y_852_;
v___y_835_ = v___x_860_;
goto v___jp_828_;
}
else
{
lean_object* v___x_861_; 
v___x_861_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_829_ = v___y_848_;
v___y_830_ = v___x_855_;
v___y_831_ = v___y_849_;
v___y_832_ = v___y_850_;
v___y_833_ = v___y_851_;
v___y_834_ = v___y_852_;
v___y_835_ = v___x_861_;
goto v___jp_828_;
}
}
v___jp_862_:
{
if (lean_obj_tag(v_unfold_712_) == 0)
{
v___y_788_ = v___y_863_;
goto v___jp_787_;
}
else
{
lean_dec_ref_known(v_unfold_712_, 1);
if (v___x_713_ == 0)
{
v___y_788_ = v___x_713_;
goto v___jp_787_;
}
else
{
lean_object* v_ref_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_ref_864_ = lean_ctor_get(v___y_722_, 2);
v___x_865_ = l_Lean_SourceInfo_fromRef(v_ref_864_, v___y_863_);
v___x_866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7));
v___x_867_ = l_Lean_Name_mkStr4(v___x_708_, v___x_709_, v___x_710_, v___x_866_);
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8));
lean_inc(v___x_865_);
v___x_869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_865_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_871_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_711_) == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___y_848_ = v___x_870_;
v___y_849_ = v___x_865_;
v___y_850_ = v___x_867_;
v___y_851_ = v___x_871_;
v___y_852_ = v___x_869_;
v___y_853_ = v___x_872_;
goto v___jp_847_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_val_873_ = lean_ctor_get(v___y_711_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v___y_711_, 1);
v___x_874_ = lean_mk_empty_array_with_capacity(v___x_704_);
v___x_875_ = lean_array_push(v___x_874_, v_val_873_);
v___y_848_ = v___x_870_;
v___y_849_ = v___x_865_;
v___y_850_ = v___x_867_;
v___y_851_ = v___x_871_;
v___y_852_ = v___x_869_;
v___y_853_ = v___x_875_;
goto v___jp_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_1014_ = _args[0];
lean_object* v___x_1015_ = _args[1];
lean_object* v_args_1016_ = _args[2];
lean_object* v_only_1017_ = _args[3];
lean_object* v___x_1018_ = _args[4];
lean_object* v___x_1019_ = _args[5];
lean_object* v___x_1020_ = _args[6];
lean_object* v___x_1021_ = _args[7];
lean_object* v___y_1022_ = _args[8];
lean_object* v_unfold_1023_ = _args[9];
lean_object* v___x_1024_ = _args[10];
lean_object* v_squeeze_1025_ = _args[11];
lean_object* v_loc_1026_ = _args[12];
lean_object* v___y_1027_ = _args[13];
lean_object* v___y_1028_ = _args[14];
lean_object* v___y_1029_ = _args[15];
lean_object* v___y_1030_ = _args[16];
lean_object* v___y_1031_ = _args[17];
lean_object* v___y_1032_ = _args[18];
lean_object* v___y_1033_ = _args[19];
lean_object* v___y_1034_ = _args[20];
lean_object* v___y_1035_ = _args[21];
_start:
{
uint8_t v___x_93207__boxed_1036_; uint8_t v___x_93212__boxed_1037_; lean_object* v_res_1038_; 
v___x_93207__boxed_1036_ = lean_unbox(v___x_1018_);
v___x_93212__boxed_1037_ = lean_unbox(v___x_1024_);
v_res_1038_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_1014_, v___x_1015_, v_args_1016_, v_only_1017_, v___x_93207__boxed_1036_, v___x_1019_, v___x_1020_, v___x_1021_, v___y_1022_, v_unfold_1023_, v___x_93212__boxed_1037_, v_squeeze_1025_, v_loc_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v_only_1017_);
lean_dec(v_args_1016_);
lean_dec(v___x_1015_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_1039_, lean_object* v_trees_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
v___x_1050_ = lean_apply_9(v_a_1039_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1051_);
lean_ctor_set(v___x_1055_, 1, v_trees_1040_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec_ref(v_trees_1040_);
v_a_1060_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1050_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1050_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object* v_a_1068_, lean_object* v_trees_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1068_, v_trees_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1079_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1086_, lean_object* v_a_1087_, uint8_t v___x_1088_, lean_object* v_a_1089_, lean_object* v_mvarCounter_1090_, lean_object* v___x_1091_, uint8_t v___x_1092_, lean_object* v___x_1093_, uint8_t v_useReducible_1094_, uint8_t v___x_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
lean_inc(v_a_1086_);
v___x_1105_ = l_Lean_MVarId_getType(v_a_1086_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_n(v_a_1106_, 2);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = l_Lean_mkIdent(v_a_1087_);
v___x_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_a_1106_);
v___x_1109_ = l_Lean_Elab_Term_elabTerm(v___x_1107_, v___x_1108_, v___x_1088_, v___x_1088_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___x_1144_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1144_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1092_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1327_; 
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v___x_1144_, 0);
lean_dec(v_unused_1328_);
v___x_1146_ = v___x_1144_;
v_isShared_1147_ = v_isSharedCheck_1327_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v___x_1144_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1327_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; 
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v_a_1110_);
v___x_1148_ = lean_infer_type(v_a_1110_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; uint8_t v_____do__lift_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1170_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
if (v_useReducible_1094_ == 0)
{
lean_object* v___x_1181_; uint8_t v_foApprox_1182_; uint8_t v_ctxApprox_1183_; uint8_t v_quasiPatternApprox_1184_; uint8_t v_constApprox_1185_; uint8_t v_isDefEqStuckEx_1186_; uint8_t v_unificationHints_1187_; uint8_t v_proofIrrelevance_1188_; uint8_t v_offsetCnstrs_1189_; uint8_t v_transparency_1190_; uint8_t v_etaStruct_1191_; uint8_t v_univApprox_1192_; uint8_t v_iota_1193_; uint8_t v_beta_1194_; uint8_t v_proj_1195_; uint8_t v_zeta_1196_; uint8_t v_zetaDelta_1197_; uint8_t v_zetaUnused_1198_; uint8_t v_zetaHave_1199_; uint8_t v_canUnfoldPredicateConfig_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1231_; 
v___x_1181_ = l_Lean_Meta_Context_config(v___y_1100_);
v_foApprox_1182_ = lean_ctor_get_uint8(v___x_1181_, 0);
v_ctxApprox_1183_ = lean_ctor_get_uint8(v___x_1181_, 1);
v_quasiPatternApprox_1184_ = lean_ctor_get_uint8(v___x_1181_, 2);
v_constApprox_1185_ = lean_ctor_get_uint8(v___x_1181_, 3);
v_isDefEqStuckEx_1186_ = lean_ctor_get_uint8(v___x_1181_, 4);
v_unificationHints_1187_ = lean_ctor_get_uint8(v___x_1181_, 5);
v_proofIrrelevance_1188_ = lean_ctor_get_uint8(v___x_1181_, 6);
v_offsetCnstrs_1189_ = lean_ctor_get_uint8(v___x_1181_, 8);
v_transparency_1190_ = lean_ctor_get_uint8(v___x_1181_, 9);
v_etaStruct_1191_ = lean_ctor_get_uint8(v___x_1181_, 10);
v_univApprox_1192_ = lean_ctor_get_uint8(v___x_1181_, 11);
v_iota_1193_ = lean_ctor_get_uint8(v___x_1181_, 12);
v_beta_1194_ = lean_ctor_get_uint8(v___x_1181_, 13);
v_proj_1195_ = lean_ctor_get_uint8(v___x_1181_, 14);
v_zeta_1196_ = lean_ctor_get_uint8(v___x_1181_, 15);
v_zetaDelta_1197_ = lean_ctor_get_uint8(v___x_1181_, 16);
v_zetaUnused_1198_ = lean_ctor_get_uint8(v___x_1181_, 17);
v_zetaHave_1199_ = lean_ctor_get_uint8(v___x_1181_, 18);
v_canUnfoldPredicateConfig_1200_ = lean_ctor_get_uint8(v___x_1181_, 19);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1202_ = v___x_1181_;
v_isShared_1203_ = v_isSharedCheck_1231_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v___x_1181_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1231_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
uint8_t v_trackZetaDelta_1204_; lean_object* v_zetaDeltaSet_1205_; lean_object* v_lctx_1206_; lean_object* v_localInstances_1207_; lean_object* v_defEqCtx_x3f_1208_; lean_object* v_synthPendingDepth_1209_; lean_object* v_customCanUnfoldPredicate_x3f_1210_; uint8_t v_univApprox_1211_; uint8_t v_inTypeClassResolution_1212_; uint8_t v_cacheInferType_1213_; lean_object* v___x_1215_; 
v_trackZetaDelta_1204_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7);
v_zetaDeltaSet_1205_ = lean_ctor_get(v___y_1100_, 1);
v_lctx_1206_ = lean_ctor_get(v___y_1100_, 2);
v_localInstances_1207_ = lean_ctor_get(v___y_1100_, 3);
v_defEqCtx_x3f_1208_ = lean_ctor_get(v___y_1100_, 4);
v_synthPendingDepth_1209_ = lean_ctor_get(v___y_1100_, 5);
v_customCanUnfoldPredicate_x3f_1210_ = lean_ctor_get(v___y_1100_, 6);
v_univApprox_1211_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1212_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 2);
v_cacheInferType_1213_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 3);
if (v_isShared_1203_ == 0)
{
v___x_1215_ = v___x_1202_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 0, v_foApprox_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 1, v_ctxApprox_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 2, v_quasiPatternApprox_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 3, v_constApprox_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 4, v_isDefEqStuckEx_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 5, v_unificationHints_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 6, v_proofIrrelevance_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 8, v_offsetCnstrs_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 9, v_transparency_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 10, v_etaStruct_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 11, v_univApprox_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 12, v_iota_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 13, v_beta_1194_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 14, v_proj_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 15, v_zeta_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 16, v_zetaDelta_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 17, v_zetaUnused_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 18, v_zetaHave_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, 19, v_canUnfoldPredicateConfig_1200_);
v___x_1215_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
uint64_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_ctor_set_uint8(v___x_1215_, 7, v___x_1095_);
v___x_1216_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set_uint64(v___x_1217_, sizeof(void*)*1, v___x_1216_);
lean_inc(v_customCanUnfoldPredicate_x3f_1210_);
lean_inc(v_synthPendingDepth_1209_);
lean_inc(v_defEqCtx_x3f_1208_);
lean_inc_ref(v_localInstances_1207_);
lean_inc_ref(v_lctx_1206_);
lean_inc(v_zetaDeltaSet_1205_);
v___x_1218_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_zetaDeltaSet_1205_);
lean_ctor_set(v___x_1218_, 2, v_lctx_1206_);
lean_ctor_set(v___x_1218_, 3, v_localInstances_1207_);
lean_ctor_set(v___x_1218_, 4, v_defEqCtx_x3f_1208_);
lean_ctor_set(v___x_1218_, 5, v_synthPendingDepth_1209_);
lean_ctor_set(v___x_1218_, 6, v_customCanUnfoldPredicate_x3f_1210_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*7, v_trackZetaDelta_1204_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*7 + 1, v_univApprox_1211_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1212_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*7 + 3, v_cacheInferType_1213_);
lean_inc(v_a_1149_);
lean_inc(v_a_1106_);
v___x_1219_ = l_Lean_Meta_isExprDefEq(v_a_1106_, v_a_1149_, v___x_1218_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref_known(v___x_1218_, 7);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; uint8_t v___x_1221_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = lean_unbox(v_a_1220_);
lean_dec(v_a_1220_);
v_____do__lift_1151_ = v___x_1221_;
v___y_1152_ = v___y_1096_;
v___y_1153_ = v___y_1097_;
v___y_1154_ = v___y_1098_;
v___y_1155_ = v___y_1099_;
v___y_1156_ = v___y_1100_;
v___y_1157_ = v___y_1101_;
v___y_1158_ = v___y_1102_;
v___y_1159_ = v___y_1103_;
goto v___jp_1150_;
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_a_1149_);
lean_del_object(v___x_1146_);
lean_dec(v_a_1110_);
lean_dec(v_a_1106_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___x_1093_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
v_a_1222_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1219_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1219_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
else
{
lean_object* v___x_1232_; uint8_t v_foApprox_1233_; uint8_t v_ctxApprox_1234_; uint8_t v_quasiPatternApprox_1235_; uint8_t v_constApprox_1236_; uint8_t v_isDefEqStuckEx_1237_; uint8_t v_unificationHints_1238_; uint8_t v_proofIrrelevance_1239_; uint8_t v_offsetCnstrs_1240_; uint8_t v_transparency_1241_; uint8_t v_etaStruct_1242_; uint8_t v_univApprox_1243_; uint8_t v_iota_1244_; uint8_t v_beta_1245_; uint8_t v_proj_1246_; uint8_t v_zeta_1247_; uint8_t v_zetaDelta_1248_; uint8_t v_zetaUnused_1249_; uint8_t v_zetaHave_1250_; uint8_t v_canUnfoldPredicateConfig_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1318_; 
v___x_1232_ = l_Lean_Meta_Context_config(v___y_1100_);
v_foApprox_1233_ = lean_ctor_get_uint8(v___x_1232_, 0);
v_ctxApprox_1234_ = lean_ctor_get_uint8(v___x_1232_, 1);
v_quasiPatternApprox_1235_ = lean_ctor_get_uint8(v___x_1232_, 2);
v_constApprox_1236_ = lean_ctor_get_uint8(v___x_1232_, 3);
v_isDefEqStuckEx_1237_ = lean_ctor_get_uint8(v___x_1232_, 4);
v_unificationHints_1238_ = lean_ctor_get_uint8(v___x_1232_, 5);
v_proofIrrelevance_1239_ = lean_ctor_get_uint8(v___x_1232_, 6);
v_offsetCnstrs_1240_ = lean_ctor_get_uint8(v___x_1232_, 8);
v_transparency_1241_ = lean_ctor_get_uint8(v___x_1232_, 9);
v_etaStruct_1242_ = lean_ctor_get_uint8(v___x_1232_, 10);
v_univApprox_1243_ = lean_ctor_get_uint8(v___x_1232_, 11);
v_iota_1244_ = lean_ctor_get_uint8(v___x_1232_, 12);
v_beta_1245_ = lean_ctor_get_uint8(v___x_1232_, 13);
v_proj_1246_ = lean_ctor_get_uint8(v___x_1232_, 14);
v_zeta_1247_ = lean_ctor_get_uint8(v___x_1232_, 15);
v_zetaDelta_1248_ = lean_ctor_get_uint8(v___x_1232_, 16);
v_zetaUnused_1249_ = lean_ctor_get_uint8(v___x_1232_, 17);
v_zetaHave_1250_ = lean_ctor_get_uint8(v___x_1232_, 18);
v_canUnfoldPredicateConfig_1251_ = lean_ctor_get_uint8(v___x_1232_, 19);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1253_ = v___x_1232_;
v_isShared_1254_ = v_isSharedCheck_1318_;
goto v_resetjp_1252_;
}
else
{
lean_dec(v___x_1232_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1318_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
uint8_t v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = 2;
v___x_1256_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1241_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v_keyedConfig_1257_; uint8_t v_trackZetaDelta_1258_; lean_object* v_zetaDeltaSet_1259_; lean_object* v_lctx_1260_; lean_object* v_localInstances_1261_; lean_object* v_defEqCtx_x3f_1262_; lean_object* v_synthPendingDepth_1263_; lean_object* v_customCanUnfoldPredicate_x3f_1264_; uint8_t v_univApprox_1265_; uint8_t v_inTypeClassResolution_1266_; uint8_t v_cacheInferType_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v_foApprox_1271_; uint8_t v_ctxApprox_1272_; uint8_t v_quasiPatternApprox_1273_; uint8_t v_constApprox_1274_; uint8_t v_isDefEqStuckEx_1275_; uint8_t v_unificationHints_1276_; uint8_t v_proofIrrelevance_1277_; uint8_t v_offsetCnstrs_1278_; uint8_t v_transparency_1279_; uint8_t v_etaStruct_1280_; uint8_t v_univApprox_1281_; uint8_t v_iota_1282_; uint8_t v_beta_1283_; uint8_t v_proj_1284_; uint8_t v_zeta_1285_; uint8_t v_zetaDelta_1286_; uint8_t v_zetaUnused_1287_; uint8_t v_zetaHave_1288_; uint8_t v_canUnfoldPredicateConfig_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1300_; 
lean_del_object(v___x_1253_);
v_keyedConfig_1257_ = lean_ctor_get(v___y_1100_, 0);
v_trackZetaDelta_1258_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7);
v_zetaDeltaSet_1259_ = lean_ctor_get(v___y_1100_, 1);
v_lctx_1260_ = lean_ctor_get(v___y_1100_, 2);
v_localInstances_1261_ = lean_ctor_get(v___y_1100_, 3);
v_defEqCtx_x3f_1262_ = lean_ctor_get(v___y_1100_, 4);
v_synthPendingDepth_1263_ = lean_ctor_get(v___y_1100_, 5);
v_customCanUnfoldPredicate_x3f_1264_ = lean_ctor_get(v___y_1100_, 6);
v_univApprox_1265_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1266_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 2);
v_cacheInferType_1267_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1257_);
v___x_1268_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1255_, v_keyedConfig_1257_);
lean_inc(v_customCanUnfoldPredicate_x3f_1264_);
lean_inc(v_synthPendingDepth_1263_);
lean_inc(v_defEqCtx_x3f_1262_);
lean_inc_ref(v_localInstances_1261_);
lean_inc_ref(v_lctx_1260_);
lean_inc(v_zetaDeltaSet_1259_);
v___x_1269_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v_zetaDeltaSet_1259_);
lean_ctor_set(v___x_1269_, 2, v_lctx_1260_);
lean_ctor_set(v___x_1269_, 3, v_localInstances_1261_);
lean_ctor_set(v___x_1269_, 4, v_defEqCtx_x3f_1262_);
lean_ctor_set(v___x_1269_, 5, v_synthPendingDepth_1263_);
lean_ctor_set(v___x_1269_, 6, v_customCanUnfoldPredicate_x3f_1264_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*7, v_trackZetaDelta_1258_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*7 + 1, v_univApprox_1265_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1266_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*7 + 3, v_cacheInferType_1267_);
v___x_1270_ = l_Lean_Meta_Context_config(v___x_1269_);
lean_dec_ref_known(v___x_1269_, 7);
v_foApprox_1271_ = lean_ctor_get_uint8(v___x_1270_, 0);
v_ctxApprox_1272_ = lean_ctor_get_uint8(v___x_1270_, 1);
v_quasiPatternApprox_1273_ = lean_ctor_get_uint8(v___x_1270_, 2);
v_constApprox_1274_ = lean_ctor_get_uint8(v___x_1270_, 3);
v_isDefEqStuckEx_1275_ = lean_ctor_get_uint8(v___x_1270_, 4);
v_unificationHints_1276_ = lean_ctor_get_uint8(v___x_1270_, 5);
v_proofIrrelevance_1277_ = lean_ctor_get_uint8(v___x_1270_, 6);
v_offsetCnstrs_1278_ = lean_ctor_get_uint8(v___x_1270_, 8);
v_transparency_1279_ = lean_ctor_get_uint8(v___x_1270_, 9);
v_etaStruct_1280_ = lean_ctor_get_uint8(v___x_1270_, 10);
v_univApprox_1281_ = lean_ctor_get_uint8(v___x_1270_, 11);
v_iota_1282_ = lean_ctor_get_uint8(v___x_1270_, 12);
v_beta_1283_ = lean_ctor_get_uint8(v___x_1270_, 13);
v_proj_1284_ = lean_ctor_get_uint8(v___x_1270_, 14);
v_zeta_1285_ = lean_ctor_get_uint8(v___x_1270_, 15);
v_zetaDelta_1286_ = lean_ctor_get_uint8(v___x_1270_, 16);
v_zetaUnused_1287_ = lean_ctor_get_uint8(v___x_1270_, 17);
v_zetaHave_1288_ = lean_ctor_get_uint8(v___x_1270_, 18);
v_canUnfoldPredicateConfig_1289_ = lean_ctor_get_uint8(v___x_1270_, 19);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1291_ = v___x_1270_;
v_isShared_1292_ = v_isSharedCheck_1300_;
goto v_resetjp_1290_;
}
else
{
lean_dec(v___x_1270_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1300_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 0, v_foApprox_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 1, v_ctxApprox_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 2, v_quasiPatternApprox_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 3, v_constApprox_1274_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 4, v_isDefEqStuckEx_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 5, v_unificationHints_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 6, v_proofIrrelevance_1277_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 8, v_offsetCnstrs_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 9, v_transparency_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 10, v_etaStruct_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 11, v_univApprox_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 12, v_iota_1282_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 13, v_beta_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 14, v_proj_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 15, v_zeta_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 16, v_zetaDelta_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 17, v_zetaUnused_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 18, v_zetaHave_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, 19, v_canUnfoldPredicateConfig_1289_);
v___x_1294_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
uint64_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_ctor_set_uint8(v___x_1294_, 7, v___x_1095_);
v___x_1295_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1294_);
v___x_1296_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set_uint64(v___x_1296_, sizeof(void*)*1, v___x_1295_);
lean_inc(v_customCanUnfoldPredicate_x3f_1264_);
lean_inc(v_synthPendingDepth_1263_);
lean_inc(v_defEqCtx_x3f_1262_);
lean_inc_ref(v_localInstances_1261_);
lean_inc_ref(v_lctx_1260_);
lean_inc(v_zetaDeltaSet_1259_);
v___x_1297_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v_zetaDeltaSet_1259_);
lean_ctor_set(v___x_1297_, 2, v_lctx_1260_);
lean_ctor_set(v___x_1297_, 3, v_localInstances_1261_);
lean_ctor_set(v___x_1297_, 4, v_defEqCtx_x3f_1262_);
lean_ctor_set(v___x_1297_, 5, v_synthPendingDepth_1263_);
lean_ctor_set(v___x_1297_, 6, v_customCanUnfoldPredicate_x3f_1264_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*7, v_trackZetaDelta_1258_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*7 + 1, v_univApprox_1265_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1266_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*7 + 3, v_cacheInferType_1267_);
lean_inc(v_a_1149_);
lean_inc(v_a_1106_);
v___x_1298_ = l_Lean_Meta_isExprDefEq(v_a_1106_, v_a_1149_, v___x_1297_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref_known(v___x_1297_, 7);
v___y_1170_ = v___x_1298_;
goto v___jp_1169_;
}
}
}
else
{
uint8_t v_trackZetaDelta_1301_; lean_object* v_zetaDeltaSet_1302_; lean_object* v_lctx_1303_; lean_object* v_localInstances_1304_; lean_object* v_defEqCtx_x3f_1305_; lean_object* v_synthPendingDepth_1306_; lean_object* v_customCanUnfoldPredicate_x3f_1307_; uint8_t v_univApprox_1308_; uint8_t v_inTypeClassResolution_1309_; uint8_t v_cacheInferType_1310_; lean_object* v___x_1312_; 
v_trackZetaDelta_1301_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7);
v_zetaDeltaSet_1302_ = lean_ctor_get(v___y_1100_, 1);
v_lctx_1303_ = lean_ctor_get(v___y_1100_, 2);
v_localInstances_1304_ = lean_ctor_get(v___y_1100_, 3);
v_defEqCtx_x3f_1305_ = lean_ctor_get(v___y_1100_, 4);
v_synthPendingDepth_1306_ = lean_ctor_get(v___y_1100_, 5);
v_customCanUnfoldPredicate_x3f_1307_ = lean_ctor_get(v___y_1100_, 6);
v_univApprox_1308_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1309_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 2);
v_cacheInferType_1310_ = lean_ctor_get_uint8(v___y_1100_, sizeof(void*)*7 + 3);
if (v_isShared_1254_ == 0)
{
v___x_1312_ = v___x_1253_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 0, v_foApprox_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 1, v_ctxApprox_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 2, v_quasiPatternApprox_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 3, v_constApprox_1236_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 4, v_isDefEqStuckEx_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 5, v_unificationHints_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 6, v_proofIrrelevance_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 8, v_offsetCnstrs_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 9, v_transparency_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 10, v_etaStruct_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 11, v_univApprox_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 12, v_iota_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 13, v_beta_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 14, v_proj_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 15, v_zeta_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 16, v_zetaDelta_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 17, v_zetaUnused_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 18, v_zetaHave_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1317_, 19, v_canUnfoldPredicateConfig_1251_);
v___x_1312_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
uint64_t v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_ctor_set_uint8(v___x_1312_, 7, v___x_1095_);
v___x_1313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1312_);
v___x_1314_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set_uint64(v___x_1314_, sizeof(void*)*1, v___x_1313_);
lean_inc(v_customCanUnfoldPredicate_x3f_1307_);
lean_inc(v_synthPendingDepth_1306_);
lean_inc(v_defEqCtx_x3f_1305_);
lean_inc_ref(v_localInstances_1304_);
lean_inc_ref(v_lctx_1303_);
lean_inc(v_zetaDeltaSet_1302_);
v___x_1315_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_zetaDeltaSet_1302_);
lean_ctor_set(v___x_1315_, 2, v_lctx_1303_);
lean_ctor_set(v___x_1315_, 3, v_localInstances_1304_);
lean_ctor_set(v___x_1315_, 4, v_defEqCtx_x3f_1305_);
lean_ctor_set(v___x_1315_, 5, v_synthPendingDepth_1306_);
lean_ctor_set(v___x_1315_, 6, v_customCanUnfoldPredicate_x3f_1307_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*7, v_trackZetaDelta_1301_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*7 + 1, v_univApprox_1308_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1309_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*7 + 3, v_cacheInferType_1310_);
lean_inc(v_a_1149_);
lean_inc(v_a_1106_);
v___x_1316_ = l_Lean_Meta_isExprDefEq(v_a_1106_, v_a_1149_, v___x_1315_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref_known(v___x_1315_, 7);
v___y_1170_ = v___x_1316_;
goto v___jp_1169_;
}
}
}
}
v___jp_1150_:
{
if (v_____do__lift_1151_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1160_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1);
lean_inc_ref(v_a_1089_);
v___x_1161_ = l_Lean_indentExpr(v_a_1089_);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set_tag(v___x_1146_, 1);
lean_ctor_set(v___x_1146_, 0, v___x_1164_);
v___x_1166_ = v___x_1146_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
lean_inc(v_a_1110_);
v___x_1167_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1166_, v_a_1106_, v_a_1149_, v_a_1110_, v___x_1093_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec_ref(v___x_1166_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_dec_ref_known(v___x_1167_, 1);
v___y_1112_ = v___y_1152_;
v___y_1113_ = v___y_1153_;
v___y_1114_ = v___y_1154_;
v___y_1115_ = v___y_1155_;
v___y_1116_ = v___y_1156_;
v___y_1117_ = v___y_1157_;
v___y_1118_ = v___y_1158_;
v___y_1119_ = v___y_1159_;
goto v___jp_1111_;
}
else
{
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v_a_1110_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
return v___x_1167_;
}
}
}
else
{
lean_dec(v_a_1149_);
lean_del_object(v___x_1146_);
lean_dec(v_a_1106_);
lean_dec(v___x_1093_);
v___y_1112_ = v___y_1152_;
v___y_1113_ = v___y_1153_;
v___y_1114_ = v___y_1154_;
v___y_1115_ = v___y_1155_;
v___y_1116_ = v___y_1156_;
v___y_1117_ = v___y_1157_;
v___y_1118_ = v___y_1158_;
v___y_1119_ = v___y_1159_;
goto v___jp_1111_;
}
}
v___jp_1169_:
{
if (lean_obj_tag(v___y_1170_) == 0)
{
lean_object* v_a_1171_; uint8_t v___x_1172_; 
v_a_1171_ = lean_ctor_get(v___y_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___y_1170_, 1);
v___x_1172_ = lean_unbox(v_a_1171_);
lean_dec(v_a_1171_);
v_____do__lift_1151_ = v___x_1172_;
v___y_1152_ = v___y_1096_;
v___y_1153_ = v___y_1097_;
v___y_1154_ = v___y_1098_;
v___y_1155_ = v___y_1099_;
v___y_1156_ = v___y_1100_;
v___y_1157_ = v___y_1101_;
v___y_1158_ = v___y_1102_;
v___y_1159_ = v___y_1103_;
goto v___jp_1150_;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_a_1149_);
lean_del_object(v___x_1146_);
lean_dec(v_a_1110_);
lean_dec(v_a_1106_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___x_1093_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
v_a_1173_ = lean_ctor_get(v___y_1170_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___y_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___y_1170_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___y_1170_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
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
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_del_object(v___x_1146_);
lean_dec(v_a_1110_);
lean_dec(v_a_1106_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___x_1093_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
v_a_1319_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1148_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1148_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
else
{
lean_dec(v_a_1110_);
lean_dec(v_a_1106_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___x_1093_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
return v___x_1144_;
}
v___jp_1111_:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_Meta_getMVars(v_a_1089_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1121_, v_mvarCounter_1090_, v___y_1117_);
lean_dec(v_a_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1123_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v_a_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref_known(v___x_1124_, 1);
v___x_1125_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_1086_, v___y_1113_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1125_, 1);
v___x_1126_ = l_Lean_Name_mkStr1(v___x_1091_);
v___x_1127_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1126_, v_a_1110_, v___x_1092_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v___x_1127_;
}
else
{
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_a_1110_);
lean_dec_ref(v___x_1091_);
return v___x_1125_;
}
}
else
{
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_a_1110_);
lean_dec_ref(v___x_1091_);
lean_dec(v_a_1086_);
return v___x_1124_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_a_1110_);
lean_dec_ref(v___x_1091_);
lean_dec(v_a_1086_);
v_a_1128_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1122_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1122_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_a_1110_);
lean_dec_ref(v___x_1091_);
lean_dec(v_a_1086_);
v_a_1136_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1120_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1120_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec(v_a_1106_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___x_1093_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
v_a_1329_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1109_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1109_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___x_1093_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1087_);
lean_dec(v_a_1086_);
v_a_1337_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1105_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1105_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object** _args){
lean_object* v_a_1345_ = _args[0];
lean_object* v_a_1346_ = _args[1];
lean_object* v___x_1347_ = _args[2];
lean_object* v_a_1348_ = _args[3];
lean_object* v_mvarCounter_1349_ = _args[4];
lean_object* v___x_1350_ = _args[5];
lean_object* v___x_1351_ = _args[6];
lean_object* v___x_1352_ = _args[7];
lean_object* v_useReducible_1353_ = _args[8];
lean_object* v___x_1354_ = _args[9];
lean_object* v___y_1355_ = _args[10];
lean_object* v___y_1356_ = _args[11];
lean_object* v___y_1357_ = _args[12];
lean_object* v___y_1358_ = _args[13];
lean_object* v___y_1359_ = _args[14];
lean_object* v___y_1360_ = _args[15];
lean_object* v___y_1361_ = _args[16];
lean_object* v___y_1362_ = _args[17];
lean_object* v___y_1363_ = _args[18];
_start:
{
uint8_t v___x_93922__boxed_1364_; uint8_t v___x_93925__boxed_1365_; uint8_t v_useReducible_boxed_1366_; uint8_t v___x_93927__boxed_1367_; lean_object* v_res_1368_; 
v___x_93922__boxed_1364_ = lean_unbox(v___x_1347_);
v___x_93925__boxed_1365_ = lean_unbox(v___x_1351_);
v_useReducible_boxed_1366_ = lean_unbox(v_useReducible_1353_);
v___x_93927__boxed_1367_ = lean_unbox(v___x_1354_);
v_res_1368_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1345_, v_a_1346_, v___x_93922__boxed_1364_, v_a_1348_, v_mvarCounter_1349_, v___x_1350_, v___x_93925__boxed_1365_, v___x_1352_, v_useReducible_boxed_1366_, v___x_93927__boxed_1367_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v_mvarCounter_1349_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v_infoState_1380_; lean_object* v_env_1381_; lean_object* v_nextMacroScope_1382_; lean_object* v_ngen_1383_; lean_object* v_auxDeclNGen_1384_; lean_object* v_traceState_1385_; lean_object* v_cache_1386_; lean_object* v_recordedDeps_1387_; lean_object* v_messages_1388_; lean_object* v_snapshotTasks_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1410_; 
v___x_1379_ = lean_st_ref_take(v___y_1377_);
v_infoState_1380_ = lean_ctor_get(v___x_1379_, 8);
v_env_1381_ = lean_ctor_get(v___x_1379_, 0);
v_nextMacroScope_1382_ = lean_ctor_get(v___x_1379_, 1);
v_ngen_1383_ = lean_ctor_get(v___x_1379_, 2);
v_auxDeclNGen_1384_ = lean_ctor_get(v___x_1379_, 3);
v_traceState_1385_ = lean_ctor_get(v___x_1379_, 4);
v_cache_1386_ = lean_ctor_get(v___x_1379_, 5);
v_recordedDeps_1387_ = lean_ctor_get(v___x_1379_, 6);
v_messages_1388_ = lean_ctor_get(v___x_1379_, 7);
v_snapshotTasks_1389_ = lean_ctor_get(v___x_1379_, 9);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1391_ = v___x_1379_;
v_isShared_1392_ = v_isSharedCheck_1410_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_snapshotTasks_1389_);
lean_inc(v_infoState_1380_);
lean_inc(v_messages_1388_);
lean_inc(v_recordedDeps_1387_);
lean_inc(v_cache_1386_);
lean_inc(v_traceState_1385_);
lean_inc(v_auxDeclNGen_1384_);
lean_inc(v_ngen_1383_);
lean_inc(v_nextMacroScope_1382_);
lean_inc(v_env_1381_);
lean_dec(v___x_1379_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1410_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
uint8_t v_enabled_1393_; lean_object* v_assignment_1394_; lean_object* v_lazyAssignment_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1408_; 
v_enabled_1393_ = lean_ctor_get_uint8(v_infoState_1380_, sizeof(void*)*3);
v_assignment_1394_ = lean_ctor_get(v_infoState_1380_, 0);
v_lazyAssignment_1395_ = lean_ctor_get(v_infoState_1380_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_infoState_1380_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_infoState_1380_, 2);
lean_dec(v_unused_1409_);
v___x_1397_ = v_infoState_1380_;
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_lazyAssignment_1395_);
lean_inc(v_assignment_1394_);
lean_dec(v_infoState_1380_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1408_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = lean_box(0);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 2, v_a_1369_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_assignment_1394_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_lazyAssignment_1395_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_a_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1407_, sizeof(void*)*3, v_enabled_1393_);
v___x_1401_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 8, v___x_1401_);
v___x_1403_ = v___x_1391_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_env_1381_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_nextMacroScope_1382_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_ngen_1383_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_auxDeclNGen_1384_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v_traceState_1385_);
lean_ctor_set(v_reuseFailAlloc_1406_, 5, v_cache_1386_);
lean_ctor_set(v_reuseFailAlloc_1406_, 6, v_recordedDeps_1387_);
lean_ctor_set(v_reuseFailAlloc_1406_, 7, v_messages_1388_);
lean_ctor_set(v_reuseFailAlloc_1406_, 8, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1406_, 9, v_snapshotTasks_1389_);
v___x_1403_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_st_ref_put(v___y_1377_, v___x_1403_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1399_);
return v___x_1405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1422_, lean_object* v_mkInfoTree_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v_a_1431_, lean_object* v_a_x3f_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_infoState_1435_; lean_object* v_trees_1436_; lean_object* v___x_1437_; 
v___x_1434_ = lean_st_ref_get(v___y_1422_);
v_infoState_1435_ = lean_ctor_get(v___x_1434_, 8);
lean_inc_ref(v_infoState_1435_);
lean_dec(v___x_1434_);
v_trees_1436_ = lean_ctor_get(v_infoState_1435_, 2);
lean_inc_ref(v_trees_1436_);
lean_dec_ref(v_infoState_1435_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
v___x_1437_ = lean_apply_10(v_mkInfoTree_1423_, v_trees_1436_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1422_, lean_box(0));
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1477_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1477_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1477_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v_infoState_1443_; lean_object* v_env_1444_; lean_object* v_nextMacroScope_1445_; lean_object* v_ngen_1446_; lean_object* v_auxDeclNGen_1447_; lean_object* v_traceState_1448_; lean_object* v_cache_1449_; lean_object* v_recordedDeps_1450_; lean_object* v_messages_1451_; lean_object* v_snapshotTasks_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1476_; 
v___x_1442_ = lean_st_ref_take(v___y_1422_);
v_infoState_1443_ = lean_ctor_get(v___x_1442_, 8);
v_env_1444_ = lean_ctor_get(v___x_1442_, 0);
v_nextMacroScope_1445_ = lean_ctor_get(v___x_1442_, 1);
v_ngen_1446_ = lean_ctor_get(v___x_1442_, 2);
v_auxDeclNGen_1447_ = lean_ctor_get(v___x_1442_, 3);
v_traceState_1448_ = lean_ctor_get(v___x_1442_, 4);
v_cache_1449_ = lean_ctor_get(v___x_1442_, 5);
v_recordedDeps_1450_ = lean_ctor_get(v___x_1442_, 6);
v_messages_1451_ = lean_ctor_get(v___x_1442_, 7);
v_snapshotTasks_1452_ = lean_ctor_get(v___x_1442_, 9);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1454_ = v___x_1442_;
v_isShared_1455_ = v_isSharedCheck_1476_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_snapshotTasks_1452_);
lean_inc(v_infoState_1443_);
lean_inc(v_messages_1451_);
lean_inc(v_recordedDeps_1450_);
lean_inc(v_cache_1449_);
lean_inc(v_traceState_1448_);
lean_inc(v_auxDeclNGen_1447_);
lean_inc(v_ngen_1446_);
lean_inc(v_nextMacroScope_1445_);
lean_inc(v_env_1444_);
lean_dec(v___x_1442_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1476_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
uint8_t v_enabled_1456_; lean_object* v_assignment_1457_; lean_object* v_lazyAssignment_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1474_; 
v_enabled_1456_ = lean_ctor_get_uint8(v_infoState_1443_, sizeof(void*)*3);
v_assignment_1457_ = lean_ctor_get(v_infoState_1443_, 0);
v_lazyAssignment_1458_ = lean_ctor_get(v_infoState_1443_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_infoState_1443_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_infoState_1443_, 2);
lean_dec(v_unused_1475_);
v___x_1460_ = v_infoState_1443_;
v_isShared_1461_ = v_isSharedCheck_1474_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_lazyAssignment_1458_);
lean_inc(v_assignment_1457_);
lean_dec(v_infoState_1443_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1474_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1462_ = lean_box(0);
v___x_1463_ = l_Lean_PersistentArray_push___redArg(v_a_1431_, v_a_1438_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 2, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_assignment_1457_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_lazyAssignment_1458_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v___x_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*3, v_enabled_1456_);
v___x_1465_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1467_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 8, v___x_1465_);
v___x_1467_ = v___x_1454_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_env_1444_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_nextMacroScope_1445_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_ngen_1446_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_auxDeclNGen_1447_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_traceState_1448_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v_cache_1449_);
lean_ctor_set(v_reuseFailAlloc_1472_, 6, v_recordedDeps_1450_);
lean_ctor_set(v_reuseFailAlloc_1472_, 7, v_messages_1451_);
lean_ctor_set(v_reuseFailAlloc_1472_, 8, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1472_, 9, v_snapshotTasks_1452_);
v___x_1467_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_st_ref_put(v___y_1422_, v___x_1467_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1462_);
v___x_1470_ = v___x_1440_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1462_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_a_1431_);
v_a_1478_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1437_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1437_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1486_, lean_object* v_mkInfoTree_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v_a_1495_, lean_object* v_a_x3f_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1486_, v_mkInfoTree_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v_a_1495_, v_a_x3f_1496_);
lean_dec(v_a_x3f_1496_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1486_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1499_, lean_object* v_mkInfoTree_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_infoState_1511_; uint8_t v_enabled_1512_; 
v___x_1510_ = lean_st_ref_get(v___y_1508_);
v_infoState_1511_ = lean_ctor_get(v___x_1510_, 8);
lean_inc_ref(v_infoState_1511_);
lean_dec(v___x_1510_);
v_enabled_1512_ = lean_ctor_get_uint8(v_infoState_1511_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1511_);
if (v_enabled_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v_mkInfoTree_1500_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
v___x_1513_ = lean_apply_9(v_x_1499_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, lean_box(0));
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v_a_1515_; lean_object* v_r_1516_; 
v___x_1514_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1508_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref(v___x_1514_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
v_r_1516_ = lean_apply_9(v_x_1499_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, lean_box(0));
if (lean_obj_tag(v_r_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1541_; 
v_a_1517_ = lean_ctor_get(v_r_1516_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_r_1516_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1519_ = v_r_1516_;
v_isShared_1520_ = v_isSharedCheck_1541_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v_r_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1541_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
lean_inc(v_a_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1508_, v_mkInfoTree_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v_a_1515_, v___x_1522_);
lean_dec_ref(v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v___x_1523_, 0);
lean_dec(v_unused_1531_);
v___x_1525_ = v___x_1523_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v___x_1523_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v_a_1517_);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1517_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_a_1517_);
v_a_1532_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1523_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1523_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_a_1542_ = lean_ctor_get(v_r_1516_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v_r_1516_, 1);
v___x_1543_ = lean_box(0);
v___x_1544_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1508_, v_mkInfoTree_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v_a_1515_, v___x_1543_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v___x_1544_, 0);
lean_dec(v_unused_1552_);
v___x_1546_ = v___x_1544_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_dec(v___x_1544_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
lean_ctor_set(v___x_1546_, 0, v_a_1542_);
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1542_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1542_);
v_a_1553_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1544_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1544_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1561_, lean_object* v_mkInfoTree_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1561_, v_mkInfoTree_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_ref_1579_; lean_object* v___x_1580_; lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1589_; 
v_ref_1579_ = lean_ctor_get(v___y_1576_, 2);
v___x_1580_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
lean_inc(v_ref_1579_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_ref_1579_);
lean_ctor_set(v___x_1585_, 1, v_a_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 1);
lean_ctor_set(v___x_1583_, 0, v___x_1585_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
return v_res_1596_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(lean_object* v_a_1597_, lean_object* v_x_1598_){
_start:
{
if (lean_obj_tag(v_x_1598_) == 0)
{
uint8_t v___x_1599_; 
v___x_1599_ = 0;
return v___x_1599_;
}
else
{
lean_object* v_key_1600_; lean_object* v_tail_1601_; uint8_t v___x_1602_; 
v_key_1600_ = lean_ctor_get(v_x_1598_, 0);
v_tail_1601_ = lean_ctor_get(v_x_1598_, 2);
v___x_1602_ = lean_expr_eqv(v_key_1600_, v_a_1597_);
if (v___x_1602_ == 0)
{
v_x_1598_ = v_tail_1601_;
goto _start;
}
else
{
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg___boxed(lean_object* v_a_1604_, lean_object* v_x_1605_){
_start:
{
uint8_t v_res_1606_; lean_object* v_r_1607_; 
v_res_1606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1604_, v_x_1605_);
lean_dec(v_x_1605_);
lean_dec_ref(v_a_1604_);
v_r_1607_ = lean_box(v_res_1606_);
return v_r_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
if (lean_obj_tag(v_x_1609_) == 0)
{
return v_x_1608_;
}
else
{
lean_object* v_key_1610_; lean_object* v_value_1611_; lean_object* v_tail_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1635_; 
v_key_1610_ = lean_ctor_get(v_x_1609_, 0);
v_value_1611_ = lean_ctor_get(v_x_1609_, 1);
v_tail_1612_ = lean_ctor_get(v_x_1609_, 2);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_x_1609_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1614_ = v_x_1609_;
v_isShared_1615_ = v_isSharedCheck_1635_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_tail_1612_);
lean_inc(v_value_1611_);
lean_inc(v_key_1610_);
lean_dec(v_x_1609_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1635_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; uint64_t v___x_1617_; uint64_t v___x_1618_; uint64_t v___x_1619_; uint64_t v_fold_1620_; uint64_t v___x_1621_; uint64_t v___x_1622_; uint64_t v___x_1623_; size_t v___x_1624_; size_t v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1616_ = lean_array_get_size(v_x_1608_);
v___x_1617_ = l_Lean_Expr_hash(v_key_1610_);
v___x_1618_ = 32ULL;
v___x_1619_ = lean_uint64_shift_right(v___x_1617_, v___x_1618_);
v_fold_1620_ = lean_uint64_xor(v___x_1617_, v___x_1619_);
v___x_1621_ = 16ULL;
v___x_1622_ = lean_uint64_shift_right(v_fold_1620_, v___x_1621_);
v___x_1623_ = lean_uint64_xor(v_fold_1620_, v___x_1622_);
v___x_1624_ = lean_uint64_to_usize(v___x_1623_);
v___x_1625_ = lean_usize_of_nat(v___x_1616_);
v___x_1626_ = ((size_t)1ULL);
v___x_1627_ = lean_usize_sub(v___x_1625_, v___x_1626_);
v___x_1628_ = lean_usize_land(v___x_1624_, v___x_1627_);
v___x_1629_ = lean_array_uget_borrowed(v_x_1608_, v___x_1628_);
lean_inc(v___x_1629_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 2, v___x_1629_);
v___x_1631_ = v___x_1614_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_key_1610_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_value_1611_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_array_uset(v_x_1608_, v___x_1628_, v___x_1631_);
v_x_1608_ = v___x_1632_;
v_x_1609_ = v_tail_1612_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(lean_object* v_i_1636_, lean_object* v_source_1637_, lean_object* v_target_1638_){
_start:
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = lean_array_get_size(v_source_1637_);
v___x_1640_ = lean_nat_dec_lt(v_i_1636_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_dec_ref(v_source_1637_);
lean_dec(v_i_1636_);
return v_target_1638_;
}
else
{
lean_object* v_es_1641_; lean_object* v___x_1642_; lean_object* v_source_1643_; lean_object* v_target_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_es_1641_ = lean_array_fget(v_source_1637_, v_i_1636_);
v___x_1642_ = lean_box(0);
v_source_1643_ = lean_array_fset(v_source_1637_, v_i_1636_, v___x_1642_);
v_target_1644_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_target_1638_, v_es_1641_);
v___x_1645_ = lean_unsigned_to_nat(1u);
v___x_1646_ = lean_nat_add(v_i_1636_, v___x_1645_);
lean_dec(v_i_1636_);
v_i_1636_ = v___x_1646_;
v_source_1637_ = v_source_1643_;
v_target_1638_ = v_target_1644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(lean_object* v_data_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_nbuckets_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1649_ = lean_array_get_size(v_data_1648_);
v___x_1650_ = lean_unsigned_to_nat(2u);
v_nbuckets_1651_ = lean_nat_mul(v___x_1649_, v___x_1650_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_mk_array(v_nbuckets_1651_, v___x_1653_);
v___x_1655_ = lean_array_propagate_mark(v_data_1648_, v___x_1654_);
v___x_1656_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v___x_1652_, v_data_1648_, v___x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(lean_object* v_m_1657_, lean_object* v_a_1658_, lean_object* v_b_1659_){
_start:
{
lean_object* v_size_1660_; lean_object* v_buckets_1661_; lean_object* v___x_1662_; uint64_t v___x_1663_; uint64_t v___x_1664_; uint64_t v___x_1665_; uint64_t v_fold_1666_; uint64_t v___x_1667_; uint64_t v___x_1668_; uint64_t v___x_1669_; size_t v___x_1670_; size_t v___x_1671_; size_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; lean_object* v_bkt_1675_; uint8_t v___x_1676_; 
v_size_1660_ = lean_ctor_get(v_m_1657_, 0);
v_buckets_1661_ = lean_ctor_get(v_m_1657_, 1);
v___x_1662_ = lean_array_get_size(v_buckets_1661_);
v___x_1663_ = l_Lean_Expr_hash(v_a_1658_);
v___x_1664_ = 32ULL;
v___x_1665_ = lean_uint64_shift_right(v___x_1663_, v___x_1664_);
v_fold_1666_ = lean_uint64_xor(v___x_1663_, v___x_1665_);
v___x_1667_ = 16ULL;
v___x_1668_ = lean_uint64_shift_right(v_fold_1666_, v___x_1667_);
v___x_1669_ = lean_uint64_xor(v_fold_1666_, v___x_1668_);
v___x_1670_ = lean_uint64_to_usize(v___x_1669_);
v___x_1671_ = lean_usize_of_nat(v___x_1662_);
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_sub(v___x_1671_, v___x_1672_);
v___x_1674_ = lean_usize_land(v___x_1670_, v___x_1673_);
v_bkt_1675_ = lean_array_uget_borrowed(v_buckets_1661_, v___x_1674_);
v___x_1676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1658_, v_bkt_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1697_; 
lean_inc_ref(v_buckets_1661_);
lean_inc(v_size_1660_);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_m_1657_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; lean_object* v_unused_1699_; 
v_unused_1698_ = lean_ctor_get(v_m_1657_, 1);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_m_1657_, 0);
lean_dec(v_unused_1699_);
v___x_1678_ = v_m_1657_;
v_isShared_1679_ = v_isSharedCheck_1697_;
goto v_resetjp_1677_;
}
else
{
lean_dec(v_m_1657_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1697_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v_size_x27_1681_; lean_object* v___x_1682_; lean_object* v_buckets_x27_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
v_size_x27_1681_ = lean_nat_add(v_size_1660_, v___x_1680_);
lean_dec(v_size_1660_);
lean_inc(v_bkt_1675_);
v___x_1682_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1682_, 0, v_a_1658_);
lean_ctor_set(v___x_1682_, 1, v_b_1659_);
lean_ctor_set(v___x_1682_, 2, v_bkt_1675_);
v_buckets_x27_1683_ = lean_array_uset(v_buckets_1661_, v___x_1674_, v___x_1682_);
v___x_1684_ = lean_unsigned_to_nat(4u);
v___x_1685_ = lean_nat_mul(v_size_x27_1681_, v___x_1684_);
v___x_1686_ = lean_unsigned_to_nat(3u);
v___x_1687_ = lean_nat_div(v___x_1685_, v___x_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_array_get_size(v_buckets_x27_1683_);
v___x_1689_ = lean_nat_dec_le(v___x_1687_, v___x_1688_);
lean_dec(v___x_1687_);
if (v___x_1689_ == 0)
{
lean_object* v_val_1690_; lean_object* v___x_1692_; 
v_val_1690_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_buckets_x27_1683_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v_val_1690_);
lean_ctor_set(v___x_1678_, 0, v_size_x27_1681_);
v___x_1692_ = v___x_1678_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_size_x27_1681_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_val_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v___x_1695_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v_buckets_x27_1683_);
lean_ctor_set(v___x_1678_, 0, v_size_x27_1681_);
v___x_1695_ = v___x_1678_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_size_x27_1681_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_buckets_x27_1683_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_dec(v_b_1659_);
lean_dec_ref(v_a_1658_);
return v_m_1657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(lean_object* v_mvarId_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; lean_object* v_mctx_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1704_ = lean_st_ref_get(v___y_1702_);
v_mctx_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc_ref(v_mctx_1705_);
lean_dec(v___x_1704_);
v___x_1706_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1705_, v_mvarId_1700_);
lean_dec_ref(v_mctx_1705_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___y_1701_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg___boxed(lean_object* v_mvarId_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec(v_mvarId_1710_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(lean_object* v_mvarId_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v_mctx_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1719_ = lean_st_ref_get(v___y_1717_);
v_mctx_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc_ref(v_mctx_1720_);
lean_dec(v___x_1719_);
v___x_1721_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1720_, v_mvarId_1715_);
lean_dec_ref(v_mctx_1720_);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___y_1716_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg___boxed(lean_object* v_mvarId_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec(v_mvarId_1725_);
return v_res_1729_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(lean_object* v_m_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_buckets_1732_; lean_object* v___x_1733_; uint64_t v___x_1734_; uint64_t v___x_1735_; uint64_t v___x_1736_; uint64_t v_fold_1737_; uint64_t v___x_1738_; uint64_t v___x_1739_; uint64_t v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_buckets_1732_ = lean_ctor_get(v_m_1730_, 1);
v___x_1733_ = lean_array_get_size(v_buckets_1732_);
v___x_1734_ = l_Lean_Expr_hash(v_a_1731_);
v___x_1735_ = 32ULL;
v___x_1736_ = lean_uint64_shift_right(v___x_1734_, v___x_1735_);
v_fold_1737_ = lean_uint64_xor(v___x_1734_, v___x_1736_);
v___x_1738_ = 16ULL;
v___x_1739_ = lean_uint64_shift_right(v_fold_1737_, v___x_1738_);
v___x_1740_ = lean_uint64_xor(v_fold_1737_, v___x_1739_);
v___x_1741_ = lean_uint64_to_usize(v___x_1740_);
v___x_1742_ = lean_usize_of_nat(v___x_1733_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_sub(v___x_1742_, v___x_1743_);
v___x_1745_ = lean_usize_land(v___x_1741_, v___x_1744_);
v___x_1746_ = lean_array_uget_borrowed(v_buckets_1732_, v___x_1745_);
v___x_1747_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_1731_, v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_m_1748_, lean_object* v_a_1749_){
_start:
{
uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_res_1750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_1748_, v_a_1749_);
lean_dec_ref(v_a_1749_);
lean_dec_ref(v_m_1748_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(lean_object* v_mvarId_1756_, lean_object* v_e_1757_, lean_object* v_a_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_d_1769_; lean_object* v_b_1770_; lean_object* v___y_1771_; uint8_t v___x_1777_; 
v___x_1777_ = l_Lean_Expr_hasExprMVar(v_e_1757_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_dec_ref(v_e_1757_);
v___x_1778_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_a_1758_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
else
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_a_1758_, v_e_1757_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_box(0);
lean_inc_ref(v_e_1757_);
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_a_1758_, v_e_1757_, v___x_1782_);
switch(lean_obj_tag(v_e_1757_))
{
case 11:
{
lean_object* v_struct_1784_; 
v_struct_1784_ = lean_ctor_get(v_e_1757_, 2);
lean_inc_ref(v_struct_1784_);
lean_dec_ref_known(v_e_1757_, 3);
v_e_1757_ = v_struct_1784_;
v_a_1758_ = v___x_1783_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1786_; lean_object* v_body_1787_; 
v_binderType_1786_ = lean_ctor_get(v_e_1757_, 1);
lean_inc_ref(v_binderType_1786_);
v_body_1787_ = lean_ctor_get(v_e_1757_, 2);
lean_inc_ref(v_body_1787_);
lean_dec_ref_known(v_e_1757_, 3);
v_d_1769_ = v_binderType_1786_;
v_b_1770_ = v_body_1787_;
v___y_1771_ = v___x_1783_;
goto v___jp_1768_;
}
case 6:
{
lean_object* v_binderType_1788_; lean_object* v_body_1789_; 
v_binderType_1788_ = lean_ctor_get(v_e_1757_, 1);
lean_inc_ref(v_binderType_1788_);
v_body_1789_ = lean_ctor_get(v_e_1757_, 2);
lean_inc_ref(v_body_1789_);
lean_dec_ref_known(v_e_1757_, 3);
v_d_1769_ = v_binderType_1788_;
v_b_1770_ = v_body_1789_;
v___y_1771_ = v___x_1783_;
goto v___jp_1768_;
}
case 8:
{
lean_object* v_type_1790_; lean_object* v_value_1791_; lean_object* v_body_1792_; lean_object* v___x_1793_; 
v_type_1790_ = lean_ctor_get(v_e_1757_, 1);
lean_inc_ref(v_type_1790_);
v_value_1791_ = lean_ctor_get(v_e_1757_, 2);
lean_inc_ref(v_value_1791_);
v_body_1792_ = lean_ctor_get(v_e_1757_, 3);
lean_inc_ref(v_body_1792_);
lean_dec_ref_known(v_e_1757_, 4);
v___x_1793_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1756_, v_type_1790_, v___x_1783_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v_fst_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
v_fst_1795_ = lean_ctor_get(v_a_1794_, 0);
if (lean_obj_tag(v_fst_1795_) == 0)
{
lean_dec(v_a_1794_);
lean_dec_ref(v_body_1792_);
lean_dec_ref(v_value_1791_);
return v___x_1793_;
}
else
{
lean_object* v_snd_1796_; lean_object* v___x_1797_; 
lean_dec_ref_known(v___x_1793_, 1);
v_snd_1796_ = lean_ctor_get(v_a_1794_, 1);
lean_inc(v_snd_1796_);
lean_dec(v_a_1794_);
v___x_1797_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1756_, v_value_1791_, v_snd_1796_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v_fst_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
v_fst_1799_ = lean_ctor_get(v_a_1798_, 0);
if (lean_obj_tag(v_fst_1799_) == 0)
{
lean_dec(v_a_1798_);
lean_dec_ref(v_body_1792_);
return v___x_1797_;
}
else
{
lean_object* v_snd_1800_; 
lean_dec_ref_known(v___x_1797_, 1);
v_snd_1800_ = lean_ctor_get(v_a_1798_, 1);
lean_inc(v_snd_1800_);
lean_dec(v_a_1798_);
v_e_1757_ = v_body_1792_;
v_a_1758_ = v_snd_1800_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1792_);
return v___x_1797_;
}
}
}
else
{
lean_dec_ref(v_body_1792_);
lean_dec_ref(v_value_1791_);
return v___x_1793_;
}
}
case 10:
{
lean_object* v_expr_1802_; 
v_expr_1802_ = lean_ctor_get(v_e_1757_, 1);
lean_inc_ref(v_expr_1802_);
lean_dec_ref_known(v_e_1757_, 2);
v_e_1757_ = v_expr_1802_;
v_a_1758_ = v___x_1783_;
goto _start;
}
case 5:
{
lean_object* v_fn_1804_; lean_object* v_arg_1805_; lean_object* v___x_1806_; 
v_fn_1804_ = lean_ctor_get(v_e_1757_, 0);
lean_inc_ref(v_fn_1804_);
v_arg_1805_ = lean_ctor_get(v_e_1757_, 1);
lean_inc_ref(v_arg_1805_);
lean_dec_ref_known(v_e_1757_, 2);
v___x_1806_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1756_, v_fn_1804_, v___x_1783_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v_fst_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
v_fst_1808_ = lean_ctor_get(v_a_1807_, 0);
if (lean_obj_tag(v_fst_1808_) == 0)
{
lean_dec(v_a_1807_);
lean_dec_ref(v_arg_1805_);
return v___x_1806_;
}
else
{
lean_object* v_snd_1809_; 
lean_dec_ref_known(v___x_1806_, 1);
v_snd_1809_ = lean_ctor_get(v_a_1807_, 1);
lean_inc(v_snd_1809_);
lean_dec(v_a_1807_);
v_e_1757_ = v_arg_1805_;
v_a_1758_ = v_snd_1809_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1805_);
return v___x_1806_;
}
}
case 2:
{
lean_object* v_mvarId_1811_; lean_object* v___x_1812_; 
v_mvarId_1811_ = lean_ctor_get(v_e_1757_, 0);
lean_inc(v_mvarId_1811_);
lean_dec_ref_known(v_e_1757_, 1);
v___x_1812_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1756_, v_mvarId_1811_, v___x_1783_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1812_;
}
default: 
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec_ref(v_e_1757_);
v___x_1813_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v___x_1783_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec_ref(v_e_1757_);
v___x_1816_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v_a_1758_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
v___jp_1768_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1756_, v_d_1769_, v___y_1771_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v_fst_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
v_fst_1774_ = lean_ctor_get(v_a_1773_, 0);
if (lean_obj_tag(v_fst_1774_) == 0)
{
lean_dec(v_a_1773_);
lean_dec_ref(v_b_1770_);
return v___x_1772_;
}
else
{
lean_object* v_snd_1775_; 
lean_dec_ref_known(v___x_1772_, 1);
v_snd_1775_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_snd_1775_);
lean_dec(v_a_1773_);
v_e_1757_ = v_b_1770_;
v_a_1758_ = v_snd_1775_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1770_);
return v___x_1772_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(lean_object* v_mvarId_1819_, lean_object* v_mvarId_x27_1820_, lean_object* v_a_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_Lean_instBEqMVarId_beq(v_mvarId_1819_, v_mvarId_x27_1820_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_x27_1820_, v_a_1821_, v___y_1827_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1916_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1916_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1916_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_fst_1837_; 
v_fst_1837_ = lean_ctor_get(v_a_1833_, 0);
lean_inc(v_fst_1837_);
if (lean_obj_tag(v_fst_1837_) == 0)
{
lean_object* v_snd_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_mvarId_x27_1820_);
v_snd_1838_ = lean_ctor_get(v_a_1833_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_a_1833_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v_a_1833_, 0);
lean_dec(v_unused_1857_);
v___x_1840_ = v_a_1833_;
v_isShared_1841_ = v_isSharedCheck_1856_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_snd_1838_);
lean_dec(v_a_1833_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1856_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1855_; 
v_a_1842_ = lean_ctor_get(v_fst_1837_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_fst_1837_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1844_ = v_fst_1837_;
v_isShared_1845_ = v_isSharedCheck_1855_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v_fst_1837_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1855_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1847_);
v___x_1849_ = v___x_1840_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_snd_1838_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1849_);
v___x_1851_ = v___x_1835_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
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
}
}
else
{
lean_object* v_a_1858_; 
lean_del_object(v___x_1835_);
v_a_1858_ = lean_ctor_get(v_fst_1837_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v_fst_1837_, 1);
if (lean_obj_tag(v_a_1858_) == 0)
{
lean_object* v_snd_1859_; lean_object* v___x_1860_; 
v_snd_1859_ = lean_ctor_get(v_a_1833_, 1);
lean_inc(v_snd_1859_);
lean_dec(v_a_1833_);
v___x_1860_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_x27_1820_, v_snd_1859_, v___y_1827_);
lean_dec(v_mvarId_x27_1820_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1904_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1904_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1904_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_fst_1865_; 
v_fst_1865_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_fst_1865_);
if (lean_obj_tag(v_fst_1865_) == 0)
{
lean_object* v_snd_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1884_; 
v_snd_1866_ = lean_ctor_get(v_a_1861_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_a_1861_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v_a_1861_, 0);
lean_dec(v_unused_1885_);
v___x_1868_ = v_a_1861_;
v_isShared_1869_ = v_isSharedCheck_1884_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snd_1866_);
lean_dec(v_a_1861_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1884_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1883_; 
v_a_1870_ = lean_ctor_get(v_fst_1865_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_fst_1865_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1872_ = v_fst_1865_;
v_isShared_1873_ = v_isSharedCheck_1883_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v_fst_1865_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1883_;
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
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1875_);
v___x_1877_ = v___x_1868_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_snd_1866_);
v___x_1877_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1879_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1877_);
v___x_1879_ = v___x_1863_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
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
}
}
else
{
lean_object* v_a_1886_; 
v_a_1886_ = lean_ctor_get(v_fst_1865_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v_fst_1865_, 1);
if (lean_obj_tag(v_a_1886_) == 0)
{
lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1898_; 
v_snd_1887_ = lean_ctor_get(v_a_1861_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_a_1861_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v_a_1861_, 0);
lean_dec(v_unused_1899_);
v___x_1889_ = v_a_1861_;
v_isShared_1890_ = v_isSharedCheck_1898_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1887_);
lean_dec(v_a_1861_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1898_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__0));
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_snd_1887_);
v___x_1893_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1895_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1893_);
v___x_1895_ = v___x_1863_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_val_1900_; lean_object* v_snd_1901_; lean_object* v_mvarIdPending_1902_; 
lean_del_object(v___x_1863_);
v_val_1900_ = lean_ctor_get(v_a_1886_, 0);
lean_inc(v_val_1900_);
lean_dec_ref_known(v_a_1886_, 1);
v_snd_1901_ = lean_ctor_get(v_a_1861_, 1);
lean_inc(v_snd_1901_);
lean_dec(v_a_1861_);
v_mvarIdPending_1902_ = lean_ctor_get(v_val_1900_, 1);
lean_inc(v_mvarIdPending_1902_);
lean_dec(v_val_1900_);
v_mvarId_x27_1820_ = v_mvarIdPending_1902_;
v_a_1821_ = v_snd_1901_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_a_1905_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1860_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1860_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_snd_1913_; lean_object* v_val_1914_; lean_object* v___x_1915_; 
lean_dec(v_mvarId_x27_1820_);
v_snd_1913_ = lean_ctor_get(v_a_1833_, 1);
lean_inc(v_snd_1913_);
lean_dec(v_a_1833_);
v_val_1914_ = lean_ctor_get(v_a_1858_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v_a_1858_, 1);
v___x_1915_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1819_, v_val_1914_, v_snd_1913_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_mvarId_x27_1820_);
v_a_1917_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1832_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1832_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec(v_mvarId_x27_1820_);
v___x_1925_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___closed__1));
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v_a_1821_);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12___boxed(lean_object* v_mvarId_1928_, lean_object* v_mvarId_x27_1929_, lean_object* v_a_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12(v_mvarId_1928_, v_mvarId_x27_1929_, v_a_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v_mvarId_1928_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6___boxed(lean_object* v_mvarId_1941_, lean_object* v_e_1942_, lean_object* v_a_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1941_, v_e_1942_, v_a_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v_mvarId_1941_);
return v_res_1953_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_unsigned_to_nat(16u);
v___x_1956_ = lean_mk_array(v___x_1955_, v___x_1954_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0);
v___x_1958_ = lean_unsigned_to_nat(0u);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v___x_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_mvarId_1960_, lean_object* v_e_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Expr_hasExprMVar(v_e_1961_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref(v_e_1961_);
v___x_1972_ = 1;
v___x_1973_ = lean_box(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
else
{
uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = 0;
v___x_1976_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
v___x_1977_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6(v_mvarId_1960_, v_e_1961_, v___x_1976_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1991_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1991_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1991_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_fst_1982_; 
v_fst_1982_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_fst_1982_);
lean_dec(v_a_1978_);
if (lean_obj_tag(v_fst_1982_) == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec_ref_known(v_fst_1982_, 1);
v___x_1983_ = lean_box(v___x_1975_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1983_);
v___x_1985_ = v___x_1980_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
lean_dec_ref_known(v_fst_1982_, 1);
v___x_1987_ = lean_box(v___x_1971_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1987_);
v___x_1989_ = v___x_1980_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1977_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1977_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_mvarId_2000_, lean_object* v_e_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_mvarId_2000_, v_e_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_mvarId_2000_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_){
_start:
{
lean_object* v_ks_2016_; lean_object* v_vs_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2041_; 
v_ks_2016_ = lean_ctor_get(v_x_2012_, 0);
v_vs_2017_ = lean_ctor_get(v_x_2012_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_x_2012_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2019_ = v_x_2012_;
v_isShared_2020_ = v_isSharedCheck_2041_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_vs_2017_);
lean_inc(v_ks_2016_);
lean_dec(v_x_2012_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2041_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_array_get_size(v_ks_2016_);
v___x_2022_ = lean_nat_dec_lt(v_x_2013_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec(v_x_2013_);
v___x_2023_ = lean_array_push(v_ks_2016_, v_x_2014_);
v___x_2024_ = lean_array_push(v_vs_2017_, v_x_2015_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v___x_2024_);
lean_ctor_set(v___x_2019_, 0, v___x_2023_);
v___x_2026_ = v___x_2019_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
else
{
lean_object* v_k_x27_2028_; uint8_t v___x_2029_; 
v_k_x27_2028_ = lean_array_fget_borrowed(v_ks_2016_, v_x_2013_);
v___x_2029_ = l_Lean_instBEqMVarId_beq(v_x_2014_, v_k_x27_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2031_; 
if (v_isShared_2020_ == 0)
{
v___x_2031_ = v___x_2019_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_ks_2016_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_vs_2017_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_x_2013_, v___x_2032_);
lean_dec(v_x_2013_);
v_x_2012_ = v___x_2031_;
v_x_2013_ = v___x_2033_;
goto _start;
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2036_ = lean_array_fset(v_ks_2016_, v_x_2013_, v_x_2014_);
v___x_2037_ = lean_array_fset(v_vs_2017_, v_x_2013_, v_x_2015_);
lean_dec(v_x_2013_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v___x_2037_);
lean_ctor_set(v___x_2019_, 0, v___x_2036_);
v___x_2039_ = v___x_2019_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_n_2042_, lean_object* v_k_2043_, lean_object* v_v_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_n_2042_, v___x_2045_, v_k_2043_, v_v_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_x_2048_, size_t v_x_2049_, size_t v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
if (lean_obj_tag(v_x_2048_) == 0)
{
lean_object* v_es_2053_; size_t v___x_2054_; size_t v___x_2055_; lean_object* v_j_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_es_2053_ = lean_ctor_get(v_x_2048_, 0);
v___x_2054_ = ((size_t)31ULL);
v___x_2055_ = lean_usize_land(v_x_2049_, v___x_2054_);
v_j_2056_ = lean_usize_to_nat(v___x_2055_);
v___x_2057_ = lean_array_get_size(v_es_2053_);
v___x_2058_ = lean_nat_dec_lt(v_j_2056_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec(v_j_2056_);
lean_dec(v_x_2052_);
lean_dec(v_x_2051_);
return v_x_2048_;
}
else
{
lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2097_; 
lean_inc_ref(v_es_2053_);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_x_2048_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v_x_2048_, 0);
lean_dec(v_unused_2098_);
v___x_2060_ = v_x_2048_;
v_isShared_2061_ = v_isSharedCheck_2097_;
goto v_resetjp_2059_;
}
else
{
lean_dec(v_x_2048_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2097_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_v_2062_; lean_object* v___x_2063_; lean_object* v_xs_x27_2064_; lean_object* v___y_2066_; 
v_v_2062_ = lean_array_fget(v_es_2053_, v_j_2056_);
v___x_2063_ = lean_box(0);
v_xs_x27_2064_ = lean_array_fset(v_es_2053_, v_j_2056_, v___x_2063_);
switch(lean_obj_tag(v_v_2062_))
{
case 0:
{
lean_object* v_key_2071_; lean_object* v_val_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2082_; 
v_key_2071_ = lean_ctor_get(v_v_2062_, 0);
v_val_2072_ = lean_ctor_get(v_v_2062_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_v_2062_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2074_ = v_v_2062_;
v_isShared_2075_ = v_isSharedCheck_2082_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_val_2072_);
lean_inc(v_key_2071_);
lean_dec(v_v_2062_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2082_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Lean_instBEqMVarId_beq(v_x_2051_, v_key_2071_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_del_object(v___x_2074_);
v___x_2077_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2071_, v_val_2072_, v_x_2051_, v_x_2052_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
v___y_2066_ = v___x_2078_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2080_; 
lean_dec(v_val_2072_);
lean_dec(v_key_2071_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v_x_2052_);
lean_ctor_set(v___x_2074_, 0, v_x_2051_);
v___x_2080_ = v___x_2074_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_x_2051_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_x_2052_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
v___y_2066_ = v___x_2080_;
goto v___jp_2065_;
}
}
}
}
case 1:
{
lean_object* v_node_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2095_; 
v_node_2083_ = lean_ctor_get(v_v_2062_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_v_2062_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2085_ = v_v_2062_;
v_isShared_2086_ = v_isSharedCheck_2095_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_node_2083_);
lean_dec(v_v_2062_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2095_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
size_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2087_ = ((size_t)5ULL);
v___x_2088_ = lean_usize_shift_right(v_x_2049_, v___x_2087_);
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_x_2050_, v___x_2089_);
v___x_2091_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_node_2083_, v___x_2088_, v___x_2090_, v_x_2051_, v_x_2052_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2091_);
v___x_2093_ = v___x_2085_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
v___y_2066_ = v___x_2093_;
goto v___jp_2065_;
}
}
}
default: 
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v_x_2051_);
lean_ctor_set(v___x_2096_, 1, v_x_2052_);
v___y_2066_ = v___x_2096_;
goto v___jp_2065_;
}
}
v___jp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_array_fset(v_xs_x27_2064_, v_j_2056_, v___y_2066_);
lean_dec(v_j_2056_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2067_);
v___x_2069_ = v___x_2060_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
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
}
else
{
lean_object* v_ks_2099_; lean_object* v_vs_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2118_; 
v_ks_2099_ = lean_ctor_get(v_x_2048_, 0);
v_vs_2100_ = lean_ctor_get(v_x_2048_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_x_2048_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2102_ = v_x_2048_;
v_isShared_2103_ = v_isSharedCheck_2118_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_vs_2100_);
lean_inc(v_ks_2099_);
lean_dec(v_x_2048_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2118_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_ks_2099_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_vs_2100_);
v___x_2105_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v_newNode_2106_; size_t v___x_2107_; uint8_t v___x_2108_; 
v_newNode_2106_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v___x_2105_, v_x_2051_, v_x_2052_);
v___x_2107_ = ((size_t)7ULL);
v___x_2108_ = lean_usize_dec_le(v___x_2107_, v_x_2050_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2106_);
v___x_2110_ = lean_unsigned_to_nat(4u);
v___x_2111_ = lean_nat_dec_lt(v___x_2109_, v___x_2110_);
lean_dec(v___x_2109_);
if (v___x_2111_ == 0)
{
lean_object* v_ks_2112_; lean_object* v_vs_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_ks_2112_ = lean_ctor_get(v_newNode_2106_, 0);
lean_inc_ref(v_ks_2112_);
v_vs_2113_ = lean_ctor_get(v_newNode_2106_, 1);
lean_inc_ref(v_vs_2113_);
lean_dec_ref(v_newNode_2106_);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___closed__0);
v___x_2116_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_x_2050_, v_ks_2112_, v_vs_2113_, v___x_2114_, v___x_2115_);
lean_dec_ref(v_vs_2113_);
lean_dec_ref(v_ks_2112_);
return v___x_2116_;
}
else
{
return v_newNode_2106_;
}
}
else
{
return v_newNode_2106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(size_t v_depth_2119_, lean_object* v_keys_2120_, lean_object* v_vals_2121_, lean_object* v_i_2122_, lean_object* v_entries_2123_){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_array_get_size(v_keys_2120_);
v___x_2125_ = lean_nat_dec_lt(v_i_2122_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_dec(v_i_2122_);
return v_entries_2123_;
}
else
{
lean_object* v_k_2126_; lean_object* v_v_2127_; uint64_t v___x_2128_; size_t v_h_2129_; size_t v___x_2130_; lean_object* v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v_h_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_k_2126_ = lean_array_fget_borrowed(v_keys_2120_, v_i_2122_);
v_v_2127_ = lean_array_fget_borrowed(v_vals_2121_, v_i_2122_);
v___x_2128_ = l_Lean_instHashableMVarId_hash(v_k_2126_);
v_h_2129_ = lean_uint64_to_usize(v___x_2128_);
v___x_2130_ = ((size_t)5ULL);
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = ((size_t)1ULL);
v___x_2133_ = lean_usize_sub(v_depth_2119_, v___x_2132_);
v___x_2134_ = lean_usize_mul(v___x_2130_, v___x_2133_);
v_h_2135_ = lean_usize_shift_right(v_h_2129_, v___x_2134_);
v___x_2136_ = lean_nat_add(v_i_2122_, v___x_2131_);
lean_dec(v_i_2122_);
lean_inc(v_v_2127_);
lean_inc(v_k_2126_);
v___x_2137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_entries_2123_, v_h_2135_, v_depth_2119_, v_k_2126_, v_v_2127_);
v_i_2122_ = v___x_2136_;
v_entries_2123_ = v___x_2137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_depth_2139_, lean_object* v_keys_2140_, lean_object* v_vals_2141_, lean_object* v_i_2142_, lean_object* v_entries_2143_){
_start:
{
size_t v_depth_boxed_2144_; lean_object* v_res_2145_; 
v_depth_boxed_2144_ = lean_unbox_usize(v_depth_2139_);
lean_dec(v_depth_2139_);
v_res_2145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_boxed_2144_, v_keys_2140_, v_vals_2141_, v_i_2142_, v_entries_2143_);
lean_dec_ref(v_vals_2141_);
lean_dec_ref(v_keys_2140_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_){
_start:
{
size_t v_x_95431__boxed_2151_; size_t v_x_95432__boxed_2152_; lean_object* v_res_2153_; 
v_x_95431__boxed_2151_ = lean_unbox_usize(v_x_2147_);
lean_dec(v_x_2147_);
v_x_95432__boxed_2152_ = lean_unbox_usize(v_x_2148_);
lean_dec(v_x_2148_);
v_res_2153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2146_, v_x_95431__boxed_2151_, v_x_95432__boxed_2152_, v_x_2149_, v_x_2150_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
uint64_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = l_Lean_instHashableMVarId_hash(v_x_2155_);
v___x_2158_ = lean_uint64_to_usize(v___x_2157_);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_2154_, v___x_2158_, v___x_2159_, v_x_2155_, v_x_2156_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(lean_object* v_mvarId_2161_, lean_object* v_val_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; lean_object* v_mctx_2166_; lean_object* v_cache_2167_; lean_object* v_zetaDeltaFVarIds_2168_; lean_object* v_postponed_2169_; lean_object* v_diag_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2199_; 
v___x_2165_ = lean_st_ref_take(v___y_2163_);
v_mctx_2166_ = lean_ctor_get(v___x_2165_, 0);
v_cache_2167_ = lean_ctor_get(v___x_2165_, 1);
v_zetaDeltaFVarIds_2168_ = lean_ctor_get(v___x_2165_, 2);
v_postponed_2169_ = lean_ctor_get(v___x_2165_, 3);
v_diag_2170_ = lean_ctor_get(v___x_2165_, 4);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2172_ = v___x_2165_;
v_isShared_2173_ = v_isSharedCheck_2199_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_diag_2170_);
lean_inc(v_postponed_2169_);
lean_inc(v_zetaDeltaFVarIds_2168_);
lean_inc(v_cache_2167_);
lean_inc(v_mctx_2166_);
lean_dec(v___x_2165_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2199_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_depth_2174_; lean_object* v_levelAssignDepth_2175_; lean_object* v_lmvarCounter_2176_; lean_object* v_mvarCounter_2177_; lean_object* v_lDecls_2178_; lean_object* v_decls_2179_; lean_object* v_userNames_2180_; lean_object* v_lAssignment_2181_; lean_object* v_eAssignment_2182_; lean_object* v_dAssignment_2183_; lean_object* v_instanceTypedMVars_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2198_; 
v_depth_2174_ = lean_ctor_get(v_mctx_2166_, 0);
v_levelAssignDepth_2175_ = lean_ctor_get(v_mctx_2166_, 1);
v_lmvarCounter_2176_ = lean_ctor_get(v_mctx_2166_, 2);
v_mvarCounter_2177_ = lean_ctor_get(v_mctx_2166_, 3);
v_lDecls_2178_ = lean_ctor_get(v_mctx_2166_, 4);
v_decls_2179_ = lean_ctor_get(v_mctx_2166_, 5);
v_userNames_2180_ = lean_ctor_get(v_mctx_2166_, 6);
v_lAssignment_2181_ = lean_ctor_get(v_mctx_2166_, 7);
v_eAssignment_2182_ = lean_ctor_get(v_mctx_2166_, 8);
v_dAssignment_2183_ = lean_ctor_get(v_mctx_2166_, 9);
v_instanceTypedMVars_2184_ = lean_ctor_get(v_mctx_2166_, 10);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_mctx_2166_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2186_ = v_mctx_2166_;
v_isShared_2187_ = v_isSharedCheck_2198_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_instanceTypedMVars_2184_);
lean_inc(v_dAssignment_2183_);
lean_inc(v_eAssignment_2182_);
lean_inc(v_lAssignment_2181_);
lean_inc(v_userNames_2180_);
lean_inc(v_decls_2179_);
lean_inc(v_lDecls_2178_);
lean_inc(v_mvarCounter_2177_);
lean_inc(v_lmvarCounter_2176_);
lean_inc(v_levelAssignDepth_2175_);
lean_inc(v_depth_2174_);
lean_dec(v_mctx_2166_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2198_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2188_ = lean_box(0);
v___x_2189_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_eAssignment_2182_, v_mvarId_2161_, v_val_2162_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 8, v___x_2189_);
v___x_2191_ = v___x_2186_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_depth_2174_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_levelAssignDepth_2175_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_lmvarCounter_2176_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_mvarCounter_2177_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v_lDecls_2178_);
lean_ctor_set(v_reuseFailAlloc_2197_, 5, v_decls_2179_);
lean_ctor_set(v_reuseFailAlloc_2197_, 6, v_userNames_2180_);
lean_ctor_set(v_reuseFailAlloc_2197_, 7, v_lAssignment_2181_);
lean_ctor_set(v_reuseFailAlloc_2197_, 8, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2197_, 9, v_dAssignment_2183_);
lean_ctor_set(v_reuseFailAlloc_2197_, 10, v_instanceTypedMVars_2184_);
v___x_2191_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2191_);
v___x_2193_ = v___x_2172_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_cache_2167_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_zetaDeltaFVarIds_2168_);
lean_ctor_set(v_reuseFailAlloc_2196_, 3, v_postponed_2169_);
lean_ctor_set(v_reuseFailAlloc_2196_, 4, v_diag_2170_);
v___x_2193_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_st_ref_put(v___y_2163_, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2188_);
return v___x_2195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg___boxed(lean_object* v_mvarId_2200_, lean_object* v_val_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_2200_, v_val_2201_, v___y_2202_);
lean_dec(v___y_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_o_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v_env_2210_; lean_object* v___x_2211_; lean_object* v_toEnvExtension_2212_; lean_object* v_asyncMode_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_merged_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2224_; 
v___x_2208_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2209_ = lean_st_ref_get(v___y_2206_);
v_env_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc_ref(v_env_2210_);
lean_dec(v___x_2209_);
v___x_2211_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2212_ = lean_ctor_get(v___x_2211_, 0);
v_asyncMode_2213_ = lean_ctor_get(v_toEnvExtension_2212_, 2);
v___x_2214_ = lean_box(0);
v___x_2215_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2208_, v___x_2211_, v_env_2210_, v_asyncMode_2213_, v___x_2214_);
v_merged_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v___x_2215_, 1);
lean_dec(v_unused_2225_);
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_merged_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_merged_2216_);
lean_ctor_set(v___x_2218_, 0, v_o_2205_);
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_o_2205_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_merged_2216_);
v___x_2221_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg___boxed(lean_object* v_o_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_2226_, v___y_2227_);
lean_dec(v___y_2227_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2236_);
v___x_2240_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v___x_2239_, v___y_2237_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
return v_res_2250_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2266_, lean_object* v_snd_2267_, uint8_t v___x_2268_, lean_object* v___x_2269_, uint8_t v___x_2270_, uint8_t v_useReducible_2271_, uint8_t v___x_2272_, lean_object* v___x_2273_, lean_object* v___x_2274_, lean_object* v_simprocs_2275_, lean_object* v_discharge_x3f_2276_, lean_object* v_snd_2277_, lean_object* v___f_2278_, lean_object* v___x_2279_, lean_object* v___x_2280_, lean_object* v___x_2281_, lean_object* v___x_2282_, lean_object* v___f_2283_, lean_object* v_a_2284_, lean_object* v___x_2285_, lean_object* v___f_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; 
if (lean_obj_tag(v_usingArg_2266_) == 1)
{
lean_object* v_val_2509_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___x_2561_; lean_object* v_infoState_2562_; uint8_t v_enabled_2563_; 
v_val_2509_ = lean_ctor_get(v_usingArg_2266_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v_usingArg_2266_, 1);
v___x_2561_ = lean_st_ref_get(v___y_2294_);
v_infoState_2562_ = lean_ctor_get(v___x_2561_, 8);
lean_inc_ref(v_infoState_2562_);
lean_dec(v___x_2561_);
v_enabled_2563_ = lean_ctor_get_uint8(v_infoState_2562_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2562_);
if (v_enabled_2563_ == 0)
{
lean_dec_ref(v___f_2286_);
v___y_2511_ = v___y_2287_;
v___y_2512_ = v___y_2288_;
v___y_2513_ = v___y_2289_;
v___y_2514_ = v___y_2290_;
v___y_2515_ = v___y_2291_;
v___y_2516_ = v___y_2292_;
v___y_2517_ = v___y_2293_;
v___y_2518_ = v___y_2294_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; 
v___x_2564_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2294_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref(v___x_2564_);
v___f_2566_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2566_, 0, v_a_2565_);
v___x_2567_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2566_, v___f_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_dec_ref_known(v___x_2567_, 1);
v___y_2511_ = v___y_2287_;
v___y_2512_ = v___y_2288_;
v___y_2513_ = v___y_2289_;
v___y_2514_ = v___y_2290_;
v___y_2515_ = v___y_2291_;
v___y_2516_ = v___y_2292_;
v___y_2517_ = v___y_2293_;
v___y_2518_ = v___y_2294_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_val_2509_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
v___jp_2510_:
{
lean_object* v___x_2519_; lean_object* v_mctx_2520_; lean_object* v_mvarCounter_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2519_ = lean_st_ref_get(v___y_2516_);
v_mctx_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_mctx_2520_);
lean_dec(v___x_2519_);
v_mvarCounter_2521_ = lean_ctor_get(v_mctx_2520_, 3);
lean_inc(v_mvarCounter_2521_);
lean_dec_ref(v_mctx_2520_);
v___x_2522_ = lean_box(0);
v___x_2523_ = l_Lean_Elab_Tactic_elabTerm(v_val_2509_, v___x_2522_, v___x_2268_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_n(v_a_2524_, 2);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2525_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_snd_2267_, v_a_2524_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; uint8_t v___x_2527_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2527_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_mvarCounter_2521_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
v___x_2528_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2529_ = l_Lean_indentExpr(v_a_2524_);
v___x_2530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = l_Lean_Expr_mvar___override(v_snd_2267_);
v___x_2534_ = l_Lean_MessageData_ofExpr(v___x_2533_);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2532_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2535_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
v___y_2361_ = v___x_2522_;
v___y_2362_ = v_a_2524_;
v___y_2363_ = v_mvarCounter_2521_;
v___y_2364_ = v___x_2522_;
v___y_2365_ = v___y_2511_;
v___y_2366_ = v___y_2512_;
v___y_2367_ = v___y_2513_;
v___y_2368_ = v___y_2514_;
v___y_2369_ = v___y_2515_;
v___y_2370_ = v___y_2516_;
v___y_2371_ = v___y_2517_;
v___y_2372_ = v___y_2518_;
goto v___jp_2360_;
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2524_);
lean_dec(v_mvarCounter_2521_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2545_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2525_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2525_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_mvarCounter_2521_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2553_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2523_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2523_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
else
{
lean_object* v_lctx_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec_ref(v___f_2286_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v___x_2269_);
lean_dec(v_usingArg_2266_);
v_lctx_2576_ = lean_ctor_get(v___y_2291_, 2);
v___x_2577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10));
v___x_2578_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2576_, v___x_2577_);
if (lean_obj_tag(v___x_2578_) == 1)
{
lean_object* v_val_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v_val_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___x_2580_ = l_Lean_LocalDecl_fvarId(v_val_2579_);
lean_dec(v_val_2579_);
v___x_2581_ = lean_mk_empty_array_with_capacity(v___x_2273_);
v___x_2582_ = lean_array_push(v___x_2581_, v___x_2580_);
lean_inc_ref(v_snd_2277_);
v___x_2583_ = l_Lean_Meta_simpGoal(v_snd_2267_, v___x_2274_, v_simprocs_2275_, v_discharge_x3f_2276_, v___x_2270_, v___x_2582_, v_snd_2277_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2612_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2612_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2612_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v_fst_2588_; 
v_fst_2588_ = lean_ctor_get(v_a_2584_, 0);
if (lean_obj_tag(v_fst_2588_) == 1)
{
lean_object* v_val_2589_; lean_object* v_snd_2590_; lean_object* v_snd_2591_; lean_object* v___x_2592_; 
lean_del_object(v___x_2586_);
lean_dec_ref(v_snd_2277_);
v_val_2589_ = lean_ctor_get(v_fst_2588_, 0);
lean_inc(v_val_2589_);
v_snd_2590_ = lean_ctor_get(v_a_2584_, 1);
lean_inc(v_snd_2590_);
lean_dec(v_a_2584_);
v_snd_2591_ = lean_ctor_get(v_val_2589_, 1);
lean_inc(v_snd_2591_);
lean_dec(v_val_2589_);
v___x_2592_ = l_Lean_MVarId_assumption(v_snd_2591_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v___x_2592_, 0);
lean_dec(v_unused_2600_);
v___x_2594_ = v___x_2592_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_dec(v___x_2592_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_snd_2590_);
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_snd_2590_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec(v_snd_2590_);
v_a_2601_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2592_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2592_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v___x_2610_; 
lean_dec(v_a_2584_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v_snd_2277_);
v___x_2610_ = v___x_2586_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_snd_2277_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_snd_2277_);
v_a_2613_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2583_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2583_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v___x_2621_; 
lean_dec(v___x_2578_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
v___x_2621_ = l_Lean_MVarId_assumption(v_snd_2267_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v___x_2621_, 0);
lean_dec(v_unused_2629_);
v___x_2623_ = v___x_2621_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_dec(v___x_2621_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v_snd_2277_);
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_snd_2277_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_snd_2277_);
v_a_2630_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2621_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2621_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
v___jp_2296_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
v___x_2300_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_snd_2267_, v___y_2297_, v___y_2299_);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2307_ == 0)
{
lean_object* v_unused_2308_; 
v_unused_2308_ = lean_ctor_get(v___x_2300_, 0);
lean_dec(v_unused_2308_);
v___x_2302_ = v___x_2300_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v___x_2300_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___y_2298_);
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___y_2298_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
v___jp_2309_:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Core_mkFreshUserName(v___y_2314_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_n(v_a_2327_, 2);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = l_Lean_MVarId_rename(v___y_2324_, v___y_2325_, v_a_2327_, v___y_2319_, v___y_2313_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_n(v_a_2329_, 2);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = lean_box(v___x_2268_);
v___x_2331_ = lean_box(v___x_2270_);
v___x_2332_ = lean_box(v_useReducible_2271_);
v___x_2333_ = lean_box(v___x_2272_);
v___f_2334_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2334_, 0, v_a_2329_);
lean_closure_set(v___f_2334_, 1, v_a_2327_);
lean_closure_set(v___f_2334_, 2, v___x_2330_);
lean_closure_set(v___f_2334_, 3, v___y_2311_);
lean_closure_set(v___f_2334_, 4, v___y_2312_);
lean_closure_set(v___f_2334_, 5, v___x_2269_);
lean_closure_set(v___f_2334_, 6, v___x_2331_);
lean_closure_set(v___f_2334_, 7, v___y_2310_);
lean_closure_set(v___f_2334_, 8, v___x_2332_);
lean_closure_set(v___f_2334_, 9, v___x_2333_);
v___x_2335_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_a_2329_, v___f_2334_, v___y_2321_, v___y_2317_, v___y_2316_, v___y_2315_, v___y_2319_, v___y_2313_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_dec_ref_known(v___x_2335_, 1);
v___y_2297_ = v___y_2318_;
v___y_2298_ = v___y_2320_;
v___y_2299_ = v___y_2313_;
goto v___jp_2296_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2318_);
lean_dec(v_snd_2267_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_a_2327_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2344_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2328_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2328_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2352_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2326_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2326_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
v___jp_2360_:
{
lean_object* v___x_2373_; 
lean_inc(v_snd_2267_);
v___x_2373_ = l_Lean_MVarId_getType(v_snd_2267_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
lean_inc(v_snd_2267_);
v___x_2375_ = l_Lean_MVarId_getTag(v_snd_2267_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2374_, v_a_2376_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2377_, 1);
v___x_2379_ = l_Lean_Expr_mvarId_x21(v_a_2378_);
v___x_2380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1));
lean_inc_ref(v___y_2362_);
v___x_2381_ = l_Lean_MVarId_note(v___x_2379_, v___x_2380_, v___y_2362_, v___y_2364_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v_fst_2383_; lean_object* v_snd_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v_fst_2383_ = lean_ctor_get(v_a_2382_, 0);
lean_inc_n(v_fst_2383_, 2);
v_snd_2384_ = lean_ctor_get(v_a_2382_, 1);
lean_inc(v_snd_2384_);
lean_dec(v_a_2382_);
v___x_2385_ = lean_mk_empty_array_with_capacity(v___x_2273_);
v___x_2386_ = lean_array_push(v___x_2385_, v_fst_2383_);
v___x_2387_ = l_Lean_Meta_simpGoal(v_snd_2384_, v___x_2274_, v_simprocs_2275_, v_discharge_x3f_2276_, v___x_2270_, v___x_2386_, v_snd_2277_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v_fst_2389_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v_fst_2389_ = lean_ctor_get(v_a_2388_, 0);
if (lean_obj_tag(v_fst_2389_) == 0)
{
lean_object* v_snd_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_fst_2383_);
lean_dec(v___y_2363_);
lean_dec(v___y_2361_);
lean_dec_ref(v___x_2269_);
v_snd_2390_ = lean_ctor_get(v_a_2388_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_a_2388_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v_a_2388_, 0);
lean_dec(v_unused_2461_);
v___x_2392_ = v_a_2388_;
v_isShared_2393_ = v_isSharedCheck_2460_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_snd_2390_);
lean_dec(v_a_2388_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2460_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v_a_2395_; uint8_t v___x_2396_; 
v___x_2394_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2395_);
lean_dec(v_a_2395_);
if (v___x_2396_ == 0)
{
lean_del_object(v___x_2392_);
lean_dec_ref(v___y_2362_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
v___y_2297_ = v_a_2378_;
v___y_2298_ = v_snd_2390_;
v___y_2299_ = v___y_2370_;
goto v___jp_2296_;
}
else
{
if (lean_obj_tag(v___y_2362_) == 1)
{
lean_object* v_fvarId_2397_; lean_object* v_lctx_2398_; lean_object* v___x_2399_; 
v_fvarId_2397_ = lean_ctor_get(v___y_2362_, 0);
lean_inc(v_fvarId_2397_);
lean_dec_ref_known(v___y_2362_, 1);
v_lctx_2398_ = lean_ctor_get(v___y_2369_, 2);
lean_inc_ref(v_lctx_2398_);
v___x_2399_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2398_, v_fvarId_2397_);
if (lean_obj_tag(v___x_2399_) == 1)
{
lean_object* v_val_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2459_; 
v_val_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2459_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_val_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2459_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = l_Lean_mkIdent(v_val_2400_);
lean_inc_ref(v___f_2278_);
lean_inc(v___y_2372_);
lean_inc_ref(v___y_2371_);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
v___x_2405_ = lean_apply_9(v___f_2278_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, lean_box(0));
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc_n(v_a_2406_, 2);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2281_);
lean_inc_ref(v___x_2280_);
lean_inc_ref(v___x_2279_);
v___x_2408_ = l_Lean_Name_mkStr4(v___x_2279_, v___x_2280_, v___x_2281_, v___x_2407_);
v___x_2409_ = l_Lean_Syntax_node1(v_a_2406_, v___x_2282_, v___x_2404_);
v___x_2410_ = l_Lean_Syntax_node1(v_a_2406_, v___x_2408_, v___x_2409_);
lean_inc(v___y_2372_);
lean_inc_ref(v___y_2371_);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
v___x_2411_ = lean_apply_9(v___f_2278_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, lean_box(0));
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v_ref_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc_n(v_a_2412_, 2);
lean_dec_ref_known(v___x_2411_, 1);
v_ref_2413_ = lean_ctor_get(v___y_2371_, 2);
v___x_2414_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 2);
lean_ctor_set(v___x_2392_, 1, v___x_2414_);
lean_ctor_set(v___x_2392_, 0, v_a_2412_);
v___x_2416_ = v___x_2392_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2412_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2418_ = l_Lean_Name_mkStr4(v___x_2279_, v___x_2280_, v___x_2281_, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node2(v_a_2412_, v___x_2418_, v___x_2416_, v___x_2410_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2419_);
v___x_2421_ = v___x_2402_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; 
lean_inc(v___y_2372_);
lean_inc_ref(v___y_2371_);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
v___x_2422_ = lean_apply_10(v___f_2283_, v___x_2421_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, lean_box(0));
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
lean_inc(v_ref_2413_);
v___x_2424_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2284_, v_ref_2413_, v_a_2423_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_dec_ref_known(v___x_2424_, 1);
v___y_2297_ = v_a_2378_;
v___y_2298_ = v_snd_2390_;
v___y_2299_ = v___y_2370_;
goto v___jp_2296_;
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_snd_2390_);
lean_dec(v_a_2378_);
lean_dec(v_snd_2267_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_snd_2390_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2284_);
lean_dec(v_snd_2267_);
v_a_2433_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2422_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2422_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v___x_2410_);
lean_del_object(v___x_2402_);
lean_del_object(v___x_2392_);
lean_dec(v_snd_2390_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec(v_snd_2267_);
v_a_2443_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2411_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2411_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v___x_2404_);
lean_del_object(v___x_2402_);
lean_del_object(v___x_2392_);
lean_dec(v_snd_2390_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec(v_snd_2267_);
v_a_2451_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2405_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2405_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
else
{
lean_dec(v___x_2399_);
lean_del_object(v___x_2392_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
v___y_2297_ = v_a_2378_;
v___y_2298_ = v_snd_2390_;
v___y_2299_ = v___y_2370_;
goto v___jp_2296_;
}
}
else
{
lean_del_object(v___x_2392_);
lean_dec_ref(v___y_2362_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
v___y_2297_ = v_a_2378_;
v___y_2298_ = v_snd_2390_;
v___y_2299_ = v___y_2370_;
goto v___jp_2296_;
}
}
}
}
else
{
lean_object* v_val_2462_; lean_object* v_snd_2463_; lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
v_val_2462_ = lean_ctor_get(v_fst_2389_, 0);
lean_inc(v_val_2462_);
v_snd_2463_ = lean_ctor_get(v_a_2388_, 1);
lean_inc(v_snd_2463_);
lean_dec(v_a_2388_);
v_fst_2464_ = lean_ctor_get(v_val_2462_, 0);
lean_inc(v_fst_2464_);
v_snd_2465_ = lean_ctor_get(v_val_2462_, 1);
lean_inc(v_snd_2465_);
lean_dec(v_val_2462_);
v___x_2466_ = lean_array_get_size(v_fst_2464_);
v___x_2467_ = lean_nat_dec_lt(v___x_2285_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_dec(v_fst_2464_);
v___y_2310_ = v___y_2361_;
v___y_2311_ = v___y_2362_;
v___y_2312_ = v___y_2363_;
v___y_2313_ = v___y_2370_;
v___y_2314_ = v___x_2380_;
v___y_2315_ = v___y_2368_;
v___y_2316_ = v___y_2367_;
v___y_2317_ = v___y_2366_;
v___y_2318_ = v_a_2378_;
v___y_2319_ = v___y_2369_;
v___y_2320_ = v_snd_2463_;
v___y_2321_ = v___y_2365_;
v___y_2322_ = v___y_2371_;
v___y_2323_ = v___y_2372_;
v___y_2324_ = v_snd_2465_;
v___y_2325_ = v_fst_2383_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2468_; 
lean_dec(v_fst_2383_);
v___x_2468_ = lean_array_fget(v_fst_2464_, v___x_2285_);
lean_dec(v_fst_2464_);
v___y_2310_ = v___y_2361_;
v___y_2311_ = v___y_2362_;
v___y_2312_ = v___y_2363_;
v___y_2313_ = v___y_2370_;
v___y_2314_ = v___x_2380_;
v___y_2315_ = v___y_2368_;
v___y_2316_ = v___y_2367_;
v___y_2317_ = v___y_2366_;
v___y_2318_ = v_a_2378_;
v___y_2319_ = v___y_2369_;
v___y_2320_ = v_snd_2463_;
v___y_2321_ = v___y_2365_;
v___y_2322_ = v___y_2371_;
v___y_2323_ = v___y_2372_;
v___y_2324_ = v_snd_2465_;
v___y_2325_ = v___x_2468_;
goto v___jp_2309_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_fst_2383_);
lean_dec(v_a_2378_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2469_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2387_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2387_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_a_2378_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2477_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2381_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2381_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2485_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2377_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2377_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_a_2374_);
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2493_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2375_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2375_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v_a_2284_);
lean_dec_ref(v___f_2283_);
lean_dec(v___x_2282_);
lean_dec_ref(v___x_2281_);
lean_dec_ref(v___x_2280_);
lean_dec_ref(v___x_2279_);
lean_dec_ref(v___f_2278_);
lean_dec_ref(v_snd_2277_);
lean_dec(v_discharge_x3f_2276_);
lean_dec_ref(v_simprocs_2275_);
lean_dec_ref(v___x_2274_);
lean_dec_ref(v___x_2269_);
lean_dec(v_snd_2267_);
v_a_2501_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2373_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2373_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v_usingArg_2638_ = _args[0];
lean_object* v_snd_2639_ = _args[1];
lean_object* v___x_2640_ = _args[2];
lean_object* v___x_2641_ = _args[3];
lean_object* v___x_2642_ = _args[4];
lean_object* v_useReducible_2643_ = _args[5];
lean_object* v___x_2644_ = _args[6];
lean_object* v___x_2645_ = _args[7];
lean_object* v___x_2646_ = _args[8];
lean_object* v_simprocs_2647_ = _args[9];
lean_object* v_discharge_x3f_2648_ = _args[10];
lean_object* v_snd_2649_ = _args[11];
lean_object* v___f_2650_ = _args[12];
lean_object* v___x_2651_ = _args[13];
lean_object* v___x_2652_ = _args[14];
lean_object* v___x_2653_ = _args[15];
lean_object* v___x_2654_ = _args[16];
lean_object* v___f_2655_ = _args[17];
lean_object* v_a_2656_ = _args[18];
lean_object* v___x_2657_ = _args[19];
lean_object* v___f_2658_ = _args[20];
lean_object* v___y_2659_ = _args[21];
lean_object* v___y_2660_ = _args[22];
lean_object* v___y_2661_ = _args[23];
lean_object* v___y_2662_ = _args[24];
lean_object* v___y_2663_ = _args[25];
lean_object* v___y_2664_ = _args[26];
lean_object* v___y_2665_ = _args[27];
lean_object* v___y_2666_ = _args[28];
lean_object* v___y_2667_ = _args[29];
_start:
{
uint8_t v___x_95742__boxed_2668_; uint8_t v___x_95744__boxed_2669_; uint8_t v_useReducible_boxed_2670_; uint8_t v___x_95745__boxed_2671_; lean_object* v_res_2672_; 
v___x_95742__boxed_2668_ = lean_unbox(v___x_2640_);
v___x_95744__boxed_2669_ = lean_unbox(v___x_2642_);
v_useReducible_boxed_2670_ = lean_unbox(v_useReducible_2643_);
v___x_95745__boxed_2671_ = lean_unbox(v___x_2644_);
v_res_2672_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2638_, v_snd_2639_, v___x_95742__boxed_2668_, v___x_2641_, v___x_95744__boxed_2669_, v_useReducible_boxed_2670_, v___x_95745__boxed_2671_, v___x_2645_, v___x_2646_, v_simprocs_2647_, v_discharge_x3f_2648_, v_snd_2649_, v___f_2650_, v___x_2651_, v___x_2652_, v___x_2653_, v___x_2654_, v___f_2655_, v_a_2656_, v___x_2657_, v___f_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___x_2657_);
lean_dec(v___x_2645_);
return v_res_2672_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0(void){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2673_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_unsigned_to_nat(32u);
v___x_2677_ = lean_mk_empty_array_with_capacity(v___x_2676_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2679_, lean_object* v_tk_2680_, lean_object* v___x_2681_, lean_object* v___x_2682_, lean_object* v___x_2683_, lean_object* v_simprocs_2684_, uint8_t v___x_2685_, lean_object* v_usingArg_2686_, lean_object* v___x_2687_, uint8_t v___x_2688_, uint8_t v_useReducible_2689_, uint8_t v___x_2690_, lean_object* v___x_2691_, lean_object* v___f_2692_, lean_object* v___x_2693_, lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v___f_2696_, lean_object* v_a_2697_, lean_object* v_usingTk_x3f_2698_, lean_object* v_discharge_x3f_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___y_2710_; 
if (lean_obj_tag(v_usingTk_x3f_2698_) == 0)
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_box(0);
v___y_2710_ = v___x_2824_;
goto v___jp_2709_;
}
else
{
lean_object* v_val_2825_; 
v_val_2825_ = lean_ctor_get(v_usingTk_x3f_2698_, 0);
lean_inc(v_val_2825_);
lean_dec_ref_known(v_usingTk_x3f_2698_, 1);
v___y_2710_ = v_val_2825_;
goto v___jp_2709_;
}
v___jp_2709_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2711_ = lean_mk_empty_array_with_capacity(v___x_2679_);
v___x_2712_ = lean_array_push(v___x_2711_, v_tk_2680_);
v___x_2713_ = lean_array_push(v___x_2712_, v___y_2710_);
v___x_2714_ = lean_box(2);
lean_inc(v___x_2681_);
v___x_2715_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v___x_2681_);
lean_ctor_set(v___x_2715_, 2, v___x_2713_);
v___x_2716_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2715_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___f_2718_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2718_, 0, v_a_2717_);
v___x_2719_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2701_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; size_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___x_2721_ = lean_mk_empty_array_with_capacity(v___x_2682_);
v___x_2722_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2682_, 3);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v___x_2682_);
v___x_2724_ = lean_unsigned_to_nat(32u);
v___x_2725_ = lean_mk_empty_array_with_capacity(v___x_2724_);
v___x_2726_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2727_ = ((size_t)5ULL);
v___x_2728_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2725_);
lean_ctor_set(v___x_2728_, 2, v___x_2682_);
lean_ctor_set(v___x_2728_, 3, v___x_2682_);
lean_ctor_set_usize(v___x_2728_, 4, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2722_);
lean_ctor_set(v___x_2729_, 1, v___x_2722_);
lean_ctor_set(v___x_2729_, 2, v___x_2722_);
lean_ctor_set(v___x_2729_, 3, v___x_2728_);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2723_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
lean_inc_ref(v___x_2730_);
lean_inc(v_discharge_x3f_2699_);
lean_inc_ref(v_simprocs_2684_);
lean_inc_ref(v___x_2683_);
v___x_2731_ = l_Lean_Meta_simpGoal(v_a_2720_, v___x_2683_, v_simprocs_2684_, v_discharge_x3f_2699_, v___x_2685_, v___x_2721_, v___x_2730_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v_fst_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v_fst_2733_ = lean_ctor_get(v_a_2732_, 0);
if (lean_obj_tag(v_fst_2733_) == 1)
{
lean_object* v_val_2734_; lean_object* v_snd_2735_; lean_object* v_snd_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref_known(v___x_2730_, 2);
v_val_2734_ = lean_ctor_get(v_fst_2733_, 0);
lean_inc(v_val_2734_);
v_snd_2735_ = lean_ctor_get(v_a_2732_, 1);
lean_inc(v_snd_2735_);
lean_dec(v_a_2732_);
v_snd_2736_ = lean_ctor_get(v_val_2734_, 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_val_2734_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v_val_2734_, 0);
lean_dec(v_unused_2760_);
v___x_2738_ = v_val_2734_;
v_isShared_2739_ = v_isSharedCheck_2759_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_snd_2736_);
lean_dec(v_val_2734_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2759_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___y_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2740_ = lean_box(v___x_2685_);
v___x_2741_ = lean_box(v___x_2688_);
v___x_2742_ = lean_box(v_useReducible_2689_);
v___x_2743_ = lean_box(v___x_2690_);
lean_inc_n(v_snd_2736_, 2);
v___y_2744_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2744_, 0, v_usingArg_2686_);
lean_closure_set(v___y_2744_, 1, v_snd_2736_);
lean_closure_set(v___y_2744_, 2, v___x_2740_);
lean_closure_set(v___y_2744_, 3, v___x_2687_);
lean_closure_set(v___y_2744_, 4, v___x_2741_);
lean_closure_set(v___y_2744_, 5, v___x_2742_);
lean_closure_set(v___y_2744_, 6, v___x_2743_);
lean_closure_set(v___y_2744_, 7, v___x_2691_);
lean_closure_set(v___y_2744_, 8, v___x_2683_);
lean_closure_set(v___y_2744_, 9, v_simprocs_2684_);
lean_closure_set(v___y_2744_, 10, v_discharge_x3f_2699_);
lean_closure_set(v___y_2744_, 11, v_snd_2735_);
lean_closure_set(v___y_2744_, 12, v___f_2692_);
lean_closure_set(v___y_2744_, 13, v___x_2693_);
lean_closure_set(v___y_2744_, 14, v___x_2694_);
lean_closure_set(v___y_2744_, 15, v___x_2695_);
lean_closure_set(v___y_2744_, 16, v___x_2681_);
lean_closure_set(v___y_2744_, 17, v___f_2696_);
lean_closure_set(v___y_2744_, 18, v_a_2697_);
lean_closure_set(v___y_2744_, 19, v___x_2682_);
lean_closure_set(v___y_2744_, 20, v___f_2718_);
v___x_2745_ = lean_box(0);
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 1);
lean_ctor_set(v___x_2738_, 1, v___x_2745_);
lean_ctor_set(v___x_2738_, 0, v_snd_2736_);
v___x_2747_ = v___x_2738_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_snd_2736_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2747_, v___y_2701_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; 
lean_dec_ref_known(v___x_2748_, 1);
v___x_2749_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___redArg(v_snd_2736_, v___y_2744_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2749_;
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec_ref(v___y_2744_);
lean_dec(v_snd_2736_);
v_a_2750_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2748_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2748_);
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
else
{
lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_a_2732_);
lean_dec_ref(v___f_2718_);
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2687_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v___x_2761_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2799_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2799_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2762_);
lean_dec(v_a_2762_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2768_; 
lean_dec_ref(v_a_2697_);
lean_dec_ref(v___f_2696_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2730_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2730_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
lean_object* v_ref_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_del_object(v___x_2764_);
v_ref_2770_ = lean_ctor_get(v___y_2706_, 2);
v___x_2771_ = lean_box(0);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
v___x_2772_ = lean_apply_10(v___f_2696_, v___x_2771_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, lean_box(0));
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2774_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
lean_inc(v_ref_2770_);
v___x_2774_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2697_, v_ref_2770_, v_a_2773_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v___x_2774_, 0);
lean_dec(v_unused_2782_);
v___x_2776_ = v___x_2774_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_dec(v___x_2774_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2730_);
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2730_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec_ref_known(v___x_2730_, 2);
v_a_2783_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2774_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2774_);
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
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec_ref_known(v___x_2730_, 2);
lean_dec_ref(v_a_2697_);
v_a_2791_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2772_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2772_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec_ref_known(v___x_2730_, 2);
lean_dec_ref(v___f_2718_);
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2687_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v_a_2800_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2731_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2731_);
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
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v___f_2718_);
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2687_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v_a_2808_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2719_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2719_);
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
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_discharge_x3f_2699_);
lean_dec_ref(v_a_2697_);
lean_dec_ref(v___f_2696_);
lean_dec_ref(v___x_2695_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v___x_2693_);
lean_dec_ref(v___f_2692_);
lean_dec(v___x_2691_);
lean_dec_ref(v___x_2687_);
lean_dec(v_usingArg_2686_);
lean_dec_ref(v_simprocs_2684_);
lean_dec_ref(v___x_2683_);
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
v_a_2816_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2716_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2716_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v___x_2826_ = _args[0];
lean_object* v_tk_2827_ = _args[1];
lean_object* v___x_2828_ = _args[2];
lean_object* v___x_2829_ = _args[3];
lean_object* v___x_2830_ = _args[4];
lean_object* v_simprocs_2831_ = _args[5];
lean_object* v___x_2832_ = _args[6];
lean_object* v_usingArg_2833_ = _args[7];
lean_object* v___x_2834_ = _args[8];
lean_object* v___x_2835_ = _args[9];
lean_object* v_useReducible_2836_ = _args[10];
lean_object* v___x_2837_ = _args[11];
lean_object* v___x_2838_ = _args[12];
lean_object* v___f_2839_ = _args[13];
lean_object* v___x_2840_ = _args[14];
lean_object* v___x_2841_ = _args[15];
lean_object* v___x_2842_ = _args[16];
lean_object* v___f_2843_ = _args[17];
lean_object* v_a_2844_ = _args[18];
lean_object* v_usingTk_x3f_2845_ = _args[19];
lean_object* v_discharge_x3f_2846_ = _args[20];
lean_object* v___y_2847_ = _args[21];
lean_object* v___y_2848_ = _args[22];
lean_object* v___y_2849_ = _args[23];
lean_object* v___y_2850_ = _args[24];
lean_object* v___y_2851_ = _args[25];
lean_object* v___y_2852_ = _args[26];
lean_object* v___y_2853_ = _args[27];
lean_object* v___y_2854_ = _args[28];
lean_object* v___y_2855_ = _args[29];
_start:
{
uint8_t v___x_96535__boxed_2856_; uint8_t v___x_96537__boxed_2857_; uint8_t v_useReducible_boxed_2858_; uint8_t v___x_96538__boxed_2859_; lean_object* v_res_2860_; 
v___x_96535__boxed_2856_ = lean_unbox(v___x_2832_);
v___x_96537__boxed_2857_ = lean_unbox(v___x_2835_);
v_useReducible_boxed_2858_ = lean_unbox(v_useReducible_2836_);
v___x_96538__boxed_2859_ = lean_unbox(v___x_2837_);
v_res_2860_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2826_, v_tk_2827_, v___x_2828_, v___x_2829_, v___x_2830_, v_simprocs_2831_, v___x_96535__boxed_2856_, v_usingArg_2833_, v___x_2834_, v___x_96537__boxed_2857_, v_useReducible_boxed_2858_, v___x_96538__boxed_2859_, v___x_2838_, v___f_2839_, v___x_2840_, v___x_2841_, v___x_2842_, v___f_2843_, v_a_2844_, v_usingTk_x3f_2845_, v_discharge_x3f_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___x_2826_);
return v_res_2860_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2866_ = lean_unsigned_to_nat(38u);
v___x_2867_ = lean_unsigned_to_nat(159u);
v___x_2868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2869_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2870_ = l_mkPanicMessageWithDecl(v___x_2869_, v___x_2868_, v___x_2867_, v___x_2866_, v___x_2865_);
return v___x_2870_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2879_ = lean_unsigned_to_nat(15u);
v___x_2880_ = lean_unsigned_to_nat(160u);
v___x_2881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2883_ = l_mkPanicMessageWithDecl(v___x_2882_, v___x_2881_, v___x_2880_, v___x_2879_, v___x_2878_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object* v_tk_2885_, lean_object* v___x_2886_, lean_object* v___x_2887_, lean_object* v___x_2888_, lean_object* v___x_2889_, uint8_t v___x_2890_, lean_object* v___x_2891_, lean_object* v___x_2892_, uint8_t v_useReducible_2893_, lean_object* v___f_2894_, lean_object* v___x_2895_, lean_object* v___x_2896_, lean_object* v___x_2897_, lean_object* v___x_2898_, lean_object* v___x_2899_, lean_object* v___x_2900_, lean_object* v_usingArg_2901_, lean_object* v___x_2902_, uint8_t v___x_2903_, lean_object* v___f_2904_, lean_object* v_usingTk_x3f_2905_, lean_object* v_squeeze_2906_, lean_object* v_unfold_2907_, lean_object* v_args_2908_, lean_object* v_only_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___y_2921_; lean_object* v___y_2925_; lean_object* v_stx_2926_; lean_object* v___y_2927_; lean_object* v_ref_2928_; lean_object* v___y_2929_; lean_object* v___y_2948_; lean_object* v_stx_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2912_, v___y_2914_, v___y_2916_, v___y_2918_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v_ref_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; uint8_t v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v_args_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; uint8_t v___y_3431_; lean_object* v_only_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3460_; uint8_t v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3520_; uint8_t v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3611_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v_ref_2976_ = lean_ctor_get(v___y_2917_, 2);
v___x_2977_ = 0;
v___x_2978_ = l_Lean_SourceInfo_fromRef(v_ref_2976_, v___x_2977_);
v___x_2979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
lean_inc_ref(v___x_2888_);
lean_inc_ref(v___x_2887_);
lean_inc_ref(v___x_2886_);
v___x_2980_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_2979_);
lean_inc(v___x_2978_);
v___x_2981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2978_);
lean_ctor_set(v___x_2981_, 1, v___x_2979_);
v___x_2982_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_2983_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_2910_) == 0)
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3611_ = v___x_3620_;
goto v___jp_3610_;
}
else
{
lean_object* v_val_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_val_3621_ = lean_ctor_get(v___y_2910_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v___y_2910_, 1);
v___x_3622_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3623_ = lean_array_push(v___x_3622_, v_val_3621_);
v___y_3611_ = v___x_3623_;
goto v___jp_3610_;
}
v___jp_2984_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2996_ = l_Array_append___redArg(v___x_2983_, v___y_2995_);
lean_dec_ref(v___y_2995_);
lean_inc_n(v___y_2988_, 2);
v___x_2997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2997_, 0, v___y_2988_);
lean_ctor_set(v___x_2997_, 1, v___x_2982_);
lean_ctor_set(v___x_2997_, 2, v___x_2996_);
v___x_2998_ = l_Lean_Syntax_node5(v___y_2988_, v___x_2891_, v___y_2986_, v___y_2993_, v___y_2994_, v___y_2992_, v___x_2997_);
v___x_2999_ = l_Lean_Syntax_node2(v___y_2988_, v___y_2989_, v___y_2987_, v___x_2998_);
v___y_2948_ = v___y_2990_;
v_stx_2949_ = v___x_2999_;
v___y_2950_ = v___y_2985_;
v___y_2951_ = v___y_2991_;
goto v___jp_2947_;
}
v___jp_3000_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = l_Array_append___redArg(v___x_2983_, v___y_3011_);
lean_dec_ref(v___y_3011_);
lean_inc(v___y_3005_);
v___x_3013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3013_, 0, v___y_3005_);
lean_ctor_set(v___x_3013_, 1, v___x_2982_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
if (lean_obj_tag(v___y_3003_) == 1)
{
lean_object* v_val_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec(v___x_2889_);
v_val_3014_ = lean_ctor_get(v___y_3003_, 0);
lean_inc(v_val_3014_);
lean_dec_ref_known(v___y_3003_, 1);
v___x_3015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3005_);
v___x_3016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___y_3005_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = l_Array_mkArray2___redArg(v___x_3016_, v_val_3014_);
v___y_2985_ = v___y_3001_;
v___y_2986_ = v___y_3002_;
v___y_2987_ = v___y_3004_;
v___y_2988_ = v___y_3005_;
v___y_2989_ = v___y_3006_;
v___y_2990_ = v___y_3008_;
v___y_2991_ = v___y_3007_;
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___y_3009_;
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___x_3017_;
goto v___jp_2984_;
}
else
{
lean_object* v___x_3018_; 
lean_dec(v___y_3003_);
v___x_3018_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_2985_ = v___y_3001_;
v___y_2986_ = v___y_3002_;
v___y_2987_ = v___y_3004_;
v___y_2988_ = v___y_3005_;
v___y_2989_ = v___y_3006_;
v___y_2990_ = v___y_3008_;
v___y_2991_ = v___y_3007_;
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___y_3009_;
v___y_2994_ = v___y_3010_;
v___y_2995_ = v___x_3018_;
goto v___jp_2984_;
}
}
v___jp_3019_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = l_Array_append___redArg(v___x_2983_, v___y_3030_);
lean_dec_ref(v___y_3030_);
lean_inc(v___y_3024_);
v___x_3032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3032_, 0, v___y_3024_);
lean_ctor_set(v___x_3032_, 1, v___x_2982_);
lean_ctor_set(v___x_3032_, 2, v___x_3031_);
if (lean_obj_tag(v___y_3029_) == 1)
{
lean_object* v_val_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_val_3033_ = lean_ctor_get(v___y_3029_, 0);
lean_inc(v_val_3033_);
lean_dec_ref_known(v___y_3029_, 1);
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3035_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3034_);
v___x_3036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3024_, 4);
v___x_3037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___y_3024_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Array_append___redArg(v___x_2983_, v_val_3033_);
lean_dec(v_val_3033_);
v___x_3039_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3039_, 0, v___y_3024_);
lean_ctor_set(v___x_3039_, 1, v___x_2982_);
lean_ctor_set(v___x_3039_, 2, v___x_3038_);
v___x_3040_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3041_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___y_3024_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = l_Lean_Syntax_node3(v___y_3024_, v___x_3035_, v___x_3037_, v___x_3039_, v___x_3041_);
v___x_3043_ = l_Array_mkArray1___redArg(v___x_3042_);
v___y_3001_ = v___y_3020_;
v___y_3002_ = v___y_3021_;
v___y_3003_ = v___y_3023_;
v___y_3004_ = v___y_3022_;
v___y_3005_ = v___y_3024_;
v___y_3006_ = v___y_3025_;
v___y_3007_ = v___y_3027_;
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___x_3032_;
v___y_3011_ = v___x_3043_;
goto v___jp_3000_;
}
else
{
lean_object* v___x_3044_; 
lean_dec(v___y_3029_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3044_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3001_ = v___y_3020_;
v___y_3002_ = v___y_3021_;
v___y_3003_ = v___y_3023_;
v___y_3004_ = v___y_3022_;
v___y_3005_ = v___y_3024_;
v___y_3006_ = v___y_3025_;
v___y_3007_ = v___y_3027_;
v___y_3008_ = v___y_3026_;
v___y_3009_ = v___y_3028_;
v___y_3010_ = v___x_3032_;
v___y_3011_ = v___x_3044_;
goto v___jp_3000_;
}
}
v___jp_3045_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = l_Array_append___redArg(v___x_2983_, v___y_3056_);
lean_dec_ref(v___y_3056_);
lean_inc(v___y_3051_);
v___x_3058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3058_, 0, v___y_3051_);
lean_ctor_set(v___x_3058_, 1, v___x_2982_);
lean_ctor_set(v___x_3058_, 2, v___x_3057_);
if (lean_obj_tag(v___y_3048_) == 1)
{
lean_object* v_val_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_val_3059_ = lean_ctor_get(v___y_3048_, 0);
lean_inc(v_val_3059_);
lean_dec_ref_known(v___y_3048_, 1);
v___x_3060_ = l_Lean_SourceInfo_fromRef(v_val_3059_, v___x_2890_);
lean_dec(v_val_3059_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = l_Array_mkArray1___redArg(v___x_3062_);
v___y_3020_ = v___y_3046_;
v___y_3021_ = v___y_3047_;
v___y_3022_ = v___y_3050_;
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3051_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3054_;
v___y_3027_ = v___y_3053_;
v___y_3028_ = v___x_3058_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___x_3063_;
goto v___jp_3019_;
}
else
{
lean_object* v___x_3064_; 
lean_dec(v___y_3048_);
v___x_3064_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3020_ = v___y_3046_;
v___y_3021_ = v___y_3047_;
v___y_3022_ = v___y_3050_;
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3051_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3054_;
v___y_3027_ = v___y_3053_;
v___y_3028_ = v___x_3058_;
v___y_3029_ = v___y_3055_;
v___y_3030_ = v___x_3064_;
goto v___jp_3019_;
}
}
v___jp_3065_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3080_ = l_Array_append___redArg(v___x_2983_, v___y_3079_);
lean_dec_ref(v___y_3079_);
lean_inc_n(v___y_3078_, 3);
v___x_3081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3078_);
lean_ctor_set(v___x_3081_, 1, v___x_2982_);
lean_ctor_set(v___x_3081_, 2, v___x_3080_);
v___x_3082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___y_3078_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_Syntax_node6(v___y_3078_, v___y_3068_, v___y_3066_, v___y_3077_, v___y_3071_, v___x_3081_, v___x_3083_, v___y_3070_);
v___x_3085_ = l_Lean_Syntax_node4(v___y_3078_, v___y_3074_, v___y_3069_, v___y_3076_, v___y_3072_, v___x_3084_);
v___y_2948_ = v___y_3067_;
v_stx_2949_ = v___x_3085_;
v___y_2950_ = v___y_3073_;
v___y_2951_ = v___y_3075_;
goto v___jp_2947_;
}
v___jp_3086_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = l_Array_append___redArg(v___x_2983_, v___y_3100_);
lean_dec_ref(v___y_3100_);
lean_inc(v___y_3099_);
v___x_3102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3102_, 0, v___y_3099_);
lean_ctor_set(v___x_3102_, 1, v___x_2982_);
lean_ctor_set(v___x_3102_, 2, v___x_3101_);
if (lean_obj_tag(v___y_3092_) == 1)
{
lean_object* v_val_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec(v___x_2889_);
v_val_3103_ = lean_ctor_get(v___y_3092_, 0);
lean_inc(v_val_3103_);
lean_dec_ref_known(v___y_3092_, 1);
v___x_3104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3105_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3104_);
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3099_, 4);
v___x_3107_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___y_3099_);
lean_ctor_set(v___x_3107_, 1, v___x_3106_);
v___x_3108_ = l_Array_append___redArg(v___x_2983_, v_val_3103_);
lean_dec(v_val_3103_);
v___x_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___y_3099_);
lean_ctor_set(v___x_3109_, 1, v___x_2982_);
lean_ctor_set(v___x_3109_, 2, v___x_3108_);
v___x_3110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3099_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Lean_Syntax_node3(v___y_3099_, v___x_3105_, v___x_3107_, v___x_3109_, v___x_3111_);
v___x_3113_ = l_Array_mkArray1___redArg(v___x_3112_);
v___y_3066_ = v___y_3087_;
v___y_3067_ = v___y_3088_;
v___y_3068_ = v___y_3089_;
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v___x_3102_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3095_;
v___y_3075_ = v___y_3096_;
v___y_3076_ = v___y_3097_;
v___y_3077_ = v___y_3098_;
v___y_3078_ = v___y_3099_;
v___y_3079_ = v___x_3113_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3114_; 
lean_dec(v___y_3092_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3114_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_3066_ = v___y_3087_;
v___y_3067_ = v___y_3088_;
v___y_3068_ = v___y_3089_;
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v___x_3102_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3095_;
v___y_3075_ = v___y_3096_;
v___y_3076_ = v___y_3097_;
v___y_3077_ = v___y_3098_;
v___y_3078_ = v___y_3099_;
v___y_3079_ = v___x_3114_;
goto v___jp_3065_;
}
}
v___jp_3115_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = l_Array_append___redArg(v___x_2983_, v___y_3129_);
lean_dec_ref(v___y_3129_);
lean_inc(v___y_3128_);
v___x_3131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3131_, 0, v___y_3128_);
lean_ctor_set(v___x_3131_, 1, v___x_2982_);
lean_ctor_set(v___x_3131_, 2, v___x_3130_);
if (lean_obj_tag(v___y_3117_) == 1)
{
lean_object* v_val_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_val_3132_ = lean_ctor_get(v___y_3117_, 0);
lean_inc(v_val_3132_);
lean_dec_ref_known(v___y_3117_, 1);
v___x_3133_ = l_Lean_SourceInfo_fromRef(v_val_3132_, v___x_2890_);
lean_dec(v_val_3132_);
v___x_3134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = l_Array_mkArray1___redArg(v___x_3135_);
v___y_3087_ = v___y_3116_;
v___y_3088_ = v___y_3118_;
v___y_3089_ = v___y_3119_;
v___y_3090_ = v___y_3120_;
v___y_3091_ = v___y_3121_;
v___y_3092_ = v___y_3122_;
v___y_3093_ = v___y_3123_;
v___y_3094_ = v___y_3124_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3127_;
v___y_3098_ = v___x_3131_;
v___y_3099_ = v___y_3128_;
v___y_3100_ = v___x_3136_;
goto v___jp_3086_;
}
else
{
lean_object* v___x_3137_; 
lean_dec(v___y_3117_);
v___x_3137_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3087_ = v___y_3116_;
v___y_3088_ = v___y_3118_;
v___y_3089_ = v___y_3119_;
v___y_3090_ = v___y_3120_;
v___y_3091_ = v___y_3121_;
v___y_3092_ = v___y_3122_;
v___y_3093_ = v___y_3123_;
v___y_3094_ = v___y_3124_;
v___y_3095_ = v___y_3125_;
v___y_3096_ = v___y_3126_;
v___y_3097_ = v___y_3127_;
v___y_3098_ = v___x_3131_;
v___y_3099_ = v___y_3128_;
v___y_3100_ = v___x_3137_;
goto v___jp_3086_;
}
}
v___jp_3138_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3150_ = l_Array_append___redArg(v___x_2983_, v___y_3149_);
lean_dec_ref(v___y_3149_);
lean_inc_n(v___y_3146_, 2);
v___x_3151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3151_, 0, v___y_3146_);
lean_ctor_set(v___x_3151_, 1, v___x_2982_);
lean_ctor_set(v___x_3151_, 2, v___x_3150_);
v___x_3152_ = l_Lean_Syntax_node5(v___y_3146_, v___x_2891_, v___y_3140_, v___y_3141_, v___y_3143_, v___y_3148_, v___x_3151_);
lean_inc(v___y_3142_);
v___x_3153_ = l_Lean_Syntax_node4(v___y_3146_, v___x_2892_, v___y_3147_, v___y_3142_, v___y_3142_, v___x_3152_);
v___y_2948_ = v___y_3144_;
v_stx_2949_ = v___x_3153_;
v___y_2950_ = v___y_3139_;
v___y_2951_ = v___y_3145_;
goto v___jp_2947_;
}
v___jp_3154_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = l_Array_append___redArg(v___x_2983_, v___y_3165_);
lean_dec_ref(v___y_3165_);
lean_inc(v___y_3163_);
v___x_3167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3167_, 0, v___y_3163_);
lean_ctor_set(v___x_3167_, 1, v___x_2982_);
lean_ctor_set(v___x_3167_, 2, v___x_3166_);
if (lean_obj_tag(v___y_3158_) == 1)
{
lean_object* v_val_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec(v___x_2889_);
v_val_3168_ = lean_ctor_get(v___y_3158_, 0);
lean_inc(v_val_3168_);
lean_dec_ref_known(v___y_3158_, 1);
v___x_3169_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3163_);
v___x_3170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___y_3163_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Array_mkArray2___redArg(v___x_3170_, v_val_3168_);
v___y_3139_ = v___y_3155_;
v___y_3140_ = v___y_3156_;
v___y_3141_ = v___y_3157_;
v___y_3142_ = v___y_3159_;
v___y_3143_ = v___y_3160_;
v___y_3144_ = v___y_3162_;
v___y_3145_ = v___y_3161_;
v___y_3146_ = v___y_3163_;
v___y_3147_ = v___y_3164_;
v___y_3148_ = v___x_3167_;
v___y_3149_ = v___x_3171_;
goto v___jp_3138_;
}
else
{
lean_object* v___x_3172_; 
lean_dec(v___y_3158_);
v___x_3172_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_3139_ = v___y_3155_;
v___y_3140_ = v___y_3156_;
v___y_3141_ = v___y_3157_;
v___y_3142_ = v___y_3159_;
v___y_3143_ = v___y_3160_;
v___y_3144_ = v___y_3162_;
v___y_3145_ = v___y_3161_;
v___y_3146_ = v___y_3163_;
v___y_3147_ = v___y_3164_;
v___y_3148_ = v___x_3167_;
v___y_3149_ = v___x_3172_;
goto v___jp_3138_;
}
}
v___jp_3173_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = l_Array_append___redArg(v___x_2983_, v___y_3184_);
lean_dec_ref(v___y_3184_);
lean_inc(v___y_3181_);
v___x_3186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3186_, 0, v___y_3181_);
lean_ctor_set(v___x_3186_, 1, v___x_2982_);
lean_ctor_set(v___x_3186_, 2, v___x_3185_);
if (lean_obj_tag(v___y_3183_) == 1)
{
lean_object* v_val_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_val_3187_ = lean_ctor_get(v___y_3183_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v___y_3183_, 1);
v___x_3188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3189_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3188_);
v___x_3190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3181_, 4);
v___x_3191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___y_3181_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = l_Array_append___redArg(v___x_2983_, v_val_3187_);
lean_dec(v_val_3187_);
v___x_3193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3193_, 0, v___y_3181_);
lean_ctor_set(v___x_3193_, 1, v___x_2982_);
lean_ctor_set(v___x_3193_, 2, v___x_3192_);
v___x_3194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___y_3181_);
lean_ctor_set(v___x_3195_, 1, v___x_3194_);
v___x_3196_ = l_Lean_Syntax_node3(v___y_3181_, v___x_3189_, v___x_3191_, v___x_3193_, v___x_3195_);
v___x_3197_ = l_Array_mkArray1___redArg(v___x_3196_);
v___y_3155_ = v___y_3174_;
v___y_3156_ = v___y_3175_;
v___y_3157_ = v___y_3176_;
v___y_3158_ = v___y_3178_;
v___y_3159_ = v___y_3177_;
v___y_3160_ = v___x_3186_;
v___y_3161_ = v___y_3180_;
v___y_3162_ = v___y_3179_;
v___y_3163_ = v___y_3181_;
v___y_3164_ = v___y_3182_;
v___y_3165_ = v___x_3197_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3198_; 
lean_dec(v___y_3183_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3198_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3155_ = v___y_3174_;
v___y_3156_ = v___y_3175_;
v___y_3157_ = v___y_3176_;
v___y_3158_ = v___y_3178_;
v___y_3159_ = v___y_3177_;
v___y_3160_ = v___x_3186_;
v___y_3161_ = v___y_3180_;
v___y_3162_ = v___y_3179_;
v___y_3163_ = v___y_3181_;
v___y_3164_ = v___y_3182_;
v___y_3165_ = v___x_3198_;
goto v___jp_3154_;
}
}
v___jp_3199_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = l_Array_append___redArg(v___x_2983_, v___y_3210_);
lean_dec_ref(v___y_3210_);
lean_inc(v___y_3207_);
v___x_3212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3212_, 0, v___y_3207_);
lean_ctor_set(v___x_3212_, 1, v___x_2982_);
lean_ctor_set(v___x_3212_, 2, v___x_3211_);
if (lean_obj_tag(v___y_3202_) == 1)
{
lean_object* v_val_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_val_3213_ = lean_ctor_get(v___y_3202_, 0);
lean_inc(v_val_3213_);
lean_dec_ref_known(v___y_3202_, 1);
v___x_3214_ = l_Lean_SourceInfo_fromRef(v_val_3213_, v___x_2890_);
lean_dec(v_val_3213_);
v___x_3215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = l_Array_mkArray1___redArg(v___x_3216_);
v___y_3174_ = v___y_3200_;
v___y_3175_ = v___y_3201_;
v___y_3176_ = v___x_3212_;
v___y_3177_ = v___y_3204_;
v___y_3178_ = v___y_3203_;
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3205_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3208_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___x_3217_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3218_; 
lean_dec(v___y_3202_);
v___x_3218_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3174_ = v___y_3200_;
v___y_3175_ = v___y_3201_;
v___y_3176_ = v___x_3212_;
v___y_3177_ = v___y_3204_;
v___y_3178_ = v___y_3203_;
v___y_3179_ = v___y_3206_;
v___y_3180_ = v___y_3205_;
v___y_3181_ = v___y_3207_;
v___y_3182_ = v___y_3208_;
v___y_3183_ = v___y_3209_;
v___y_3184_ = v___x_3218_;
goto v___jp_3173_;
}
}
v___jp_3219_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3233_ = l_Array_append___redArg(v___x_2983_, v___y_3232_);
lean_dec_ref(v___y_3232_);
lean_inc_n(v___y_3226_, 3);
v___x_3234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3234_, 0, v___y_3226_);
lean_ctor_set(v___x_3234_, 1, v___x_2982_);
lean_ctor_set(v___x_3234_, 2, v___x_3233_);
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___y_3226_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = l_Lean_Syntax_node6(v___y_3226_, v___y_3229_, v___y_3220_, v___y_3225_, v___y_3231_, v___x_3234_, v___x_3236_, v___y_3228_);
lean_inc(v___y_3224_);
v___x_3238_ = l_Lean_Syntax_node4(v___y_3226_, v___y_3222_, v___y_3221_, v___y_3224_, v___y_3224_, v___x_3237_);
v___y_2948_ = v___y_3223_;
v_stx_2949_ = v___x_3238_;
v___y_2950_ = v___y_3227_;
v___y_2951_ = v___y_3230_;
goto v___jp_2947_;
}
v___jp_3239_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = l_Array_append___redArg(v___x_2983_, v___y_3252_);
lean_dec_ref(v___y_3252_);
lean_inc(v___y_3246_);
v___x_3254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3254_, 0, v___y_3246_);
lean_ctor_set(v___x_3254_, 1, v___x_2982_);
lean_ctor_set(v___x_3254_, 2, v___x_3253_);
if (lean_obj_tag(v___y_3247_) == 1)
{
lean_object* v_val_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v___x_2889_);
v_val_3255_ = lean_ctor_get(v___y_3247_, 0);
lean_inc(v_val_3255_);
lean_dec_ref_known(v___y_3247_, 1);
v___x_3256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3257_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3256_);
v___x_3258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3246_, 4);
v___x_3259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___y_3246_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = l_Array_append___redArg(v___x_2983_, v_val_3255_);
lean_dec(v_val_3255_);
v___x_3261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3261_, 0, v___y_3246_);
lean_ctor_set(v___x_3261_, 1, v___x_2982_);
lean_ctor_set(v___x_3261_, 2, v___x_3260_);
v___x_3262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___y_3246_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = l_Lean_Syntax_node3(v___y_3246_, v___x_3257_, v___x_3259_, v___x_3261_, v___x_3263_);
v___x_3265_ = l_Array_mkArray1___redArg(v___x_3264_);
v___y_3220_ = v___y_3240_;
v___y_3221_ = v___y_3241_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3243_;
v___y_3224_ = v___y_3244_;
v___y_3225_ = v___y_3245_;
v___y_3226_ = v___y_3246_;
v___y_3227_ = v___y_3248_;
v___y_3228_ = v___y_3249_;
v___y_3229_ = v___y_3250_;
v___y_3230_ = v___y_3251_;
v___y_3231_ = v___x_3254_;
v___y_3232_ = v___x_3265_;
goto v___jp_3219_;
}
else
{
lean_object* v___x_3266_; 
lean_dec(v___y_3247_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3266_ = lean_mk_empty_array_with_capacity(v___x_2889_);
lean_dec(v___x_2889_);
v___y_3220_ = v___y_3240_;
v___y_3221_ = v___y_3241_;
v___y_3222_ = v___y_3242_;
v___y_3223_ = v___y_3243_;
v___y_3224_ = v___y_3244_;
v___y_3225_ = v___y_3245_;
v___y_3226_ = v___y_3246_;
v___y_3227_ = v___y_3248_;
v___y_3228_ = v___y_3249_;
v___y_3229_ = v___y_3250_;
v___y_3230_ = v___y_3251_;
v___y_3231_ = v___x_3254_;
v___y_3232_ = v___x_3266_;
goto v___jp_3219_;
}
}
v___jp_3267_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = l_Array_append___redArg(v___x_2983_, v___y_3280_);
lean_dec_ref(v___y_3280_);
lean_inc(v___y_3274_);
v___x_3282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3282_, 0, v___y_3274_);
lean_ctor_set(v___x_3282_, 1, v___x_2982_);
lean_ctor_set(v___x_3282_, 2, v___x_3281_);
if (lean_obj_tag(v___y_3271_) == 1)
{
lean_object* v_val_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_val_3283_ = lean_ctor_get(v___y_3271_, 0);
lean_inc(v_val_3283_);
lean_dec_ref_known(v___y_3271_, 1);
v___x_3284_ = l_Lean_SourceInfo_fromRef(v_val_3283_, v___x_2890_);
lean_dec(v_val_3283_);
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_Array_mkArray1___redArg(v___x_3286_);
v___y_3240_ = v___y_3268_;
v___y_3241_ = v___y_3269_;
v___y_3242_ = v___y_3270_;
v___y_3243_ = v___y_3272_;
v___y_3244_ = v___y_3273_;
v___y_3245_ = v___x_3282_;
v___y_3246_ = v___y_3274_;
v___y_3247_ = v___y_3275_;
v___y_3248_ = v___y_3276_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___x_3287_;
goto v___jp_3239_;
}
else
{
lean_object* v___x_3288_; 
lean_dec(v___y_3271_);
v___x_3288_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3240_ = v___y_3268_;
v___y_3241_ = v___y_3269_;
v___y_3242_ = v___y_3270_;
v___y_3243_ = v___y_3272_;
v___y_3244_ = v___y_3273_;
v___y_3245_ = v___x_3282_;
v___y_3246_ = v___y_3274_;
v___y_3247_ = v___y_3275_;
v___y_3248_ = v___y_3276_;
v___y_3249_ = v___y_3277_;
v___y_3250_ = v___y_3278_;
v___y_3251_ = v___y_3279_;
v___y_3252_ = v___x_3288_;
goto v___jp_3239_;
}
}
v___jp_3289_:
{
if (v___y_3297_ == 0)
{
if (v_useReducible_2893_ == 0)
{
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
if (lean_obj_tag(v___y_3293_) == 0)
{
lean_dec(v___y_3304_);
lean_dec(v___y_3298_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___y_2954_ = v___y_3296_;
v___y_2955_ = v___y_3302_;
v___y_2956_ = v___y_3301_;
v___y_2957_ = v___y_3290_;
v___y_2958_ = v___y_3295_;
v___y_2959_ = v___y_3303_;
v___y_2960_ = v___y_3294_;
v___y_2961_ = v___y_3299_;
v___y_2962_ = v___y_3300_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_3305_; lean_object* v___x_3306_; 
v_val_3305_ = lean_ctor_get(v___y_3293_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v___y_3293_, 1);
lean_inc(v___y_3300_);
lean_inc_ref(v___y_3299_);
v___x_3306_ = lean_apply_9(v___f_2894_, v___y_3302_, v___y_3301_, v___y_3290_, v___y_3295_, v___y_3303_, v___y_3294_, v___y_3299_, v___y_3300_, lean_box(0));
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc_n(v_a_3307_, 3);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2888_, 2);
lean_inc_ref_n(v___x_2887_, 2);
lean_inc_ref_n(v___x_2886_, 2);
v___x_3309_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_a_3307_);
lean_ctor_set(v___x_3310_, 1, v___x_2895_);
v___x_3311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3311_, 0, v_a_3307_);
lean_ctor_set(v___x_3311_, 1, v___x_2982_);
lean_ctor_set(v___x_3311_, 2, v___x_2983_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3313_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3312_);
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3268_ = v___y_3291_;
v___y_3269_ = v___x_3310_;
v___y_3270_ = v___x_3309_;
v___y_3271_ = v___y_3292_;
v___y_3272_ = v___y_3296_;
v___y_3273_ = v___x_3311_;
v___y_3274_ = v_a_3307_;
v___y_3275_ = v___y_3298_;
v___y_3276_ = v___y_3299_;
v___y_3277_ = v_val_3305_;
v___y_3278_ = v___x_3313_;
v___y_3279_ = v___y_3300_;
v___y_3280_ = v___x_3314_;
goto v___jp_3267_;
}
else
{
lean_object* v_val_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_val_3315_ = lean_ctor_get(v___y_3304_, 0);
lean_inc(v_val_3315_);
lean_dec_ref_known(v___y_3304_, 1);
v___x_3316_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3317_ = lean_array_push(v___x_3316_, v_val_3315_);
v___y_3268_ = v___y_3291_;
v___y_3269_ = v___x_3310_;
v___y_3270_ = v___x_3309_;
v___y_3271_ = v___y_3292_;
v___y_3272_ = v___y_3296_;
v___y_3273_ = v___x_3311_;
v___y_3274_ = v_a_3307_;
v___y_3275_ = v___y_3298_;
v___y_3276_ = v___y_3299_;
v___y_3277_ = v_val_3305_;
v___y_3278_ = v___x_3313_;
v___y_3279_ = v___y_3300_;
v___y_3280_ = v___x_3317_;
goto v___jp_3267_;
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_val_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3318_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3306_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3306_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
else
{
lean_object* v___x_3326_; 
lean_inc(v___y_3300_);
lean_inc_ref(v___y_3299_);
v___x_3326_ = lean_apply_9(v___f_2894_, v___y_3302_, v___y_3301_, v___y_3290_, v___y_3295_, v___y_3303_, v___y_3294_, v___y_3299_, v___y_3300_, lean_box(0));
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc_n(v_a_3327_, 3);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3328_, 0, v_a_3327_);
lean_ctor_set(v___x_3328_, 1, v___x_2895_);
v___x_3329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3329_, 0, v_a_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_2982_);
lean_ctor_set(v___x_3329_, 2, v___x_2983_);
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3200_ = v___y_3299_;
v___y_3201_ = v___y_3291_;
v___y_3202_ = v___y_3292_;
v___y_3203_ = v___y_3293_;
v___y_3204_ = v___x_3329_;
v___y_3205_ = v___y_3300_;
v___y_3206_ = v___y_3296_;
v___y_3207_ = v_a_3327_;
v___y_3208_ = v___x_3328_;
v___y_3209_ = v___y_3298_;
v___y_3210_ = v___x_3330_;
goto v___jp_3199_;
}
else
{
lean_object* v_val_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_val_3331_ = lean_ctor_get(v___y_3304_, 0);
lean_inc(v_val_3331_);
lean_dec_ref_known(v___y_3304_, 1);
v___x_3332_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3333_ = lean_array_push(v___x_3332_, v_val_3331_);
v___y_3200_ = v___y_3299_;
v___y_3201_ = v___y_3291_;
v___y_3202_ = v___y_3292_;
v___y_3203_ = v___y_3293_;
v___y_3204_ = v___x_3329_;
v___y_3205_ = v___y_3300_;
v___y_3206_ = v___y_3296_;
v___y_3207_ = v_a_3327_;
v___y_3208_ = v___x_3328_;
v___y_3209_ = v___y_3298_;
v___y_3210_ = v___x_3333_;
goto v___jp_3199_;
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v___y_3304_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3334_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3326_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3326_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
else
{
lean_dec(v___x_2892_);
if (v_useReducible_2893_ == 0)
{
lean_dec(v___x_2891_);
if (lean_obj_tag(v___y_3293_) == 0)
{
lean_dec(v___y_3304_);
lean_dec(v___y_3298_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___y_2954_ = v___y_3296_;
v___y_2955_ = v___y_3302_;
v___y_2956_ = v___y_3301_;
v___y_2957_ = v___y_3290_;
v___y_2958_ = v___y_3295_;
v___y_2959_ = v___y_3303_;
v___y_2960_ = v___y_3294_;
v___y_2961_ = v___y_3299_;
v___y_2962_ = v___y_3300_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_3342_; lean_object* v___x_3343_; 
v_val_3342_ = lean_ctor_get(v___y_3293_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v___y_3293_, 1);
lean_inc(v___y_3300_);
lean_inc_ref(v___y_3299_);
v___x_3343_ = lean_apply_9(v___f_2894_, v___y_3302_, v___y_3301_, v___y_3290_, v___y_3295_, v___y_3303_, v___y_3294_, v___y_3299_, v___y_3300_, lean_box(0));
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc_n(v_a_3344_, 5);
lean_dec_ref_known(v___x_3343_, 1);
v___x_3345_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2888_, 2);
lean_inc_ref_n(v___x_2887_, 2);
lean_inc_ref_n(v___x_2886_, 2);
v___x_3346_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3345_);
v___x_3347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3347_, 0, v_a_3344_);
lean_ctor_set(v___x_3347_, 1, v___x_2895_);
v___x_3348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3348_, 0, v_a_3344_);
lean_ctor_set(v___x_3348_, 1, v___x_2982_);
lean_ctor_set(v___x_3348_, 2, v___x_2983_);
v___x_3349_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3350_, 0, v_a_3344_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = l_Lean_Syntax_node1(v_a_3344_, v___x_2982_, v___x_3350_);
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3353_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3352_);
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3116_ = v___y_3291_;
v___y_3117_ = v___y_3292_;
v___y_3118_ = v___y_3296_;
v___y_3119_ = v___x_3353_;
v___y_3120_ = v___x_3347_;
v___y_3121_ = v_val_3342_;
v___y_3122_ = v___y_3298_;
v___y_3123_ = v___x_3351_;
v___y_3124_ = v___y_3299_;
v___y_3125_ = v___x_3346_;
v___y_3126_ = v___y_3300_;
v___y_3127_ = v___x_3348_;
v___y_3128_ = v_a_3344_;
v___y_3129_ = v___x_3354_;
goto v___jp_3115_;
}
else
{
lean_object* v_val_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_val_3355_ = lean_ctor_get(v___y_3304_, 0);
lean_inc(v_val_3355_);
lean_dec_ref_known(v___y_3304_, 1);
v___x_3356_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3357_ = lean_array_push(v___x_3356_, v_val_3355_);
v___y_3116_ = v___y_3291_;
v___y_3117_ = v___y_3292_;
v___y_3118_ = v___y_3296_;
v___y_3119_ = v___x_3353_;
v___y_3120_ = v___x_3347_;
v___y_3121_ = v_val_3342_;
v___y_3122_ = v___y_3298_;
v___y_3123_ = v___x_3351_;
v___y_3124_ = v___y_3299_;
v___y_3125_ = v___x_3346_;
v___y_3126_ = v___y_3300_;
v___y_3127_ = v___x_3348_;
v___y_3128_ = v_a_3344_;
v___y_3129_ = v___x_3357_;
goto v___jp_3115_;
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v_val_3342_);
lean_dec(v___y_3304_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___x_2895_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3358_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3343_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3343_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
else
{
lean_object* v___x_3366_; 
lean_dec_ref(v___x_2895_);
lean_inc(v___y_3300_);
lean_inc_ref(v___y_3299_);
v___x_3366_ = lean_apply_9(v___f_2894_, v___y_3302_, v___y_3301_, v___y_3290_, v___y_3295_, v___y_3303_, v___y_3294_, v___y_3299_, v___y_3300_, lean_box(0));
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc_n(v_a_3367_, 2);
lean_dec_ref_known(v___x_3366_, 1);
v___x_3368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2888_);
lean_inc_ref(v___x_2887_);
lean_inc_ref(v___x_2886_);
v___x_3369_ = l_Lean_Name_mkStr4(v___x_2886_, v___x_2887_, v___x_2888_, v___x_3368_);
v___x_3370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_a_3367_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3046_ = v___y_3299_;
v___y_3047_ = v___y_3291_;
v___y_3048_ = v___y_3292_;
v___y_3049_ = v___y_3293_;
v___y_3050_ = v___x_3371_;
v___y_3051_ = v_a_3367_;
v___y_3052_ = v___x_3369_;
v___y_3053_ = v___y_3300_;
v___y_3054_ = v___y_3296_;
v___y_3055_ = v___y_3298_;
v___y_3056_ = v___x_3372_;
goto v___jp_3045_;
}
else
{
lean_object* v_val_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_val_3373_ = lean_ctor_get(v___y_3304_, 0);
lean_inc(v_val_3373_);
lean_dec_ref_known(v___y_3304_, 1);
v___x_3374_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3375_ = lean_array_push(v___x_3374_, v_val_3373_);
v___y_3046_ = v___y_3299_;
v___y_3047_ = v___y_3291_;
v___y_3048_ = v___y_3292_;
v___y_3049_ = v___y_3293_;
v___y_3050_ = v___x_3371_;
v___y_3051_ = v_a_3367_;
v___y_3052_ = v___x_3369_;
v___y_3053_ = v___y_3300_;
v___y_3054_ = v___y_3296_;
v___y_3055_ = v___y_3298_;
v___y_3056_ = v___x_3375_;
goto v___jp_3045_;
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v___y_3304_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3376_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3366_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3366_);
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
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
}
v___jp_3384_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3401_ = lean_unsigned_to_nat(5u);
v___x_3402_ = l_Lean_Syntax_getArg(v___y_3389_, v___x_3401_);
lean_dec(v___y_3389_);
v___x_3403_ = l_Lean_Syntax_matchesNull(v___x_3402_, v___x_2889_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec(v_args_3392_);
lean_dec(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3404_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3405_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3404_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___y_2948_ = v___y_3390_;
v_stx_2949_ = v_a_3406_;
v___y_2950_ = v___y_3399_;
v___y_2951_ = v___y_3400_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___y_3390_);
lean_dec(v_tk_2885_);
v_a_3407_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3405_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3405_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_Syntax_getOptional_x3f(v___y_3386_);
lean_dec(v___y_3386_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_box(0);
v___y_3290_ = v___y_3395_;
v___y_3291_ = v___y_3385_;
v___y_3292_ = v___y_3388_;
v___y_3293_ = v___y_3387_;
v___y_3294_ = v___y_3398_;
v___y_3295_ = v___y_3396_;
v___y_3296_ = v___y_3390_;
v___y_3297_ = v___y_3391_;
v___y_3298_ = v_args_3392_;
v___y_3299_ = v___y_3399_;
v___y_3300_ = v___y_3400_;
v___y_3301_ = v___y_3394_;
v___y_3302_ = v___y_3393_;
v___y_3303_ = v___y_3397_;
v___y_3304_ = v___x_3416_;
goto v___jp_3289_;
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_val_3417_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3415_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v___x_3415_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_val_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
v___y_3290_ = v___y_3395_;
v___y_3291_ = v___y_3385_;
v___y_3292_ = v___y_3388_;
v___y_3293_ = v___y_3387_;
v___y_3294_ = v___y_3398_;
v___y_3295_ = v___y_3396_;
v___y_3296_ = v___y_3390_;
v___y_3297_ = v___y_3391_;
v___y_3298_ = v_args_3392_;
v___y_3299_ = v___y_3399_;
v___y_3300_ = v___y_3400_;
v___y_3301_ = v___y_3394_;
v___y_3302_ = v___y_3393_;
v___y_3303_ = v___y_3397_;
v___y_3304_ = v___x_3422_;
goto v___jp_3289_;
}
}
}
}
}
v___jp_3425_:
{
lean_object* v___x_3441_; uint8_t v___x_3442_; 
v___x_3441_ = l_Lean_Syntax_getArg(v___y_3429_, v___x_2896_);
v___x_3442_ = l_Lean_Syntax_isNone(v___x_3441_);
if (v___x_3442_ == 0)
{
uint8_t v___x_3443_; 
lean_inc(v___x_3441_);
v___x_3443_ = l_Lean_Syntax_matchesNull(v___x_3441_, v___x_2897_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec(v___x_3441_);
lean_dec(v_only_3432_);
lean_dec(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3445_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3444_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___y_2948_ = v___y_3430_;
v_stx_2949_ = v_a_3446_;
v___y_2950_ = v___y_3439_;
v___y_2951_ = v___y_3440_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec_ref(v___y_3430_);
lean_dec(v_tk_2885_);
v_a_3447_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3445_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3445_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = l_Lean_Syntax_getArg(v___x_3441_, v___x_2898_);
lean_dec(v___x_2898_);
lean_dec(v___x_3441_);
v___x_3456_ = l_Lean_Syntax_getArgs(v___x_3455_);
lean_dec(v___x_3455_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
v___y_3385_ = v___y_3426_;
v___y_3386_ = v___y_3427_;
v___y_3387_ = v___y_3428_;
v___y_3388_ = v_only_3432_;
v___y_3389_ = v___y_3429_;
v___y_3390_ = v___y_3430_;
v___y_3391_ = v___y_3431_;
v_args_3392_ = v___x_3457_;
v___y_3393_ = v___y_3433_;
v___y_3394_ = v___y_3434_;
v___y_3395_ = v___y_3435_;
v___y_3396_ = v___y_3436_;
v___y_3397_ = v___y_3437_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
goto v___jp_3384_;
}
}
else
{
lean_object* v___x_3458_; 
lean_dec(v___x_3441_);
lean_dec(v___x_2898_);
v___x_3458_ = lean_box(0);
v___y_3385_ = v___y_3426_;
v___y_3386_ = v___y_3427_;
v___y_3387_ = v___y_3428_;
v___y_3388_ = v_only_3432_;
v___y_3389_ = v___y_3429_;
v___y_3390_ = v___y_3430_;
v___y_3391_ = v___y_3431_;
v_args_3392_ = v___x_3458_;
v___y_3393_ = v___y_3433_;
v___y_3394_ = v___y_3434_;
v___y_3395_ = v___y_3435_;
v___y_3396_ = v___y_3436_;
v___y_3397_ = v___y_3437_;
v___y_3398_ = v___y_3438_;
v___y_3399_ = v___y_3439_;
v___y_3400_ = v___y_3440_;
goto v___jp_3384_;
}
}
v___jp_3459_:
{
lean_object* v_usedTheorems_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_usedTheorems_3464_ = lean_ctor_get(v___y_3460_, 0);
v___x_3465_ = l_Lean_Syntax_unsetTrailing(v___y_3462_);
v___x_3466_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3465_, v_usedTheorems_3464_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; uint8_t v___x_3468_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc_n(v_a_3467_, 2);
lean_dec_ref_known(v___x_3466_, 1);
v___x_3468_ = l_Lean_Syntax_isOfKind(v_a_3467_, v___x_2980_);
lean_dec(v___x_2980_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_inc(v_ref_2976_);
lean_dec(v_a_3467_);
lean_dec(v___y_3463_);
lean_dec(v___x_2900_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3469_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3470_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3469_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v___y_2925_ = v___y_3460_;
v_stx_2926_ = v_a_3471_;
v___y_2927_ = v___y_2917_;
v_ref_2928_ = v_ref_2976_;
v___y_2929_ = v___y_2918_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___y_3460_);
lean_dec(v_ref_2976_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v_tk_2885_);
v_a_3472_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3470_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3470_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3480_ = l_Lean_Syntax_getArg(v_a_3467_, v___x_2898_);
lean_inc(v___x_3480_);
v___x_3481_ = l_Lean_Syntax_isOfKind(v___x_3480_, v___x_2899_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_inc(v_ref_2976_);
lean_dec(v___x_3480_);
lean_dec(v_a_3467_);
lean_dec(v___y_3463_);
lean_dec(v___x_2900_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3482_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3483_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3482_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___y_2925_ = v___y_3460_;
v_stx_2926_ = v_a_3484_;
v___y_2927_ = v___y_2917_;
v_ref_2928_ = v_ref_2976_;
v___y_2929_ = v___y_2918_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___y_3460_);
lean_dec(v_ref_2976_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v_tk_2885_);
v_a_3485_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3483_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3483_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3493_ = l_Lean_Syntax_getArg(v_a_3467_, v___x_2900_);
lean_dec(v___x_2900_);
v___x_3494_ = l_Lean_Syntax_getArg(v_a_3467_, v___x_2897_);
v___x_3495_ = l_Lean_Syntax_isNone(v___x_3494_);
if (v___x_3495_ == 0)
{
uint8_t v___x_3496_; 
lean_inc(v___x_3494_);
v___x_3496_ = l_Lean_Syntax_matchesNull(v___x_3494_, v___x_2898_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
lean_inc(v_ref_2976_);
lean_dec(v___x_3494_);
lean_dec(v___x_3493_);
lean_dec(v___x_3480_);
lean_dec(v_a_3467_);
lean_dec(v___y_3463_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
v___x_3497_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3498_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3497_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___y_2925_ = v___y_3460_;
v_stx_2926_ = v_a_3499_;
v___y_2927_ = v___y_2917_;
v_ref_2928_ = v_ref_2976_;
v___y_2929_ = v___y_2918_;
goto v___jp_2924_;
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v___y_3460_);
lean_dec(v_ref_2976_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v_tk_2885_);
v_a_3500_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3498_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = l_Lean_Syntax_getArg(v___x_3494_, v___x_2889_);
lean_dec(v___x_3494_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___y_3426_ = v___x_3480_;
v___y_3427_ = v___x_3493_;
v___y_3428_ = v___y_3463_;
v___y_3429_ = v_a_3467_;
v___y_3430_ = v___y_3460_;
v___y_3431_ = v___y_3461_;
v_only_3432_ = v___x_3509_;
v___y_3433_ = v___y_2911_;
v___y_3434_ = v___y_2912_;
v___y_3435_ = v___y_2913_;
v___y_3436_ = v___y_2914_;
v___y_3437_ = v___y_2915_;
v___y_3438_ = v___y_2916_;
v___y_3439_ = v___y_2917_;
v___y_3440_ = v___y_2918_;
goto v___jp_3425_;
}
}
else
{
lean_object* v___x_3510_; 
lean_dec(v___x_3494_);
v___x_3510_ = lean_box(0);
v___y_3426_ = v___x_3480_;
v___y_3427_ = v___x_3493_;
v___y_3428_ = v___y_3463_;
v___y_3429_ = v_a_3467_;
v___y_3430_ = v___y_3460_;
v___y_3431_ = v___y_3461_;
v_only_3432_ = v___x_3510_;
v___y_3433_ = v___y_2911_;
v___y_3434_ = v___y_2912_;
v___y_3435_ = v___y_2913_;
v___y_3436_ = v___y_2914_;
v___y_3437_ = v___y_2915_;
v___y_3438_ = v___y_2916_;
v___y_3439_ = v___y_2917_;
v___y_3440_ = v___y_2918_;
goto v___jp_3425_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3460_);
lean_dec(v___x_2980_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___x_2900_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3511_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3466_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3466_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
v___jp_3519_:
{
if (lean_obj_tag(v_usingArg_2901_) == 0)
{
v___y_3460_ = v___y_3520_;
v___y_3461_ = v___y_3521_;
v___y_3462_ = v___y_3522_;
v___y_3463_ = v_usingArg_2901_;
goto v___jp_3459_;
}
else
{
lean_object* v_val_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3531_; 
v_val_3523_ = lean_ctor_get(v_usingArg_2901_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_usingArg_2901_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3525_ = v_usingArg_2901_;
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_val_3523_);
lean_dec(v_usingArg_2901_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3527_ = l_Lean_Syntax_unsetTrailing(v_val_3523_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3527_);
v___x_3529_ = v___x_3525_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
v___y_3460_ = v___y_3520_;
v___y_3461_ = v___y_3521_;
v___y_3462_ = v___y_3522_;
v___y_3463_ = v___x_3529_;
goto v___jp_3459_;
}
}
}
}
v___jp_3532_:
{
if (v___y_3536_ == 0)
{
lean_dec(v___y_3535_);
lean_dec(v___x_2980_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v_usingArg_2901_);
lean_dec(v___x_2900_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v___y_2921_ = v___y_3533_;
goto v___jp_2920_;
}
else
{
v___y_3520_ = v___y_3533_;
v___y_3521_ = v___y_3534_;
v___y_3522_ = v___y_3535_;
goto v___jp_3519_;
}
}
v___jp_3537_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___f_3548_; lean_object* v___x_3549_; 
v___x_3543_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3542_, v___x_2977_);
v___x_3544_ = lean_box(v___x_2890_);
v___x_3545_ = lean_box(v___x_2977_);
v___x_3546_ = lean_box(v_useReducible_2893_);
v___x_3547_ = lean_box(v___x_2903_);
lean_inc_ref(v___x_2888_);
lean_inc_ref(v___x_2887_);
lean_inc_ref(v___x_2886_);
lean_inc_ref(v___f_2894_);
lean_inc(v___x_2898_);
lean_inc_ref(v___x_2895_);
lean_inc(v_usingArg_2901_);
lean_inc(v___x_2889_);
lean_inc(v_tk_2885_);
lean_inc(v___x_2900_);
v___f_3548_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3548_, 0, v___x_2900_);
lean_closure_set(v___f_3548_, 1, v_tk_2885_);
lean_closure_set(v___f_3548_, 2, v___x_2982_);
lean_closure_set(v___f_3548_, 3, v___x_2889_);
lean_closure_set(v___f_3548_, 4, v___x_3543_);
lean_closure_set(v___f_3548_, 5, v___y_3538_);
lean_closure_set(v___f_3548_, 6, v___x_3544_);
lean_closure_set(v___f_3548_, 7, v_usingArg_2901_);
lean_closure_set(v___f_3548_, 8, v___x_2895_);
lean_closure_set(v___f_3548_, 9, v___x_3545_);
lean_closure_set(v___f_3548_, 10, v___x_3546_);
lean_closure_set(v___f_3548_, 11, v___x_3547_);
lean_closure_set(v___f_3548_, 12, v___x_2898_);
lean_closure_set(v___f_3548_, 13, v___f_2894_);
lean_closure_set(v___f_3548_, 14, v___x_2886_);
lean_closure_set(v___f_3548_, 15, v___x_2887_);
lean_closure_set(v___f_3548_, 16, v___x_2888_);
lean_closure_set(v___f_3548_, 17, v___f_2904_);
lean_closure_set(v___f_3548_, 18, v_a_2975_);
lean_closure_set(v___f_3548_, 19, v_usingTk_x3f_2905_);
v___x_3549_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3540_, v___f_3548_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_3540_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3551_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2917_);
v___x_3552_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3553_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v___x_3551_, v___x_3552_);
lean_dec_ref(v___x_3551_);
if (v___x_3553_ == 0)
{
if (lean_obj_tag(v_squeeze_2906_) == 0)
{
v___y_3533_ = v_a_3550_;
v___y_3534_ = v___y_3539_;
v___y_3535_ = v___y_3541_;
v___y_3536_ = v___x_3553_;
goto v___jp_3532_;
}
else
{
v___y_3533_ = v_a_3550_;
v___y_3534_ = v___y_3539_;
v___y_3535_ = v___y_3541_;
v___y_3536_ = v___x_2903_;
goto v___jp_3532_;
}
}
else
{
v___y_3520_ = v_a_3550_;
v___y_3521_ = v___y_3539_;
v___y_3522_ = v___y_3541_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v___y_3541_);
lean_dec(v___x_2980_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v_usingArg_2901_);
lean_dec(v___x_2900_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3554_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3549_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3549_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
v___jp_3562_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3566_ = l_Array_append___redArg(v___x_2983_, v___y_3565_);
lean_dec_ref(v___y_3565_);
lean_inc_n(v___x_2978_, 2);
v___x_3567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3567_, 0, v___x_2978_);
lean_ctor_set(v___x_3567_, 1, v___x_2982_);
lean_ctor_set(v___x_3567_, 2, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___x_2978_);
lean_ctor_set(v___x_3568_, 1, v___x_2982_);
lean_ctor_set(v___x_3568_, 2, v___x_2983_);
lean_inc(v___x_2980_);
v___x_3569_ = l_Lean_Syntax_node6(v___x_2978_, v___x_2980_, v___x_2981_, v___x_2902_, v___y_3563_, v___y_3564_, v___x_3567_, v___x_3568_);
v___x_3570_ = 0;
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3572_ = lean_box(v___x_2977_);
v___x_3573_ = lean_box(v___x_3570_);
v___x_3574_ = lean_box(v___x_2977_);
lean_inc(v___x_3569_);
v___x_3575_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3575_, 0, v___x_3569_);
lean_closure_set(v___x_3575_, 1, v___x_3572_);
lean_closure_set(v___x_3575_, 2, v___x_3573_);
lean_closure_set(v___x_3575_, 3, v___x_3574_);
lean_closure_set(v___x_3575_, 4, v___x_3571_);
v___x_3576_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3575_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3576_, 1);
if (lean_obj_tag(v_unfold_2907_) == 0)
{
lean_object* v_ctx_3578_; lean_object* v_simprocs_3579_; lean_object* v_dischargeWrapper_3580_; 
v_ctx_3578_ = lean_ctor_get(v_a_3577_, 0);
lean_inc_ref(v_ctx_3578_);
v_simprocs_3579_ = lean_ctor_get(v_a_3577_, 1);
lean_inc_ref(v_simprocs_3579_);
v_dischargeWrapper_3580_ = lean_ctor_get(v_a_3577_, 2);
lean_inc(v_dischargeWrapper_3580_);
lean_dec(v_a_3577_);
v___y_3538_ = v_simprocs_3579_;
v___y_3539_ = v___x_2977_;
v___y_3540_ = v_dischargeWrapper_3580_;
v___y_3541_ = v___x_3569_;
v___y_3542_ = v_ctx_3578_;
goto v___jp_3537_;
}
else
{
if (v___x_2903_ == 0)
{
lean_object* v_ctx_3581_; lean_object* v_simprocs_3582_; lean_object* v_dischargeWrapper_3583_; 
v_ctx_3581_ = lean_ctor_get(v_a_3577_, 0);
lean_inc_ref(v_ctx_3581_);
v_simprocs_3582_ = lean_ctor_get(v_a_3577_, 1);
lean_inc_ref(v_simprocs_3582_);
v_dischargeWrapper_3583_ = lean_ctor_get(v_a_3577_, 2);
lean_inc(v_dischargeWrapper_3583_);
lean_dec(v_a_3577_);
v___y_3538_ = v_simprocs_3582_;
v___y_3539_ = v___x_2903_;
v___y_3540_ = v_dischargeWrapper_3583_;
v___y_3541_ = v___x_3569_;
v___y_3542_ = v_ctx_3581_;
goto v___jp_3537_;
}
else
{
lean_object* v_ctx_3584_; lean_object* v_simprocs_3585_; lean_object* v_dischargeWrapper_3586_; lean_object* v___x_3587_; 
v_ctx_3584_ = lean_ctor_get(v_a_3577_, 0);
lean_inc_ref(v_ctx_3584_);
v_simprocs_3585_ = lean_ctor_get(v_a_3577_, 1);
lean_inc_ref(v_simprocs_3585_);
v_dischargeWrapper_3586_ = lean_ctor_get(v_a_3577_, 2);
lean_inc(v_dischargeWrapper_3586_);
lean_dec(v_a_3577_);
v___x_3587_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3584_);
v___y_3538_ = v_simprocs_3585_;
v___y_3539_ = v___x_2903_;
v___y_3540_ = v_dischargeWrapper_3586_;
v___y_3541_ = v___x_3569_;
v___y_3542_ = v___x_3587_;
goto v___jp_3537_;
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v___x_3569_);
lean_dec(v___x_2980_);
lean_dec(v_a_2975_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v_usingTk_x3f_2905_);
lean_dec_ref(v___f_2904_);
lean_dec(v_usingArg_2901_);
lean_dec(v___x_2900_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3588_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3576_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3576_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
v___jp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = l_Array_append___redArg(v___x_2983_, v___y_3598_);
lean_dec_ref(v___y_3598_);
lean_inc(v___x_2978_);
v___x_3600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3600_, 0, v___x_2978_);
lean_ctor_set(v___x_3600_, 1, v___x_2982_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
if (lean_obj_tag(v_args_2908_) == 1)
{
lean_object* v_val_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_val_3601_ = lean_ctor_get(v_args_2908_, 0);
v___x_3602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_2978_, 3);
v___x_3603_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_2978_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = l_Array_append___redArg(v___x_2983_, v_val_3601_);
v___x_3605_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3605_, 0, v___x_2978_);
lean_ctor_set(v___x_3605_, 1, v___x_2982_);
lean_ctor_set(v___x_3605_, 2, v___x_3604_);
v___x_3606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_2978_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Array_mkArray3___redArg(v___x_3603_, v___x_3605_, v___x_3607_);
v___y_3563_ = v___y_3597_;
v___y_3564_ = v___x_3600_;
v___y_3565_ = v___x_3608_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3609_; 
v___x_3609_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3563_ = v___y_3597_;
v___y_3564_ = v___x_3600_;
v___y_3565_ = v___x_3609_;
goto v___jp_3562_;
}
}
v___jp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = l_Array_append___redArg(v___x_2983_, v___y_3611_);
lean_dec_ref(v___y_3611_);
lean_inc(v___x_2978_);
v___x_3613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3613_, 0, v___x_2978_);
lean_ctor_set(v___x_3613_, 1, v___x_2982_);
lean_ctor_set(v___x_3613_, 2, v___x_3612_);
if (lean_obj_tag(v_only_2909_) == 1)
{
lean_object* v_val_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_val_3614_ = lean_ctor_get(v_only_2909_, 0);
v___x_3615_ = l_Lean_SourceInfo_fromRef(v_val_3614_, v___x_2890_);
v___x_3616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = l_Array_mkArray1___redArg(v___x_3617_);
v___y_3597_ = v___x_3613_;
v___y_3598_ = v___x_3618_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___y_3597_ = v___x_3613_;
v___y_3598_ = v___x_3619_;
goto v___jp_3596_;
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v_usingTk_x3f_2905_);
lean_dec_ref(v___f_2904_);
lean_dec(v___x_2902_);
lean_dec(v_usingArg_2901_);
lean_dec(v___x_2900_);
lean_dec(v___x_2898_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___f_2894_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2886_);
lean_dec(v_tk_2885_);
v_a_3624_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_2974_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_2974_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
v___jp_2920_:
{
lean_object* v_diag_2922_; lean_object* v___x_2923_; 
v_diag_2922_ = lean_ctor_get(v___y_2921_, 1);
lean_inc_ref(v_diag_2922_);
lean_dec_ref(v___y_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_diag_2922_);
return v___x_2923_;
}
v___jp_2924_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v_stx_2926_);
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
lean_ctor_set(v___x_2933_, 3, v___x_2932_);
lean_ctor_set(v___x_2933_, 4, v___x_2932_);
lean_ctor_set(v___x_2933_, 5, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_ref_2928_);
v___x_2935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0));
v___x_2936_ = 4;
v___x_2937_ = l_Lean_MessageData_nil;
v___x_2938_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2885_, v___x_2933_, v___x_2934_, v___x_2935_, v___x_2932_, v___x_2936_, v___x_2937_, v___y_2927_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2927_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_dec_ref_known(v___x_2938_, 1);
v___y_2921_ = v___y_2925_;
goto v___jp_2920_;
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v___y_2925_);
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2938_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
v___jp_2947_:
{
lean_object* v_ref_2952_; 
v_ref_2952_ = lean_ctor_get(v___y_2950_, 2);
lean_inc(v_ref_2952_);
v___y_2925_ = v___y_2948_;
v_stx_2926_ = v_stx_2949_;
v___y_2927_ = v___y_2950_;
v_ref_2928_ = v_ref_2952_;
v___y_2929_ = v___y_2951_;
goto v___jp_2924_;
}
v___jp_2953_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4);
v___x_2964_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_2963_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
v___y_2948_ = v___y_2954_;
v_stx_2949_ = v_a_2965_;
v___y_2950_ = v___y_2961_;
v___y_2951_ = v___y_2962_;
goto v___jp_2947_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec_ref(v___y_2954_);
lean_dec(v_tk_2885_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object** _args){
lean_object* v_tk_3632_ = _args[0];
lean_object* v___x_3633_ = _args[1];
lean_object* v___x_3634_ = _args[2];
lean_object* v___x_3635_ = _args[3];
lean_object* v___x_3636_ = _args[4];
lean_object* v___x_3637_ = _args[5];
lean_object* v___x_3638_ = _args[6];
lean_object* v___x_3639_ = _args[7];
lean_object* v_useReducible_3640_ = _args[8];
lean_object* v___f_3641_ = _args[9];
lean_object* v___x_3642_ = _args[10];
lean_object* v___x_3643_ = _args[11];
lean_object* v___x_3644_ = _args[12];
lean_object* v___x_3645_ = _args[13];
lean_object* v___x_3646_ = _args[14];
lean_object* v___x_3647_ = _args[15];
lean_object* v_usingArg_3648_ = _args[16];
lean_object* v___x_3649_ = _args[17];
lean_object* v___x_3650_ = _args[18];
lean_object* v___f_3651_ = _args[19];
lean_object* v_usingTk_x3f_3652_ = _args[20];
lean_object* v_squeeze_3653_ = _args[21];
lean_object* v_unfold_3654_ = _args[22];
lean_object* v_args_3655_ = _args[23];
lean_object* v_only_3656_ = _args[24];
lean_object* v___y_3657_ = _args[25];
lean_object* v___y_3658_ = _args[26];
lean_object* v___y_3659_ = _args[27];
lean_object* v___y_3660_ = _args[28];
lean_object* v___y_3661_ = _args[29];
lean_object* v___y_3662_ = _args[30];
lean_object* v___y_3663_ = _args[31];
lean_object* v___y_3664_ = _args[32];
lean_object* v___y_3665_ = _args[33];
lean_object* v___y_3666_ = _args[34];
_start:
{
uint8_t v___x_96970__boxed_3667_; uint8_t v_useReducible_boxed_3668_; uint8_t v___x_96981__boxed_3669_; lean_object* v_res_3670_; 
v___x_96970__boxed_3667_ = lean_unbox(v___x_3637_);
v_useReducible_boxed_3668_ = lean_unbox(v_useReducible_3640_);
v___x_96981__boxed_3669_ = lean_unbox(v___x_3650_);
v_res_3670_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3632_, v___x_3633_, v___x_3634_, v___x_3635_, v___x_3636_, v___x_96970__boxed_3667_, v___x_3638_, v___x_3639_, v_useReducible_boxed_3668_, v___f_3641_, v___x_3642_, v___x_3643_, v___x_3644_, v___x_3645_, v___x_3646_, v___x_3647_, v_usingArg_3648_, v___x_3649_, v___x_96981__boxed_3669_, v___f_3651_, v_usingTk_x3f_3652_, v_squeeze_3653_, v_unfold_3654_, v_args_3655_, v_only_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v_only_3656_);
lean_dec(v_args_3655_);
lean_dec(v_unfold_3654_);
lean_dec(v_squeeze_3653_);
lean_dec(v___x_3646_);
lean_dec(v___x_3644_);
lean_dec(v___x_3643_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3696_, lean_object* v_stx_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_3708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3709_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3697_);
v___x_3712_ = l_Lean_Syntax_isOfKind(v_stx_3697_, v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; 
lean_dec(v_stx_3697_);
v___x_3713_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3713_;
}
else
{
lean_object* v___f_3714_; lean_object* v___x_3715_; lean_object* v_tk_3716_; lean_object* v___x_3717_; lean_object* v___y_3719_; uint8_t v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3751_; uint8_t v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_usingTk_x3f_3771_; lean_object* v_usingArg_3772_; lean_object* v___y_3784_; uint8_t v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v_args_3804_; lean_object* v___y_3816_; uint8_t v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v_only_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v_unfold_3860_; lean_object* v_squeeze_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___f_3714_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3715_ = lean_unsigned_to_nat(0u);
v_tk_3716_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3715_);
v___x_3717_ = lean_unsigned_to_nat(1u);
v___x_3896_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3717_);
v___x_3897_ = l_Lean_Syntax_isNone(v___x_3896_);
if (v___x_3897_ == 0)
{
uint8_t v___x_3898_; 
lean_inc(v___x_3896_);
v___x_3898_ = l_Lean_Syntax_matchesNull(v___x_3896_, v___x_3717_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; 
lean_dec(v___x_3896_);
lean_dec(v_tk_3716_);
lean_dec(v_stx_3697_);
v___x_3899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3899_;
}
else
{
lean_object* v_squeeze_3900_; lean_object* v___x_3901_; 
v_squeeze_3900_ = l_Lean_Syntax_getArg(v___x_3896_, v___x_3715_);
lean_dec(v___x_3896_);
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v_squeeze_3900_);
v_squeeze_3879_ = v___x_3901_;
v___y_3880_ = v_a_3698_;
v___y_3881_ = v_a_3699_;
v___y_3882_ = v_a_3700_;
v___y_3883_ = v_a_3701_;
v___y_3884_ = v_a_3702_;
v___y_3885_ = v_a_3703_;
v___y_3886_ = v_a_3704_;
v___y_3887_ = v_a_3705_;
goto v___jp_3878_;
}
}
else
{
lean_object* v___x_3902_; 
lean_dec(v___x_3896_);
v___x_3902_ = lean_box(0);
v_squeeze_3879_ = v___x_3902_;
v___y_3880_ = v_a_3698_;
v___y_3881_ = v_a_3699_;
v___y_3882_ = v_a_3700_;
v___y_3883_ = v_a_3701_;
v___y_3884_ = v_a_3702_;
v___y_3885_ = v_a_3703_;
v___y_3886_ = v_a_3704_;
v___y_3887_ = v_a_3705_;
goto v___jp_3878_;
}
v___jp_3718_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___f_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___f_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3741_ = lean_box(v___x_3712_);
v___x_3742_ = lean_box(v___y_3720_);
lean_inc(v___y_3731_);
lean_inc(v___y_3725_);
lean_inc(v___y_3740_);
lean_inc(v___y_3724_);
lean_inc(v___y_3735_);
lean_inc(v___y_3732_);
v___f_3743_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 22, 12);
lean_closure_set(v___f_3743_, 0, v___y_3732_);
lean_closure_set(v___f_3743_, 1, v___x_3715_);
lean_closure_set(v___f_3743_, 2, v___y_3735_);
lean_closure_set(v___f_3743_, 3, v___y_3724_);
lean_closure_set(v___f_3743_, 4, v___x_3741_);
lean_closure_set(v___f_3743_, 5, v___x_3707_);
lean_closure_set(v___f_3743_, 6, v___x_3708_);
lean_closure_set(v___f_3743_, 7, v___x_3709_);
lean_closure_set(v___f_3743_, 8, v___y_3740_);
lean_closure_set(v___f_3743_, 9, v___y_3725_);
lean_closure_set(v___f_3743_, 10, v___x_3742_);
lean_closure_set(v___f_3743_, 11, v___y_3731_);
v___x_3744_ = lean_box(v___x_3712_);
v___x_3745_ = lean_box(v_useReducible_3696_);
v___x_3746_ = lean_box(v___y_3720_);
lean_inc(v___y_3729_);
lean_inc(v___y_3739_);
v___f_3747_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3747_, 0, v_tk_3716_);
lean_closure_set(v___f_3747_, 1, v___x_3707_);
lean_closure_set(v___f_3747_, 2, v___x_3708_);
lean_closure_set(v___f_3747_, 3, v___x_3709_);
lean_closure_set(v___f_3747_, 4, v___x_3715_);
lean_closure_set(v___f_3747_, 5, v___x_3744_);
lean_closure_set(v___f_3747_, 6, v___y_3739_);
lean_closure_set(v___f_3747_, 7, v___x_3711_);
lean_closure_set(v___f_3747_, 8, v___x_3745_);
lean_closure_set(v___f_3747_, 9, v___f_3714_);
lean_closure_set(v___f_3747_, 10, v___x_3710_);
lean_closure_set(v___f_3747_, 11, v___y_3721_);
lean_closure_set(v___f_3747_, 12, v___y_3737_);
lean_closure_set(v___f_3747_, 13, v___x_3717_);
lean_closure_set(v___f_3747_, 14, v___y_3729_);
lean_closure_set(v___f_3747_, 15, v___y_3727_);
lean_closure_set(v___f_3747_, 16, v___y_3733_);
lean_closure_set(v___f_3747_, 17, v___y_3732_);
lean_closure_set(v___f_3747_, 18, v___x_3746_);
lean_closure_set(v___f_3747_, 19, v___f_3743_);
lean_closure_set(v___f_3747_, 20, v___y_3726_);
lean_closure_set(v___f_3747_, 21, v___y_3731_);
lean_closure_set(v___f_3747_, 22, v___y_3725_);
lean_closure_set(v___f_3747_, 23, v___y_3735_);
lean_closure_set(v___f_3747_, 24, v___y_3724_);
lean_closure_set(v___f_3747_, 25, v___y_3740_);
v___x_3748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3748_, 0, v___f_3747_);
v___x_3749_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3748_, v___y_3730_, v___y_3722_, v___y_3719_, v___y_3734_, v___y_3728_, v___y_3723_, v___y_3736_, v___y_3738_);
return v___x_3749_;
}
v___jp_3750_:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_Syntax_getOptional_x3f(v___y_3763_);
lean_dec(v___y_3763_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_box(0);
v___y_3719_ = v___y_3751_;
v___y_3720_ = v___y_3752_;
v___y_3721_ = v___y_3753_;
v___y_3722_ = v___y_3754_;
v___y_3723_ = v___y_3755_;
v___y_3724_ = v___y_3756_;
v___y_3725_ = v___y_3757_;
v___y_3726_ = v_usingTk_x3f_3771_;
v___y_3727_ = v___y_3758_;
v___y_3728_ = v___y_3759_;
v___y_3729_ = v___y_3760_;
v___y_3730_ = v___y_3761_;
v___y_3731_ = v___y_3762_;
v___y_3732_ = v___y_3764_;
v___y_3733_ = v_usingArg_3772_;
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3765_;
v___y_3736_ = v___y_3767_;
v___y_3737_ = v___y_3768_;
v___y_3738_ = v___y_3770_;
v___y_3739_ = v___y_3769_;
v___y_3740_ = v___x_3774_;
goto v___jp_3718_;
}
else
{
lean_object* v_val_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v_val_3775_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3773_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_val_3775_);
lean_dec(v___x_3773_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_val_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
v___y_3719_ = v___y_3751_;
v___y_3720_ = v___y_3752_;
v___y_3721_ = v___y_3753_;
v___y_3722_ = v___y_3754_;
v___y_3723_ = v___y_3755_;
v___y_3724_ = v___y_3756_;
v___y_3725_ = v___y_3757_;
v___y_3726_ = v_usingTk_x3f_3771_;
v___y_3727_ = v___y_3758_;
v___y_3728_ = v___y_3759_;
v___y_3729_ = v___y_3760_;
v___y_3730_ = v___y_3761_;
v___y_3731_ = v___y_3762_;
v___y_3732_ = v___y_3764_;
v___y_3733_ = v_usingArg_3772_;
v___y_3734_ = v___y_3766_;
v___y_3735_ = v___y_3765_;
v___y_3736_ = v___y_3767_;
v___y_3737_ = v___y_3768_;
v___y_3738_ = v___y_3770_;
v___y_3739_ = v___y_3769_;
v___y_3740_ = v___x_3780_;
goto v___jp_3718_;
}
}
}
}
v___jp_3783_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = lean_unsigned_to_nat(4u);
v___x_3806_ = l_Lean_Syntax_getArg(v___y_3791_, v___x_3805_);
lean_dec(v___y_3791_);
v___x_3807_ = l_Lean_Syntax_isNone(v___x_3806_);
if (v___x_3807_ == 0)
{
uint8_t v___x_3808_; 
lean_inc(v___x_3806_);
v___x_3808_ = l_Lean_Syntax_matchesNull(v___x_3806_, v___y_3794_);
lean_dec(v___y_3794_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
lean_dec(v___x_3806_);
lean_dec(v_args_3804_);
lean_dec(v___y_3801_);
lean_dec(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec(v_tk_3716_);
v___x_3809_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3809_;
}
else
{
lean_object* v_usingTk_x3f_3810_; lean_object* v_usingArg_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_usingTk_x3f_3810_ = l_Lean_Syntax_getArg(v___x_3806_, v___x_3715_);
v_usingArg_3811_ = l_Lean_Syntax_getArg(v___x_3806_, v___x_3717_);
lean_dec(v___x_3806_);
v___x_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3812_, 0, v_usingTk_x3f_3810_);
v___x_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3813_, 0, v_usingArg_3811_);
v___y_3751_ = v___y_3784_;
v___y_3752_ = v___y_3785_;
v___y_3753_ = v___x_3805_;
v___y_3754_ = v___y_3786_;
v___y_3755_ = v___y_3787_;
v___y_3756_ = v___y_3788_;
v___y_3757_ = v___y_3789_;
v___y_3758_ = v___y_3790_;
v___y_3759_ = v___y_3792_;
v___y_3760_ = v___y_3793_;
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___y_3796_;
v___y_3763_ = v___y_3797_;
v___y_3764_ = v___y_3798_;
v___y_3765_ = v_args_3804_;
v___y_3766_ = v___y_3799_;
v___y_3767_ = v___y_3800_;
v___y_3768_ = v___y_3801_;
v___y_3769_ = v___y_3803_;
v___y_3770_ = v___y_3802_;
v_usingTk_x3f_3771_ = v___x_3812_;
v_usingArg_3772_ = v___x_3813_;
goto v___jp_3750_;
}
}
else
{
lean_object* v___x_3814_; 
lean_dec(v___x_3806_);
lean_dec(v___y_3794_);
v___x_3814_ = lean_box(0);
v___y_3751_ = v___y_3784_;
v___y_3752_ = v___y_3785_;
v___y_3753_ = v___x_3805_;
v___y_3754_ = v___y_3786_;
v___y_3755_ = v___y_3787_;
v___y_3756_ = v___y_3788_;
v___y_3757_ = v___y_3789_;
v___y_3758_ = v___y_3790_;
v___y_3759_ = v___y_3792_;
v___y_3760_ = v___y_3793_;
v___y_3761_ = v___y_3795_;
v___y_3762_ = v___y_3796_;
v___y_3763_ = v___y_3797_;
v___y_3764_ = v___y_3798_;
v___y_3765_ = v_args_3804_;
v___y_3766_ = v___y_3799_;
v___y_3767_ = v___y_3800_;
v___y_3768_ = v___y_3801_;
v___y_3769_ = v___y_3803_;
v___y_3770_ = v___y_3802_;
v_usingTk_x3f_3771_ = v___x_3814_;
v_usingArg_3772_ = v___x_3814_;
goto v___jp_3750_;
}
}
v___jp_3815_:
{
lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3837_ = l_Lean_Syntax_getArg(v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
v___x_3838_ = l_Lean_Syntax_isNone(v___x_3837_);
if (v___x_3838_ == 0)
{
uint8_t v___x_3839_; 
lean_inc(v___x_3837_);
v___x_3839_ = l_Lean_Syntax_matchesNull(v___x_3837_, v___x_3717_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_dec(v___x_3837_);
lean_dec(v_only_3828_);
lean_dec(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec(v___y_3821_);
lean_dec(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec(v___y_3816_);
lean_dec(v_tk_3716_);
v___x_3840_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; 
v___x_3841_ = l_Lean_Syntax_getArg(v___x_3837_, v___x_3715_);
lean_dec(v___x_3837_);
v___x_3842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3841_);
v___x_3843_ = l_Lean_Syntax_isOfKind(v___x_3841_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3844_; 
lean_dec(v___x_3841_);
lean_dec(v_only_3828_);
lean_dec(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec(v___y_3821_);
lean_dec(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec(v___y_3816_);
lean_dec(v_tk_3716_);
v___x_3844_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3844_;
}
else
{
lean_object* v___x_3845_; lean_object* v_args_3846_; lean_object* v___x_3847_; 
v___x_3845_ = l_Lean_Syntax_getArg(v___x_3841_, v___x_3717_);
lean_dec(v___x_3841_);
v_args_3846_ = l_Lean_Syntax_getArgs(v___x_3845_);
lean_dec(v___x_3845_);
v___x_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_args_3846_);
v___y_3784_ = v___y_3831_;
v___y_3785_ = v___y_3817_;
v___y_3786_ = v___y_3830_;
v___y_3787_ = v___y_3834_;
v___y_3788_ = v_only_3828_;
v___y_3789_ = v___y_3818_;
v___y_3790_ = v___y_3819_;
v___y_3791_ = v___y_3826_;
v___y_3792_ = v___y_3833_;
v___y_3793_ = v___y_3820_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v___y_3829_;
v___y_3796_ = v___y_3823_;
v___y_3797_ = v___y_3824_;
v___y_3798_ = v___y_3816_;
v___y_3799_ = v___y_3832_;
v___y_3800_ = v___y_3835_;
v___y_3801_ = v___y_3821_;
v___y_3802_ = v___y_3836_;
v___y_3803_ = v___y_3822_;
v_args_3804_ = v___x_3847_;
goto v___jp_3783_;
}
}
}
else
{
lean_object* v___x_3848_; 
lean_dec(v___x_3837_);
v___x_3848_ = lean_box(0);
v___y_3784_ = v___y_3831_;
v___y_3785_ = v___y_3817_;
v___y_3786_ = v___y_3830_;
v___y_3787_ = v___y_3834_;
v___y_3788_ = v_only_3828_;
v___y_3789_ = v___y_3818_;
v___y_3790_ = v___y_3819_;
v___y_3791_ = v___y_3826_;
v___y_3792_ = v___y_3833_;
v___y_3793_ = v___y_3820_;
v___y_3794_ = v___y_3825_;
v___y_3795_ = v___y_3829_;
v___y_3796_ = v___y_3823_;
v___y_3797_ = v___y_3824_;
v___y_3798_ = v___y_3816_;
v___y_3799_ = v___y_3832_;
v___y_3800_ = v___y_3835_;
v___y_3801_ = v___y_3821_;
v___y_3802_ = v___y_3836_;
v___y_3803_ = v___y_3822_;
v_args_3804_ = v___x_3848_;
goto v___jp_3783_;
}
}
v___jp_3849_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3861_ = lean_unsigned_to_nat(3u);
v___x_3862_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3861_);
lean_dec(v_stx_3697_);
v___x_3863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3862_);
v___x_3864_ = l_Lean_Syntax_isOfKind(v___x_3862_, v___x_3863_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; 
lean_dec(v___x_3862_);
lean_dec(v_unfold_3860_);
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v_tk_3716_);
v___x_3865_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3865_;
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3866_ = l_Lean_Syntax_getArg(v___x_3862_, v___x_3715_);
v___x_3867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3866_);
v___x_3868_ = l_Lean_Syntax_isOfKind(v___x_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
lean_dec(v___x_3866_);
lean_dec(v___x_3862_);
lean_dec(v_unfold_3860_);
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v_tk_3716_);
v___x_3869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3869_;
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3870_ = l_Lean_Syntax_getArg(v___x_3862_, v___x_3717_);
v___x_3871_ = l_Lean_Syntax_getArg(v___x_3862_, v___y_3858_);
v___x_3872_ = l_Lean_Syntax_isNone(v___x_3871_);
if (v___x_3872_ == 0)
{
uint8_t v___x_3873_; 
lean_inc(v___x_3871_);
v___x_3873_ = l_Lean_Syntax_matchesNull(v___x_3871_, v___x_3717_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; 
lean_dec(v___x_3871_);
lean_dec(v___x_3870_);
lean_dec(v___x_3866_);
lean_dec(v___x_3862_);
lean_dec(v_unfold_3860_);
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v_tk_3716_);
v___x_3874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3874_;
}
else
{
lean_object* v_only_3875_; lean_object* v___x_3876_; 
v_only_3875_ = l_Lean_Syntax_getArg(v___x_3871_, v___x_3715_);
lean_dec(v___x_3871_);
v___x_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3876_, 0, v_only_3875_);
lean_inc(v___y_3858_);
v___y_3816_ = v___x_3866_;
v___y_3817_ = v___x_3864_;
v___y_3818_ = v_unfold_3860_;
v___y_3819_ = v___y_3858_;
v___y_3820_ = v___x_3867_;
v___y_3821_ = v___x_3861_;
v___y_3822_ = v___x_3863_;
v___y_3823_ = v___y_3859_;
v___y_3824_ = v___x_3870_;
v___y_3825_ = v___y_3858_;
v___y_3826_ = v___x_3862_;
v___y_3827_ = v___x_3861_;
v_only_3828_ = v___x_3876_;
v___y_3829_ = v___y_3851_;
v___y_3830_ = v___y_3856_;
v___y_3831_ = v___y_3855_;
v___y_3832_ = v___y_3854_;
v___y_3833_ = v___y_3850_;
v___y_3834_ = v___y_3853_;
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3852_;
goto v___jp_3815_;
}
}
else
{
lean_object* v___x_3877_; 
lean_dec(v___x_3871_);
v___x_3877_ = lean_box(0);
lean_inc(v___y_3858_);
v___y_3816_ = v___x_3866_;
v___y_3817_ = v___x_3864_;
v___y_3818_ = v_unfold_3860_;
v___y_3819_ = v___y_3858_;
v___y_3820_ = v___x_3867_;
v___y_3821_ = v___x_3861_;
v___y_3822_ = v___x_3863_;
v___y_3823_ = v___y_3859_;
v___y_3824_ = v___x_3870_;
v___y_3825_ = v___y_3858_;
v___y_3826_ = v___x_3862_;
v___y_3827_ = v___x_3861_;
v_only_3828_ = v___x_3877_;
v___y_3829_ = v___y_3851_;
v___y_3830_ = v___y_3856_;
v___y_3831_ = v___y_3855_;
v___y_3832_ = v___y_3854_;
v___y_3833_ = v___y_3850_;
v___y_3834_ = v___y_3853_;
v___y_3835_ = v___y_3857_;
v___y_3836_ = v___y_3852_;
goto v___jp_3815_;
}
}
}
}
v___jp_3878_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; 
v___x_3888_ = lean_unsigned_to_nat(2u);
v___x_3889_ = l_Lean_Syntax_getArg(v_stx_3697_, v___x_3888_);
v___x_3890_ = l_Lean_Syntax_isNone(v___x_3889_);
if (v___x_3890_ == 0)
{
uint8_t v___x_3891_; 
lean_inc(v___x_3889_);
v___x_3891_ = l_Lean_Syntax_matchesNull(v___x_3889_, v___x_3717_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; 
lean_dec(v___x_3889_);
lean_dec(v_squeeze_3879_);
lean_dec(v_tk_3716_);
lean_dec(v_stx_3697_);
v___x_3892_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3892_;
}
else
{
lean_object* v_unfold_3893_; lean_object* v___x_3894_; 
v_unfold_3893_ = l_Lean_Syntax_getArg(v___x_3889_, v___x_3715_);
lean_dec(v___x_3889_);
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_unfold_3893_);
v___y_3850_ = v___y_3884_;
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3887_;
v___y_3853_ = v___y_3885_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3882_;
v___y_3856_ = v___y_3881_;
v___y_3857_ = v___y_3886_;
v___y_3858_ = v___x_3888_;
v___y_3859_ = v_squeeze_3879_;
v_unfold_3860_ = v___x_3894_;
goto v___jp_3849_;
}
}
else
{
lean_object* v___x_3895_; 
lean_dec(v___x_3889_);
v___x_3895_ = lean_box(0);
v___y_3850_ = v___y_3884_;
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3887_;
v___y_3853_ = v___y_3885_;
v___y_3854_ = v___y_3883_;
v___y_3855_ = v___y_3882_;
v___y_3856_ = v___y_3881_;
v___y_3857_ = v___y_3886_;
v___y_3858_ = v___x_3888_;
v___y_3859_ = v_squeeze_3879_;
v_unfold_3860_ = v___x_3895_;
goto v___jp_3849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3903_, lean_object* v_stx_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
uint8_t v_useReducible_boxed_3914_; lean_object* v_res_3915_; 
v_useReducible_boxed_3914_ = lean_unbox(v_useReducible_3903_);
v_res_3915_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3914_, v_stx_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_3916_, lean_object* v_val_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___redArg(v_mvarId_3916_, v_val_3917_, v___y_3923_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_3928_, lean_object* v_val_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_3928_, v_val_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_o_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_o_3940_, v___y_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___boxed(lean_object* v_o_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(v_o_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_3962_, lean_object* v_msg_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_3963_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_3974_, lean_object* v_msg_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_3974_, v_msg_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v_00_u03b1_3986_, lean_object* v_x_3987_, lean_object* v_mkInfoTree_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_3987_, v_mkInfoTree_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v_00_u03b1_3999_, lean_object* v_x_4000_, lean_object* v_mkInfoTree_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v_00_u03b1_3999_, v_x_4000_, v_mkInfoTree_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_00_u03b2_4012_, lean_object* v_x_4013_, lean_object* v_x_4014_, lean_object* v_x_4015_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___redArg(v_x_4013_, v_x_4014_, v_x_4015_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_4017_, lean_object* v_x_4018_, size_t v_x_4019_, size_t v_x_4020_, lean_object* v_x_4021_, lean_object* v_x_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_x_4018_, v_x_4019_, v_x_4020_, v_x_4021_, v_x_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_4024_, lean_object* v_x_4025_, lean_object* v_x_4026_, lean_object* v_x_4027_, lean_object* v_x_4028_, lean_object* v_x_4029_){
_start:
{
size_t v_x_99134__boxed_4030_; size_t v_x_99135__boxed_4031_; lean_object* v_res_4032_; 
v_x_99134__boxed_4030_ = lean_unbox_usize(v_x_4026_);
lean_dec(v_x_4026_);
v_x_99135__boxed_4031_ = lean_unbox_usize(v_x_4027_);
lean_dec(v_x_4027_);
v_res_4032_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_4024_, v_x_4025_, v_x_99134__boxed_4030_, v_x_99135__boxed_4031_, v_x_4028_, v_x_4029_);
return v_res_4032_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_4033_, lean_object* v_m_4034_, lean_object* v_a_4035_){
_start:
{
uint8_t v___x_4036_; 
v___x_4036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___redArg(v_m_4034_, v_a_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10___boxed(lean_object* v_00_u03b2_4037_, lean_object* v_m_4038_, lean_object* v_a_4039_){
_start:
{
uint8_t v_res_4040_; lean_object* v_r_4041_; 
v_res_4040_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10(v_00_u03b2_4037_, v_m_4038_, v_a_4039_);
lean_dec_ref(v_a_4039_);
lean_dec_ref(v_m_4038_);
v_r_4041_ = lean_box(v_res_4040_);
return v_r_4041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_4042_, lean_object* v_m_4043_, lean_object* v_a_4044_, lean_object* v_b_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11___redArg(v_m_4043_, v_a_4044_, v_b_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(lean_object* v_mvarId_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___redArg(v_mvarId_4047_, v___y_4048_, v___y_4054_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19___boxed(lean_object* v_mvarId_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__19(v_mvarId_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v_mvarId_4059_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(lean_object* v_mvarId_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___redArg(v_mvarId_4071_, v___y_4072_, v___y_4078_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20___boxed(lean_object* v_mvarId_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__12_spec__20(v_mvarId_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v_mvarId_4083_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4095_, lean_object* v_n_4096_, lean_object* v_k_4097_, lean_object* v_v_4098_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_n_4096_, v_k_4097_, v_v_4098_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_4100_, size_t v_depth_4101_, lean_object* v_keys_4102_, lean_object* v_vals_4103_, lean_object* v_heq_4104_, lean_object* v_i_4105_, lean_object* v_entries_4106_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___redArg(v_depth_4101_, v_keys_4102_, v_vals_4103_, v_i_4105_, v_entries_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_4108_, lean_object* v_depth_4109_, lean_object* v_keys_4110_, lean_object* v_vals_4111_, lean_object* v_heq_4112_, lean_object* v_i_4113_, lean_object* v_entries_4114_){
_start:
{
size_t v_depth_boxed_4115_; lean_object* v_res_4116_; 
v_depth_boxed_4115_ = lean_unbox_usize(v_depth_4109_);
lean_dec(v_depth_4109_);
v_res_4116_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__12(v_00_u03b2_4108_, v_depth_boxed_4115_, v_keys_4110_, v_vals_4111_, v_heq_4112_, v_i_4113_, v_entries_4114_);
lean_dec_ref(v_vals_4111_);
lean_dec_ref(v_keys_4110_);
return v_res_4116_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(lean_object* v_00_u03b2_4117_, lean_object* v_a_4118_, lean_object* v_x_4119_){
_start:
{
uint8_t v___x_4120_; 
v___x_4120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___redArg(v_a_4118_, v_x_4119_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15___boxed(lean_object* v_00_u03b2_4121_, lean_object* v_a_4122_, lean_object* v_x_4123_){
_start:
{
uint8_t v_res_4124_; lean_object* v_r_4125_; 
v_res_4124_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__10_spec__15(v_00_u03b2_4121_, v_a_4122_, v_x_4123_);
lean_dec(v_x_4123_);
lean_dec_ref(v_a_4122_);
v_r_4125_ = lean_box(v_res_4124_);
return v_r_4125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17(lean_object* v_00_u03b2_4126_, lean_object* v_data_4127_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17___redArg(v_data_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_4129_, lean_object* v_x_4130_, lean_object* v_x_4131_, lean_object* v_x_4132_, lean_object* v_x_4133_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11_spec__13___redArg(v_x_4130_, v_x_4131_, v_x_4132_, v_x_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19(lean_object* v_00_u03b2_4135_, lean_object* v_i_4136_, lean_object* v_source_4137_, lean_object* v_target_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19___redArg(v_i_4136_, v_source_4137_, v_target_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23(lean_object* v_00_u03b2_4140_, lean_object* v_x_4141_, lean_object* v_x_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__6_spec__11_spec__17_spec__19_spec__23___redArg(v_x_4141_, v_x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
uint8_t v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = 1;
v___x_4155_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_4154_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4176_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4179_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_4180_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4176_, v___x_4177_, v___x_4178_, v___x_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_4211_ = l_Lean_addBuiltinDeclarationRanges(v___x_4209_, v___x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_4218_);
lean_dec(v_x_4218_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; uint8_t v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_4231_);
v___x_4273_ = l_Lean_Syntax_isOfKind(v_stx_4231_, v___x_4272_);
if (v___x_4273_ == 0)
{
lean_object* v___x_4274_; 
lean_dec(v_stx_4231_);
v___x_4274_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4274_;
}
else
{
lean_object* v___x_4275_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; uint8_t v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; uint8_t v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; uint8_t v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; uint8_t v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v_tk_4402_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v_args_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; lean_object* v___x_4462_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v_only_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v_unfold_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v_squeeze_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v___x_4275_ = lean_unsigned_to_nat(0u);
v_tk_4402_ = l_Lean_Syntax_getArg(v_stx_4231_, v___x_4275_);
v___x_4462_ = lean_unsigned_to_nat(1u);
v___x_4538_ = l_Lean_Syntax_getArg(v_stx_4231_, v___x_4462_);
v___x_4539_ = l_Lean_Syntax_isNone(v___x_4538_);
if (v___x_4539_ == 0)
{
uint8_t v___x_4540_; 
lean_inc(v___x_4538_);
v___x_4540_ = l_Lean_Syntax_matchesNull(v___x_4538_, v___x_4462_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
lean_dec(v___x_4538_);
lean_dec(v_tk_4402_);
lean_dec(v_stx_4231_);
v___x_4541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4541_;
}
else
{
lean_object* v_squeeze_4542_; lean_object* v___x_4543_; 
v_squeeze_4542_ = l_Lean_Syntax_getArg(v___x_4538_, v___x_4275_);
lean_dec(v___x_4538_);
v___x_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_squeeze_4542_);
v_squeeze_4521_ = v___x_4543_;
v___y_4522_ = v_a_4232_;
v___y_4523_ = v_a_4233_;
v___y_4524_ = v_a_4234_;
v___y_4525_ = v_a_4235_;
v___y_4526_ = v_a_4236_;
v___y_4527_ = v_a_4237_;
v___y_4528_ = v_a_4238_;
v___y_4529_ = v_a_4239_;
goto v___jp_4520_;
}
}
else
{
lean_object* v___x_4544_; 
lean_dec(v___x_4538_);
v___x_4544_ = lean_box(0);
v_squeeze_4521_ = v___x_4544_;
v___y_4522_ = v_a_4232_;
v___y_4523_ = v_a_4233_;
v___y_4524_ = v_a_4234_;
v___y_4525_ = v_a_4235_;
v___y_4526_ = v_a_4236_;
v___y_4527_ = v_a_4237_;
v___y_4528_ = v_a_4238_;
v___y_4529_ = v_a_4239_;
goto v___jp_4520_;
}
v___jp_4276_:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
lean_inc_ref(v___y_4293_);
v___x_4299_ = l_Array_append___redArg(v___y_4293_, v___y_4298_);
lean_dec_ref(v___y_4298_);
lean_inc(v___y_4282_);
lean_inc(v___y_4279_);
v___x_4300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4300_, 0, v___y_4279_);
lean_ctor_set(v___x_4300_, 1, v___y_4282_);
lean_ctor_set(v___x_4300_, 2, v___x_4299_);
if (lean_obj_tag(v___y_4281_) == 1)
{
lean_object* v_val_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v_val_4301_ = lean_ctor_get(v___y_4281_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v___y_4281_, 1);
v___x_4302_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_4279_, 4);
v___x_4304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___y_4279_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
lean_inc_ref(v___y_4293_);
v___x_4305_ = l_Array_append___redArg(v___y_4293_, v_val_4301_);
lean_dec(v_val_4301_);
lean_inc(v___y_4282_);
v___x_4306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4306_, 0, v___y_4279_);
lean_ctor_set(v___x_4306_, 1, v___y_4282_);
lean_ctor_set(v___x_4306_, 2, v___x_4305_);
v___x_4307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_4308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___y_4279_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = l_Lean_Syntax_node3(v___y_4279_, v___x_4302_, v___x_4304_, v___x_4306_, v___x_4308_);
v___x_4310_ = l_Array_mkArray1___redArg(v___x_4309_);
v___y_4242_ = v___y_4277_;
v___y_4243_ = v___y_4278_;
v___y_4244_ = v___y_4280_;
v___y_4245_ = v___y_4279_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___y_4284_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4289_;
v___y_4253_ = v___y_4288_;
v___y_4254_ = v___y_4291_;
v___y_4255_ = v___y_4290_;
v___y_4256_ = v___y_4292_;
v___y_4257_ = v___y_4293_;
v___y_4258_ = v___x_4300_;
v___y_4259_ = v___y_4294_;
v___y_4260_ = v___y_4295_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v___y_4297_;
v___y_4263_ = v___x_4310_;
goto v___jp_4241_;
}
else
{
lean_object* v___x_4311_; 
lean_dec(v___y_4281_);
v___x_4311_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4242_ = v___y_4277_;
v___y_4243_ = v___y_4278_;
v___y_4244_ = v___y_4280_;
v___y_4245_ = v___y_4279_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___y_4284_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4289_;
v___y_4253_ = v___y_4288_;
v___y_4254_ = v___y_4291_;
v___y_4255_ = v___y_4290_;
v___y_4256_ = v___y_4292_;
v___y_4257_ = v___y_4293_;
v___y_4258_ = v___x_4300_;
v___y_4259_ = v___y_4294_;
v___y_4260_ = v___y_4295_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v___y_4297_;
v___y_4263_ = v___x_4311_;
goto v___jp_4241_;
}
}
v___jp_4312_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
lean_inc_ref(v___y_4329_);
v___x_4335_ = l_Array_append___redArg(v___y_4329_, v___y_4334_);
lean_dec_ref(v___y_4334_);
lean_inc(v___y_4317_);
lean_inc(v___y_4315_);
v___x_4336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4336_, 0, v___y_4315_);
lean_ctor_set(v___x_4336_, 1, v___y_4317_);
lean_ctor_set(v___x_4336_, 2, v___x_4335_);
if (lean_obj_tag(v___y_4324_) == 1)
{
lean_object* v_val_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v_val_4337_ = lean_ctor_get(v___y_4324_, 0);
lean_inc(v_val_4337_);
lean_dec_ref_known(v___y_4324_, 1);
v___x_4338_ = l_Lean_SourceInfo_fromRef(v_val_4337_, v___x_4273_);
lean_dec(v_val_4337_);
v___x_4339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4338_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = l_Array_mkArray1___redArg(v___x_4340_);
v___y_4277_ = v___y_4313_;
v___y_4278_ = v___y_4314_;
v___y_4279_ = v___y_4315_;
v___y_4280_ = v___y_4316_;
v___y_4281_ = v___y_4318_;
v___y_4282_ = v___y_4317_;
v___y_4283_ = v___y_4319_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___x_4336_;
v___y_4289_ = v___y_4325_;
v___y_4290_ = v___y_4327_;
v___y_4291_ = v___y_4326_;
v___y_4292_ = v___y_4328_;
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4331_;
v___y_4296_ = v___y_4332_;
v___y_4297_ = v___y_4333_;
v___y_4298_ = v___x_4341_;
goto v___jp_4276_;
}
else
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4324_);
lean_dec(v___y_4324_);
v___y_4277_ = v___y_4313_;
v___y_4278_ = v___y_4314_;
v___y_4279_ = v___y_4315_;
v___y_4280_ = v___y_4316_;
v___y_4281_ = v___y_4318_;
v___y_4282_ = v___y_4317_;
v___y_4283_ = v___y_4319_;
v___y_4284_ = v___y_4320_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___y_4322_;
v___y_4287_ = v___y_4323_;
v___y_4288_ = v___x_4336_;
v___y_4289_ = v___y_4325_;
v___y_4290_ = v___y_4327_;
v___y_4291_ = v___y_4326_;
v___y_4292_ = v___y_4328_;
v___y_4293_ = v___y_4329_;
v___y_4294_ = v___y_4330_;
v___y_4295_ = v___y_4331_;
v___y_4296_ = v___y_4332_;
v___y_4297_ = v___y_4333_;
v___y_4298_ = v___x_4342_;
goto v___jp_4276_;
}
}
v___jp_4343_:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
lean_inc_ref(v___y_4359_);
v___x_4365_ = l_Array_append___redArg(v___y_4359_, v___y_4364_);
lean_dec_ref(v___y_4364_);
lean_inc(v___y_4348_);
lean_inc(v___y_4346_);
v___x_4366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4366_, 0, v___y_4346_);
lean_ctor_set(v___x_4366_, 1, v___y_4348_);
lean_ctor_set(v___x_4366_, 2, v___x_4365_);
v___x_4367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4363_) == 0)
{
lean_object* v___x_4368_; 
v___x_4368_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4313_ = v___y_4344_;
v___y_4314_ = v___y_4345_;
v___y_4315_ = v___y_4346_;
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4348_;
v___y_4318_ = v___y_4349_;
v___y_4319_ = v___y_4350_;
v___y_4320_ = v___y_4351_;
v___y_4321_ = v___y_4352_;
v___y_4322_ = v___y_4353_;
v___y_4323_ = v___x_4366_;
v___y_4324_ = v___y_4355_;
v___y_4325_ = v___y_4354_;
v___y_4326_ = v___y_4357_;
v___y_4327_ = v___y_4356_;
v___y_4328_ = v___y_4358_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4360_;
v___y_4331_ = v___y_4361_;
v___y_4332_ = v___y_4362_;
v___y_4333_ = v___x_4367_;
v___y_4334_ = v___x_4368_;
goto v___jp_4312_;
}
else
{
lean_object* v_val_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_val_4369_ = lean_ctor_get(v___y_4363_, 0);
lean_inc(v_val_4369_);
lean_dec_ref_known(v___y_4363_, 1);
v___x_4370_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4371_ = lean_array_push(v___x_4370_, v_val_4369_);
v___y_4313_ = v___y_4344_;
v___y_4314_ = v___y_4345_;
v___y_4315_ = v___y_4346_;
v___y_4316_ = v___y_4347_;
v___y_4317_ = v___y_4348_;
v___y_4318_ = v___y_4349_;
v___y_4319_ = v___y_4350_;
v___y_4320_ = v___y_4351_;
v___y_4321_ = v___y_4352_;
v___y_4322_ = v___y_4353_;
v___y_4323_ = v___x_4366_;
v___y_4324_ = v___y_4355_;
v___y_4325_ = v___y_4354_;
v___y_4326_ = v___y_4357_;
v___y_4327_ = v___y_4356_;
v___y_4328_ = v___y_4358_;
v___y_4329_ = v___y_4359_;
v___y_4330_ = v___y_4360_;
v___y_4331_ = v___y_4361_;
v___y_4332_ = v___y_4362_;
v___y_4333_ = v___x_4367_;
v___y_4334_ = v___x_4371_;
goto v___jp_4312_;
}
}
v___jp_4372_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_inc_ref(v___y_4388_);
v___x_4394_ = l_Array_append___redArg(v___y_4388_, v___y_4393_);
lean_dec_ref(v___y_4393_);
lean_inc(v___y_4377_);
lean_inc(v___y_4375_);
v___x_4395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4395_, 0, v___y_4375_);
lean_ctor_set(v___x_4395_, 1, v___y_4377_);
lean_ctor_set(v___x_4395_, 2, v___x_4394_);
if (lean_obj_tag(v___y_4384_) == 1)
{
lean_object* v_val_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_val_4396_ = lean_ctor_get(v___y_4384_, 0);
lean_inc(v_val_4396_);
lean_dec_ref_known(v___y_4384_, 1);
v___x_4397_ = l_Lean_SourceInfo_fromRef(v_val_4396_, v___x_4273_);
lean_dec(v_val_4396_);
v___x_4398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_4399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4397_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = l_Array_mkArray1___redArg(v___x_4399_);
v___y_4344_ = v___y_4373_;
v___y_4345_ = v___y_4374_;
v___y_4346_ = v___y_4375_;
v___y_4347_ = v___y_4376_;
v___y_4348_ = v___y_4377_;
v___y_4349_ = v___y_4378_;
v___y_4350_ = v___x_4395_;
v___y_4351_ = v___y_4379_;
v___y_4352_ = v___y_4380_;
v___y_4353_ = v___y_4381_;
v___y_4354_ = v___y_4382_;
v___y_4355_ = v___y_4383_;
v___y_4356_ = v___y_4386_;
v___y_4357_ = v___y_4385_;
v___y_4358_ = v___y_4387_;
v___y_4359_ = v___y_4388_;
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4390_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4392_;
v___y_4364_ = v___x_4400_;
goto v___jp_4343_;
}
else
{
lean_object* v___x_4401_; 
v___x_4401_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4384_);
lean_dec(v___y_4384_);
v___y_4344_ = v___y_4373_;
v___y_4345_ = v___y_4374_;
v___y_4346_ = v___y_4375_;
v___y_4347_ = v___y_4376_;
v___y_4348_ = v___y_4377_;
v___y_4349_ = v___y_4378_;
v___y_4350_ = v___x_4395_;
v___y_4351_ = v___y_4379_;
v___y_4352_ = v___y_4380_;
v___y_4353_ = v___y_4381_;
v___y_4354_ = v___y_4382_;
v___y_4355_ = v___y_4383_;
v___y_4356_ = v___y_4386_;
v___y_4357_ = v___y_4385_;
v___y_4358_ = v___y_4387_;
v___y_4359_ = v___y_4388_;
v___y_4360_ = v___y_4389_;
v___y_4361_ = v___y_4390_;
v___y_4362_ = v___y_4391_;
v___y_4363_ = v___y_4392_;
v___y_4364_ = v___x_4401_;
goto v___jp_4343_;
}
}
v___jp_4403_:
{
lean_object* v_ref_4419_; uint8_t v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v_ref_4419_ = lean_ctor_get(v___y_4409_, 2);
v___x_4420_ = 0;
v___x_4421_ = l_Lean_SourceInfo_fromRef(v_ref_4419_, v___x_4420_);
v___x_4422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4423_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4424_ = l_Lean_SourceInfo_fromRef(v_tk_4402_, v___x_4273_);
lean_dec(v_tk_4402_);
v___x_4425_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
lean_ctor_set(v___x_4425_, 1, v___x_4422_);
v___x_4426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_4427_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_4413_) == 1)
{
lean_object* v_val_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v_val_4428_ = lean_ctor_get(v___y_4413_, 0);
lean_inc(v_val_4428_);
lean_dec_ref_known(v___y_4413_, 1);
v___x_4429_ = l_Lean_SourceInfo_fromRef(v_val_4428_, v___x_4273_);
lean_dec(v_val_4428_);
v___x_4430_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4429_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = l_Array_mkArray1___redArg(v___x_4431_);
v___y_4373_ = v___y_4404_;
v___y_4374_ = v___y_4405_;
v___y_4375_ = v___x_4421_;
v___y_4376_ = v___y_4406_;
v___y_4377_ = v___x_4426_;
v___y_4378_ = v___y_4407_;
v___y_4379_ = v___y_4408_;
v___y_4380_ = v___y_4409_;
v___y_4381_ = v___y_4410_;
v___y_4382_ = v___y_4411_;
v___y_4383_ = v___y_4412_;
v___y_4384_ = v___y_4414_;
v___y_4385_ = v___x_4423_;
v___y_4386_ = v___x_4420_;
v___y_4387_ = v___y_4415_;
v___y_4388_ = v___x_4427_;
v___y_4389_ = v___y_4416_;
v___y_4390_ = v___y_4417_;
v___y_4391_ = v___x_4425_;
v___y_4392_ = v___y_4418_;
v___y_4393_ = v___x_4432_;
goto v___jp_4372_;
}
else
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4413_);
lean_dec(v___y_4413_);
v___y_4373_ = v___y_4404_;
v___y_4374_ = v___y_4405_;
v___y_4375_ = v___x_4421_;
v___y_4376_ = v___y_4406_;
v___y_4377_ = v___x_4426_;
v___y_4378_ = v___y_4407_;
v___y_4379_ = v___y_4408_;
v___y_4380_ = v___y_4409_;
v___y_4381_ = v___y_4410_;
v___y_4382_ = v___y_4411_;
v___y_4383_ = v___y_4412_;
v___y_4384_ = v___y_4414_;
v___y_4385_ = v___x_4423_;
v___y_4386_ = v___x_4420_;
v___y_4387_ = v___y_4415_;
v___y_4388_ = v___x_4427_;
v___y_4389_ = v___y_4416_;
v___y_4390_ = v___y_4417_;
v___y_4391_ = v___x_4425_;
v___y_4392_ = v___y_4418_;
v___y_4393_ = v___x_4433_;
goto v___jp_4372_;
}
}
v___jp_4434_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4450_ = lean_unsigned_to_nat(5u);
v___x_4451_ = l_Lean_Syntax_getArg(v___y_4440_, v___x_4450_);
lean_dec(v___y_4440_);
v___x_4452_ = l_Lean_Syntax_getOptional_x3f(v___y_4438_);
lean_dec(v___y_4438_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_box(0);
v___y_4404_ = v___y_4442_;
v___y_4405_ = v___y_4449_;
v___y_4406_ = v___y_4445_;
v___y_4407_ = v_args_4441_;
v___y_4408_ = v___y_4439_;
v___y_4409_ = v___y_4448_;
v___y_4410_ = v___y_4447_;
v___y_4411_ = v___y_4446_;
v___y_4412_ = v___y_4435_;
v___y_4413_ = v___y_4437_;
v___y_4414_ = v___y_4436_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___x_4451_;
v___y_4417_ = v___y_4443_;
v___y_4418_ = v___x_4453_;
goto v___jp_4403_;
}
else
{
lean_object* v_val_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
v_val_4454_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4452_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_val_4454_);
lean_dec(v___x_4452_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_val_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
v___y_4404_ = v___y_4442_;
v___y_4405_ = v___y_4449_;
v___y_4406_ = v___y_4445_;
v___y_4407_ = v_args_4441_;
v___y_4408_ = v___y_4439_;
v___y_4409_ = v___y_4448_;
v___y_4410_ = v___y_4447_;
v___y_4411_ = v___y_4446_;
v___y_4412_ = v___y_4435_;
v___y_4413_ = v___y_4437_;
v___y_4414_ = v___y_4436_;
v___y_4415_ = v___y_4444_;
v___y_4416_ = v___x_4451_;
v___y_4417_ = v___y_4443_;
v___y_4418_ = v___x_4459_;
goto v___jp_4403_;
}
}
}
}
v___jp_4463_:
{
lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4479_ = l_Lean_Syntax_getArg(v___y_4467_, v___y_4469_);
v___x_4480_ = l_Lean_Syntax_isNone(v___x_4479_);
if (v___x_4480_ == 0)
{
uint8_t v___x_4481_; 
lean_inc(v___x_4479_);
v___x_4481_ = l_Lean_Syntax_matchesNull(v___x_4479_, v___x_4462_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; 
lean_dec(v___x_4479_);
lean_dec(v_only_4470_);
lean_dec(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec(v_tk_4402_);
v___x_4482_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4482_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
v___x_4483_ = l_Lean_Syntax_getArg(v___x_4479_, v___x_4275_);
lean_dec(v___x_4479_);
v___x_4484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4483_);
v___x_4485_ = l_Lean_Syntax_isOfKind(v___x_4483_, v___x_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; 
lean_dec(v___x_4483_);
lean_dec(v_only_4470_);
lean_dec(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec(v_tk_4402_);
v___x_4486_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4486_;
}
else
{
lean_object* v___x_4487_; lean_object* v_args_4488_; lean_object* v___x_4489_; 
v___x_4487_ = l_Lean_Syntax_getArg(v___x_4483_, v___x_4462_);
lean_dec(v___x_4483_);
v_args_4488_ = l_Lean_Syntax_getArgs(v___x_4487_);
lean_dec(v___x_4487_);
v___x_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4489_, 0, v_args_4488_);
v___y_4435_ = v_only_4470_;
v___y_4436_ = v___y_4465_;
v___y_4437_ = v___y_4464_;
v___y_4438_ = v___y_4466_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4467_;
v_args_4441_ = v___x_4489_;
v___y_4442_ = v___y_4471_;
v___y_4443_ = v___y_4472_;
v___y_4444_ = v___y_4473_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4475_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4478_;
goto v___jp_4434_;
}
}
}
else
{
lean_object* v___x_4490_; 
lean_dec(v___x_4479_);
v___x_4490_ = lean_box(0);
v___y_4435_ = v_only_4470_;
v___y_4436_ = v___y_4465_;
v___y_4437_ = v___y_4464_;
v___y_4438_ = v___y_4466_;
v___y_4439_ = v___y_4468_;
v___y_4440_ = v___y_4467_;
v_args_4441_ = v___x_4490_;
v___y_4442_ = v___y_4471_;
v___y_4443_ = v___y_4472_;
v___y_4444_ = v___y_4473_;
v___y_4445_ = v___y_4474_;
v___y_4446_ = v___y_4475_;
v___y_4447_ = v___y_4476_;
v___y_4448_ = v___y_4477_;
v___y_4449_ = v___y_4478_;
goto v___jp_4434_;
}
}
v___jp_4491_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; uint8_t v___x_4506_; 
v___x_4503_ = lean_unsigned_to_nat(3u);
v___x_4504_ = l_Lean_Syntax_getArg(v_stx_4231_, v___x_4503_);
lean_dec(v_stx_4231_);
v___x_4505_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4504_);
v___x_4506_ = l_Lean_Syntax_isOfKind(v___x_4504_, v___x_4505_);
if (v___x_4506_ == 0)
{
lean_object* v___x_4507_; 
lean_dec(v___x_4504_);
lean_dec(v_unfold_4494_);
lean_dec(v___y_4492_);
lean_dec(v_tk_4402_);
v___x_4507_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4507_;
}
else
{
lean_object* v___x_4508_; lean_object* v___x_4509_; uint8_t v___x_4510_; 
v___x_4508_ = l_Lean_Syntax_getArg(v___x_4504_, v___x_4275_);
v___x_4509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4508_);
v___x_4510_ = l_Lean_Syntax_isOfKind(v___x_4508_, v___x_4509_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
lean_dec(v___x_4508_);
lean_dec(v___x_4504_);
lean_dec(v_unfold_4494_);
lean_dec(v___y_4492_);
lean_dec(v_tk_4402_);
v___x_4511_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4511_;
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4512_ = l_Lean_Syntax_getArg(v___x_4504_, v___x_4462_);
v___x_4513_ = l_Lean_Syntax_getArg(v___x_4504_, v___y_4493_);
v___x_4514_ = l_Lean_Syntax_isNone(v___x_4513_);
if (v___x_4514_ == 0)
{
uint8_t v___x_4515_; 
lean_inc(v___x_4513_);
v___x_4515_ = l_Lean_Syntax_matchesNull(v___x_4513_, v___x_4462_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; 
lean_dec(v___x_4513_);
lean_dec(v___x_4512_);
lean_dec(v___x_4508_);
lean_dec(v___x_4504_);
lean_dec(v_unfold_4494_);
lean_dec(v___y_4492_);
lean_dec(v_tk_4402_);
v___x_4516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4516_;
}
else
{
lean_object* v_only_4517_; lean_object* v___x_4518_; 
v_only_4517_ = l_Lean_Syntax_getArg(v___x_4513_, v___x_4275_);
lean_dec(v___x_4513_);
v___x_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4518_, 0, v_only_4517_);
v___y_4464_ = v___y_4492_;
v___y_4465_ = v_unfold_4494_;
v___y_4466_ = v___x_4512_;
v___y_4467_ = v___x_4504_;
v___y_4468_ = v___x_4508_;
v___y_4469_ = v___x_4503_;
v_only_4470_ = v___x_4518_;
v___y_4471_ = v___y_4495_;
v___y_4472_ = v___y_4496_;
v___y_4473_ = v___y_4497_;
v___y_4474_ = v___y_4498_;
v___y_4475_ = v___y_4499_;
v___y_4476_ = v___y_4500_;
v___y_4477_ = v___y_4501_;
v___y_4478_ = v___y_4502_;
goto v___jp_4463_;
}
}
else
{
lean_object* v___x_4519_; 
lean_dec(v___x_4513_);
v___x_4519_ = lean_box(0);
v___y_4464_ = v___y_4492_;
v___y_4465_ = v_unfold_4494_;
v___y_4466_ = v___x_4512_;
v___y_4467_ = v___x_4504_;
v___y_4468_ = v___x_4508_;
v___y_4469_ = v___x_4503_;
v_only_4470_ = v___x_4519_;
v___y_4471_ = v___y_4495_;
v___y_4472_ = v___y_4496_;
v___y_4473_ = v___y_4497_;
v___y_4474_ = v___y_4498_;
v___y_4475_ = v___y_4499_;
v___y_4476_ = v___y_4500_;
v___y_4477_ = v___y_4501_;
v___y_4478_ = v___y_4502_;
goto v___jp_4463_;
}
}
}
}
v___jp_4520_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; 
v___x_4530_ = lean_unsigned_to_nat(2u);
v___x_4531_ = l_Lean_Syntax_getArg(v_stx_4231_, v___x_4530_);
v___x_4532_ = l_Lean_Syntax_isNone(v___x_4531_);
if (v___x_4532_ == 0)
{
uint8_t v___x_4533_; 
lean_inc(v___x_4531_);
v___x_4533_ = l_Lean_Syntax_matchesNull(v___x_4531_, v___x_4462_);
if (v___x_4533_ == 0)
{
lean_object* v___x_4534_; 
lean_dec(v___x_4531_);
lean_dec(v_squeeze_4521_);
lean_dec(v_tk_4402_);
lean_dec(v_stx_4231_);
v___x_4534_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4534_;
}
else
{
lean_object* v_unfold_4535_; lean_object* v___x_4536_; 
v_unfold_4535_ = l_Lean_Syntax_getArg(v___x_4531_, v___x_4275_);
lean_dec(v___x_4531_);
v___x_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_unfold_4535_);
v___y_4492_ = v_squeeze_4521_;
v___y_4493_ = v___x_4530_;
v_unfold_4494_ = v___x_4536_;
v___y_4495_ = v___y_4522_;
v___y_4496_ = v___y_4523_;
v___y_4497_ = v___y_4524_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
v___y_4500_ = v___y_4527_;
v___y_4501_ = v___y_4528_;
v___y_4502_ = v___y_4529_;
goto v___jp_4491_;
}
}
else
{
lean_object* v___x_4537_; 
lean_dec(v___x_4531_);
v___x_4537_ = lean_box(0);
v___y_4492_ = v_squeeze_4521_;
v___y_4493_ = v___x_4530_;
v_unfold_4494_ = v___x_4537_;
v___y_4495_ = v___y_4522_;
v___y_4496_ = v___y_4523_;
v___y_4497_ = v___y_4524_;
v___y_4498_ = v___y_4525_;
v___y_4499_ = v___y_4526_;
v___y_4500_ = v___y_4527_;
v___y_4501_ = v___y_4528_;
v___y_4502_ = v___y_4529_;
goto v___jp_4491_;
}
}
}
v___jp_4241_:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
lean_inc_ref(v___y_4257_);
v___x_4264_ = l_Array_append___redArg(v___y_4257_, v___y_4263_);
lean_dec_ref(v___y_4263_);
lean_inc_n(v___y_4246_, 2);
lean_inc_n(v___y_4245_, 4);
v___x_4265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4265_, 0, v___y_4245_);
lean_ctor_set(v___x_4265_, 1, v___y_4246_);
lean_ctor_set(v___x_4265_, 2, v___x_4264_);
v___x_4266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___y_4245_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_Syntax_node2(v___y_4245_, v___y_4246_, v___x_4267_, v___y_4259_);
lean_inc(v___y_4262_);
v___x_4269_ = l_Lean_Syntax_node5(v___y_4245_, v___y_4262_, v___y_4248_, v___y_4253_, v___y_4258_, v___x_4265_, v___x_4268_);
lean_inc(v___y_4254_);
v___x_4270_ = l_Lean_Syntax_node4(v___y_4245_, v___y_4254_, v___y_4261_, v___y_4247_, v___y_4251_, v___x_4269_);
v___x_4271_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4255_, v___x_4270_, v___y_4242_, v___y_4260_, v___y_4256_, v___y_4244_, v___y_4252_, v___y_4250_, v___y_4249_, v___y_4243_);
return v___x_4271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4548_);
lean_dec(v_a_4547_);
lean_dec_ref(v_a_4546_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4564_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4565_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4568_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4564_, v___x_4565_, v___x_4566_, v___x_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4570_;
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
