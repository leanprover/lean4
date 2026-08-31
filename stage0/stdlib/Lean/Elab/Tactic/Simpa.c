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
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20(lean_object*, lean_object*, lean_object*);
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
uint8_t v_suppressElabErrors_boxed_116_; uint8_t v___y_4756__boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_suppressElabErrors_boxed_116_ = lean_unbox(v_suppressElabErrors_113_);
v___y_4756__boxed_117_ = lean_unbox(v___y_114_);
v_res_118_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_116_, v___y_4756__boxed_117_, v_x_115_);
lean_dec(v_x_115_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; lean_object* v_env_127_; lean_object* v___x_128_; lean_object* v_mctx_129_; lean_object* v_lctx_130_; lean_object* v_options_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_126_ = lean_st_ref_get(v___y_124_);
v_env_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_env_127_);
lean_dec(v___x_126_);
v___x_128_ = lean_st_ref_get(v___y_122_);
v_mctx_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc_ref(v_mctx_129_);
lean_dec(v___x_128_);
v_lctx_130_ = lean_ctor_get(v___y_121_, 2);
v_options_131_ = lean_ctor_get(v___y_123_, 2);
lean_inc_ref(v_options_131_);
lean_inc_ref(v_lctx_130_);
v___x_132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_132_, 0, v_env_127_);
lean_ctor_set(v___x_132_, 1, v_mctx_129_);
lean_ctor_set(v___x_132_, 2, v_lctx_130_);
lean_ctor_set(v___x_132_, 3, v_options_131_);
v___x_133_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_msgData_120_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msgData_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_143_, lean_object* v_msgData_144_, uint8_t v_severity_145_, uint8_t v_isSilent_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; uint8_t v___y_158_; uint8_t v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; uint8_t v___y_194_; uint8_t v___y_195_; lean_object* v___y_196_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v___y_218_; uint8_t v___y_219_; uint8_t v___y_220_; lean_object* v___y_221_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; uint8_t v___y_229_; uint8_t v___y_230_; uint8_t v___y_231_; uint8_t v___x_236_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; uint8_t v___y_242_; uint8_t v___y_243_; uint8_t v___y_244_; uint8_t v___y_246_; uint8_t v___x_261_; 
v___x_236_ = 2;
v___x_261_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_236_);
if (v___x_261_ == 0)
{
v___y_246_ = v___x_261_;
goto v___jp_245_;
}
else
{
uint8_t v___x_262_; 
lean_inc_ref(v_msgData_144_);
v___x_262_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_144_);
v___y_246_ = v___x_262_;
goto v___jp_245_;
}
v___jp_152_:
{
lean_object* v___x_162_; lean_object* v_currNamespace_163_; lean_object* v_openDecls_164_; lean_object* v_env_165_; lean_object* v_nextMacroScope_166_; lean_object* v_ngen_167_; lean_object* v_auxDeclNGen_168_; lean_object* v_traceState_169_; lean_object* v_cache_170_; lean_object* v_messages_171_; lean_object* v_infoState_172_; lean_object* v_snapshotTasks_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_187_; 
v___x_162_ = lean_st_ref_take(v___y_161_);
v_currNamespace_163_ = lean_ctor_get(v___y_160_, 6);
v_openDecls_164_ = lean_ctor_get(v___y_160_, 7);
v_env_165_ = lean_ctor_get(v___x_162_, 0);
v_nextMacroScope_166_ = lean_ctor_get(v___x_162_, 1);
v_ngen_167_ = lean_ctor_get(v___x_162_, 2);
v_auxDeclNGen_168_ = lean_ctor_get(v___x_162_, 3);
v_traceState_169_ = lean_ctor_get(v___x_162_, 4);
v_cache_170_ = lean_ctor_get(v___x_162_, 5);
v_messages_171_ = lean_ctor_get(v___x_162_, 6);
v_infoState_172_ = lean_ctor_get(v___x_162_, 7);
v_snapshotTasks_173_ = lean_ctor_get(v___x_162_, 8);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_187_ == 0)
{
v___x_175_ = v___x_162_;
v_isShared_176_ = v_isSharedCheck_187_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snapshotTasks_173_);
lean_inc(v_infoState_172_);
lean_inc(v_messages_171_);
lean_inc(v_cache_170_);
lean_inc(v_traceState_169_);
lean_inc(v_auxDeclNGen_168_);
lean_inc(v_ngen_167_);
lean_inc(v_nextMacroScope_166_);
lean_inc(v_env_165_);
lean_dec(v___x_162_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_187_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
lean_inc(v_openDecls_164_);
lean_inc(v_currNamespace_163_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_currNamespace_163_);
lean_ctor_set(v___x_177_, 1, v_openDecls_164_);
v___x_178_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___y_156_);
lean_inc_ref(v___y_157_);
lean_inc_ref(v___y_155_);
v___x_179_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_179_, 0, v___y_155_);
lean_ctor_set(v___x_179_, 1, v___y_154_);
lean_ctor_set(v___x_179_, 2, v___y_153_);
lean_ctor_set(v___x_179_, 3, v___y_157_);
lean_ctor_set(v___x_179_, 4, v___x_178_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5, v___y_159_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5 + 1, v___y_158_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5 + 2, v_isSilent_146_);
v___x_180_ = l_Lean_MessageLog_add(v___x_179_, v_messages_171_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 6, v___x_180_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_env_165_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_nextMacroScope_166_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_ngen_167_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_auxDeclNGen_168_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_traceState_169_);
lean_ctor_set(v_reuseFailAlloc_186_, 5, v_cache_170_);
lean_ctor_set(v_reuseFailAlloc_186_, 6, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_186_, 7, v_infoState_172_);
lean_ctor_set(v_reuseFailAlloc_186_, 8, v_snapshotTasks_173_);
v___x_182_ = v_reuseFailAlloc_186_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_st_ref_put(v___y_161_, v___x_182_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
}
v___jp_188_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_212_; 
v___x_197_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_144_);
v___x_198_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v___x_197_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc_ref_n(v___y_191_, 2);
v___x_203_ = l_Lean_FileMap_toPosition(v___y_191_, v___y_190_);
lean_dec(v___y_190_);
v___x_204_ = l_Lean_FileMap_toPosition(v___y_191_, v___y_196_);
lean_dec(v___y_196_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___closed__0));
if (v___y_193_ == 0)
{
lean_del_object(v___x_201_);
lean_dec_ref(v___y_189_);
v___y_153_ = v___x_205_;
v___y_154_ = v___x_203_;
v___y_155_ = v___y_192_;
v___y_156_ = v_a_199_;
v___y_157_ = v___x_206_;
v___y_158_ = v___y_195_;
v___y_159_ = v___y_194_;
v___y_160_ = v___y_149_;
v___y_161_ = v___y_150_;
goto v___jp_152_;
}
else
{
uint8_t v___x_207_; 
lean_inc(v_a_199_);
v___x_207_ = l_Lean_MessageData_hasTag(v___y_189_, v_a_199_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec_ref_known(v___x_205_, 1);
lean_dec_ref(v___x_203_);
lean_dec(v_a_199_);
v___x_208_ = lean_box(0);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_208_);
v___x_210_ = v___x_201_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
else
{
lean_del_object(v___x_201_);
v___y_153_ = v___x_205_;
v___y_154_ = v___x_203_;
v___y_155_ = v___y_192_;
v___y_156_ = v_a_199_;
v___y_157_ = v___x_206_;
v___y_158_ = v___y_195_;
v___y_159_ = v___y_194_;
v___y_160_ = v___y_149_;
v___y_161_ = v___y_150_;
goto v___jp_152_;
}
}
}
}
v___jp_213_:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Syntax_getTailPos_x3f(v___y_217_, v___y_220_);
lean_dec(v___y_217_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_inc(v___y_221_);
v___y_189_ = v___y_214_;
v___y_190_ = v___y_221_;
v___y_191_ = v___y_215_;
v___y_192_ = v___y_216_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_219_;
v___y_196_ = v___y_221_;
goto v___jp_188_;
}
else
{
lean_object* v_val_223_; 
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_189_ = v___y_214_;
v___y_190_ = v___y_221_;
v___y_191_ = v___y_215_;
v___y_192_ = v___y_216_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_220_;
v___y_195_ = v___y_219_;
v___y_196_ = v_val_223_;
goto v___jp_188_;
}
}
v___jp_224_:
{
lean_object* v_ref_232_; lean_object* v___x_233_; 
v_ref_232_ = l_Lean_replaceRef(v_ref_143_, v___y_228_);
v___x_233_ = l_Lean_Syntax_getPos_x3f(v_ref_232_, v___y_230_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v___y_214_ = v___y_225_;
v___y_215_ = v___y_226_;
v___y_216_ = v___y_227_;
v___y_217_ = v_ref_232_;
v___y_218_ = v___y_229_;
v___y_219_ = v___y_231_;
v___y_220_ = v___y_230_;
v___y_221_ = v___x_234_;
goto v___jp_213_;
}
else
{
lean_object* v_val_235_; 
v_val_235_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_233_, 1);
v___y_214_ = v___y_225_;
v___y_215_ = v___y_226_;
v___y_216_ = v___y_227_;
v___y_217_ = v_ref_232_;
v___y_218_ = v___y_229_;
v___y_219_ = v___y_231_;
v___y_220_ = v___y_230_;
v___y_221_ = v_val_235_;
goto v___jp_213_;
}
}
v___jp_237_:
{
if (v___y_244_ == 0)
{
v___y_225_ = v___y_239_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_241_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_242_;
v___y_230_ = v___y_243_;
v___y_231_ = v_severity_145_;
goto v___jp_224_;
}
else
{
v___y_225_ = v___y_239_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_241_;
v___y_228_ = v___y_240_;
v___y_229_ = v___y_242_;
v___y_230_ = v___y_243_;
v___y_231_ = v___x_236_;
goto v___jp_224_;
}
}
v___jp_245_:
{
if (v___y_246_ == 0)
{
lean_object* v_fileName_247_; lean_object* v_fileMap_248_; lean_object* v_options_249_; lean_object* v_ref_250_; uint8_t v_suppressElabErrors_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___f_254_; uint8_t v___x_255_; uint8_t v___x_256_; 
v_fileName_247_ = lean_ctor_get(v___y_149_, 0);
v_fileMap_248_ = lean_ctor_get(v___y_149_, 1);
v_options_249_ = lean_ctor_get(v___y_149_, 2);
v_ref_250_ = lean_ctor_get(v___y_149_, 5);
v_suppressElabErrors_251_ = lean_ctor_get_uint8(v___y_149_, sizeof(void*)*14 + 1);
v___x_252_ = lean_box(v_suppressElabErrors_251_);
v___x_253_ = lean_box(v___y_246_);
v___f_254_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_254_, 0, v___x_252_);
lean_closure_set(v___f_254_, 1, v___x_253_);
v___x_255_ = 1;
v___x_256_ = l_Lean_instBEqMessageSeverity_beq(v_severity_145_, v___x_255_);
if (v___x_256_ == 0)
{
v___y_238_ = v_fileMap_248_;
v___y_239_ = v___f_254_;
v___y_240_ = v_ref_250_;
v___y_241_ = v_fileName_247_;
v___y_242_ = v_suppressElabErrors_251_;
v___y_243_ = v___y_246_;
v___y_244_ = v___x_256_;
goto v___jp_237_;
}
else
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = l_Lean_warningAsError;
v___x_258_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_249_, v___x_257_);
v___y_238_ = v_fileMap_248_;
v___y_239_ = v___f_254_;
v___y_240_ = v_ref_250_;
v___y_241_ = v_fileName_247_;
v___y_242_ = v_suppressElabErrors_251_;
v___y_243_ = v___y_246_;
v___y_244_ = v___x_258_;
goto v___jp_237_;
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref(v_msgData_144_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_263_, lean_object* v_msgData_264_, lean_object* v_severity_265_, lean_object* v_isSilent_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v_severity_boxed_272_; uint8_t v_isSilent_boxed_273_; lean_object* v_res_274_; 
v_severity_boxed_272_ = lean_unbox(v_severity_265_);
v_isSilent_boxed_273_ = lean_unbox(v_isSilent_266_);
v_res_274_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_263_, v_msgData_264_, v_severity_boxed_272_, v_isSilent_boxed_273_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v_ref_263_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(lean_object* v_ref_275_, lean_object* v_msgData_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
uint8_t v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; 
v___x_286_ = 1;
v___x_287_ = 0;
v___x_288_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_275_, v_msgData_276_, v___x_286_, v___x_287_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0___boxed(lean_object* v_ref_289_, lean_object* v_msgData_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_ref_289_, v_msgData_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v_ref_289_);
return v_res_300_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__0));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__2));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(lean_object* v_linterOption_307_, lean_object* v_stx_308_, lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_name_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_337_; 
v_name_319_ = lean_ctor_get(v_linterOption_307_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_linterOption_307_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_linterOption_307_, 1);
lean_dec(v_unused_338_);
v___x_321_ = v_linterOption_307_;
v_isShared_322_ = v_isSharedCheck_337_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_name_319_);
lean_dec(v_linterOption_307_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_337_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__1);
lean_inc(v_name_319_);
v___x_324_ = l_Lean_MessageData_ofName(v_name_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 7);
lean_ctor_set(v___x_321_, 1, v___x_324_);
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_326_ = v___x_321_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_324_);
v___x_326_ = v_reuseFailAlloc_336_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_disable_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_327_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___closed__3);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v_disable_329_ = l_Lean_MessageData_note(v___x_328_);
v___x_330_ = l_Lean_Linter_linterMessageTag;
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v_msg_309_);
lean_ctor_set(v___x_331_, 1, v_disable_329_);
v___x_332_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_333_, 0, v_name_319_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
lean_inc(v_stx_308_);
v___x_334_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_334_, 0, v_stx_308_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0(v_stx_308_, v___x_334_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v_stx_308_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0___boxed(lean_object* v_linterOption_339_, lean_object* v_stx_340_, lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v_linterOption_339_, v_stx_340_, v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_351_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v_msg_354_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__0));
v_msg_354_ = l_Lean_stringToMessageData(v___x_353_);
return v_msg_354_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__5));
v___x_362_ = l_Lean_MessageData_ofFormat(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(lean_object* v_initialState_363_, lean_object* v_ref_364_, lean_object* v_replacement_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_msg_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_box(0);
lean_inc(v_replacement_365_);
v___x_388_ = l_Lean_Meta_Tactic_TryThis_isValidTactic(v_initialState_363_, v_replacement_365_, v___x_387_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v_msg_390_; uint8_t v___x_391_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v_msg_390_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__1);
v___x_391_ = lean_unbox(v_a_389_);
lean_dec(v_a_389_);
if (v___x_391_ == 0)
{
lean_dec(v_replacement_365_);
v_msg_376_ = v_msg_390_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
v___y_379_ = v_a_368_;
v___y_380_ = v_a_369_;
v___y_381_ = v_a_370_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
goto v___jp_375_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_replacement_365_);
v___x_394_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_387_);
lean_ctor_set(v___x_394_, 2, v___x_387_);
lean_ctor_set(v___x_394_, 3, v___x_387_);
lean_ctor_set(v___x_394_, 4, v___x_387_);
lean_ctor_set(v___x_394_, 5, v___x_387_);
lean_inc(v_ref_364_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_ref_364_);
v___x_396_ = 4;
lean_inc_ref(v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_397_, 0, v___x_394_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_387_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3, v___x_396_);
v___x_398_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__6);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_mk_empty_array_with_capacity(v___x_399_);
v___x_401_ = lean_array_push(v___x_400_, v___x_397_);
v___x_402_ = 0;
v___x_403_ = l_Lean_MessageData_hint(v___x_398_, v___x_401_, v___x_395_, v___x_387_, v___x_402_, v_a_372_, v_a_373_);
lean_dec_ref(v___x_401_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v_msg_390_);
lean_ctor_set(v___x_405_, 1, v_a_404_);
v_msg_376_ = v___x_405_;
v___y_377_ = v_a_366_;
v___y_378_ = v_a_367_;
v___y_379_ = v_a_368_;
v___y_380_ = v_a_369_;
v___y_381_ = v_a_370_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
goto v___jp_375_;
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_ref_364_);
v_a_406_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_403_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_403_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_replacement_365_);
lean_dec(v_ref_364_);
v_a_414_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_388_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_388_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
v___jp_375_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = l_Lean_linter_unnecessarySimpa;
v___x_386_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0(v___x_385_, v_ref_364_, v_msg_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___boxed(lean_object* v_initialState_422_, lean_object* v_ref_423_, lean_object* v_replacement_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_initialState_422_, v_ref_423_, v_replacement_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(lean_object* v_ref_435_, lean_object* v_msgData_436_, uint8_t v_severity_437_, uint8_t v_isSilent_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg(v_ref_435_, v_msgData_436_, v_severity_437_, v_isSilent_438_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_449_, lean_object* v_msgData_450_, lean_object* v_severity_451_, lean_object* v_isSilent_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v_severity_boxed_462_; uint8_t v_isSilent_boxed_463_; lean_object* v_res_464_; 
v_severity_boxed_462_ = lean_unbox(v_severity_451_);
v_isSilent_boxed_463_ = lean_unbox(v_isSilent_452_);
v_res_464_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1(v_ref_449_, v_msgData_450_, v_severity_boxed_462_, v_isSilent_boxed_463_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_ref_449_);
return v_res_464_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
v___x_466_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg(){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(lean_object* v_00_u03b1_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(lean_object* v_00_u03b1_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0(lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
v___x_505_ = lean_apply_9(v_x_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, lean_box(0));
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0(v_x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(lean_object* v_mvarId_517_, lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v___f_528_; lean_object* v___x_529_; 
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
v___f_528_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_528_, 0, v_x_518_);
lean_closure_set(v___f_528_, 1, v___y_519_);
lean_closure_set(v___f_528_, 2, v___y_520_);
lean_closure_set(v___f_528_, 3, v___y_521_);
lean_closure_set(v___f_528_, 4, v___y_522_);
v___x_529_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_517_, v___f_528_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_529_) == 0)
{
return v___x_529_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg___boxed(lean_object* v_mvarId_538_, lean_object* v_x_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_mvarId_538_, v_x_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(lean_object* v_00_u03b1_550_, lean_object* v_mvarId_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_mvarId_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(lean_object* v_00_u03b1_563_, lean_object* v_mvarId_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_00_u03b1_563_, v_mvarId_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_575_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_unsigned_to_nat(32u);
v___x_577_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_579_ = ((size_t)5ULL);
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_unsigned_to_nat(32u);
v___x_582_ = lean_mk_empty_array_with_capacity(v___x_581_);
v___x_583_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__0);
v___x_584_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_580_);
lean_ctor_set(v___x_584_, 3, v___x_580_);
lean_ctor_set_usize(v___x_584_, 4, v___x_579_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; lean_object* v_infoState_588_; lean_object* v_trees_589_; lean_object* v___x_590_; lean_object* v_infoState_591_; lean_object* v_env_592_; lean_object* v_nextMacroScope_593_; lean_object* v_ngen_594_; lean_object* v_auxDeclNGen_595_; lean_object* v_traceState_596_; lean_object* v_cache_597_; lean_object* v_messages_598_; lean_object* v_snapshotTasks_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_620_; 
v___x_587_ = lean_st_ref_get(v___y_585_);
v_infoState_588_ = lean_ctor_get(v___x_587_, 7);
lean_inc_ref(v_infoState_588_);
lean_dec(v___x_587_);
v_trees_589_ = lean_ctor_get(v_infoState_588_, 2);
lean_inc_ref(v_trees_589_);
lean_dec_ref(v_infoState_588_);
v___x_590_ = lean_st_ref_take(v___y_585_);
v_infoState_591_ = lean_ctor_get(v___x_590_, 7);
v_env_592_ = lean_ctor_get(v___x_590_, 0);
v_nextMacroScope_593_ = lean_ctor_get(v___x_590_, 1);
v_ngen_594_ = lean_ctor_get(v___x_590_, 2);
v_auxDeclNGen_595_ = lean_ctor_get(v___x_590_, 3);
v_traceState_596_ = lean_ctor_get(v___x_590_, 4);
v_cache_597_ = lean_ctor_get(v___x_590_, 5);
v_messages_598_ = lean_ctor_get(v___x_590_, 6);
v_snapshotTasks_599_ = lean_ctor_get(v___x_590_, 8);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_620_ == 0)
{
v___x_601_ = v___x_590_;
v_isShared_602_ = v_isSharedCheck_620_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_snapshotTasks_599_);
lean_inc(v_infoState_591_);
lean_inc(v_messages_598_);
lean_inc(v_cache_597_);
lean_inc(v_traceState_596_);
lean_inc(v_auxDeclNGen_595_);
lean_inc(v_ngen_594_);
lean_inc(v_nextMacroScope_593_);
lean_inc(v_env_592_);
lean_dec(v___x_590_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_620_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v_enabled_603_; lean_object* v_assignment_604_; lean_object* v_lazyAssignment_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_618_; 
v_enabled_603_ = lean_ctor_get_uint8(v_infoState_591_, sizeof(void*)*3);
v_assignment_604_ = lean_ctor_get(v_infoState_591_, 0);
v_lazyAssignment_605_ = lean_ctor_get(v_infoState_591_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_infoState_591_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_infoState_591_, 2);
lean_dec(v_unused_619_);
v___x_607_ = v_infoState_591_;
v_isShared_608_ = v_isSharedCheck_618_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_lazyAssignment_605_);
lean_inc(v_assignment_604_);
lean_dec(v_infoState_591_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_618_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___closed__1);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_assignment_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_lazyAssignment_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___x_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_617_, sizeof(void*)*3, v_enabled_603_);
v___x_611_ = v_reuseFailAlloc_617_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 7, v___x_611_);
v___x_613_ = v___x_601_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_env_592_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_nextMacroScope_593_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_ngen_594_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_auxDeclNGen_595_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_traceState_596_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_cache_597_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_messages_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_snapshotTasks_599_);
v___x_613_ = v_reuseFailAlloc_616_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_st_ref_put(v___y_585_, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_trees_589_);
return v___x_615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_621_);
lean_dec(v___y_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___f_655_; lean_object* v___x_81280__overap_656_; lean_object* v___x_657_; 
v___f_655_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___closed__0));
v___x_81280__overap_656_ = lean_panic_fn_borrowed(v___f_655_, v_msg_645_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
lean_inc(v___y_651_);
lean_inc_ref(v___y_650_);
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
v___x_657_ = lean_apply_9(v___x_81280__overap_656_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, lean_box(0));
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_ref_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_ref_678_ = lean_ctor_get(v___y_675_, 5);
v___x_679_ = 0;
v___x_680_ = l_Lean_SourceInfo_fromRef(v_ref_678_, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_691_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6(void){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Array_mkArray0(lean_box(0));
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v_args_710_, lean_object* v_only_711_, uint8_t v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v___y_716_, lean_object* v_unfold_717_, uint8_t v___x_718_, lean_object* v_squeeze_719_, lean_object* v_loc_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; uint8_t v___y_793_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; uint8_t v___y_868_; 
if (lean_obj_tag(v_squeeze_719_) == 0)
{
uint8_t v___x_881_; 
v___x_881_ = 0;
v___y_868_ = v___x_881_;
goto v___jp_867_;
}
else
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_1017_; 
v_isSharedCheck_1017_ = !lean_is_exclusive(v_squeeze_719_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v_squeeze_719_, 0);
lean_dec(v_unused_1018_);
v___x_883_ = v_squeeze_719_;
v_isShared_884_ = v_isSharedCheck_1017_;
goto v_resetjp_882_;
}
else
{
lean_dec(v_squeeze_719_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_1017_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (v___x_718_ == 0)
{
lean_del_object(v___x_883_);
v___y_868_ = v___x_718_;
goto v___jp_867_;
}
else
{
if (lean_obj_tag(v_unfold_717_) == 0)
{
lean_object* v_ref_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_936_; 
v_ref_885_ = lean_ctor_get(v___y_727_, 5);
v___x_886_ = 0;
v___x_887_ = l_Lean_SourceInfo_fromRef(v_ref_885_, v___x_886_);
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__9));
lean_inc_ref_n(v___x_715_, 2);
lean_inc_ref_n(v___x_714_, 2);
lean_inc_ref_n(v___x_713_, 2);
v___x_889_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_888_);
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__10));
lean_inc_n(v___x_887_, 2);
v___x_891_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_887_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_893_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
v___x_894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_894_, 0, v___x_887_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
lean_ctor_set(v___x_894_, 2, v___x_893_);
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_896_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_895_);
if (lean_obj_tag(v___y_716_) == 0)
{
lean_object* v___x_945_; 
v___x_945_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_936_ = v___x_945_;
goto v___jp_935_;
}
else
{
lean_object* v_val_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_val_946_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_val_946_);
lean_dec_ref_known(v___y_716_, 1);
v___x_947_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_948_ = lean_array_push(v___x_947_, v_val_946_);
v___y_936_ = v___x_948_;
goto v___jp_935_;
}
v___jp_897_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_902_ = l_Array_append___redArg(v___x_893_, v___y_901_);
lean_dec_ref(v___y_901_);
lean_inc_n(v___x_887_, 2);
v___x_903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_903_, 0, v___x_887_);
lean_ctor_set(v___x_903_, 1, v___x_892_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
v___x_904_ = l_Lean_Syntax_node5(v___x_887_, v___x_896_, v___x_708_, v___y_900_, v___y_899_, v___y_898_, v___x_903_);
v___x_905_ = l_Lean_Syntax_node3(v___x_887_, v___x_889_, v___x_891_, v___x_894_, v___x_904_);
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
lean_ctor_set(v___x_883_, 0, v___x_905_);
v___x_907_ = v___x_883_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
v___jp_909_:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = l_Array_append___redArg(v___x_893_, v___y_912_);
lean_dec_ref(v___y_912_);
lean_inc(v___x_887_);
v___x_914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_914_, 0, v___x_887_);
lean_ctor_set(v___x_914_, 1, v___x_892_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
if (lean_obj_tag(v_loc_720_) == 1)
{
lean_object* v_val_915_; lean_object* v___x_916_; 
v_val_915_ = lean_ctor_get(v_loc_720_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v_loc_720_, 1);
v___x_916_ = l_Array_mkArray1___redArg(v_val_915_);
v___y_898_ = v___x_914_;
v___y_899_ = v___y_910_;
v___y_900_ = v___y_911_;
v___y_901_ = v___x_916_;
goto v___jp_897_;
}
else
{
lean_object* v___x_917_; 
lean_dec(v_loc_720_);
v___x_917_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_898_ = v___x_914_;
v___y_899_ = v___y_910_;
v___y_900_ = v___y_911_;
v___y_901_ = v___x_917_;
goto v___jp_897_;
}
}
v___jp_918_:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = l_Array_append___redArg(v___x_893_, v___y_920_);
lean_dec_ref(v___y_920_);
lean_inc(v___x_887_);
v___x_922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_922_, 0, v___x_887_);
lean_ctor_set(v___x_922_, 1, v___x_892_);
lean_ctor_set(v___x_922_, 2, v___x_921_);
if (lean_obj_tag(v_args_710_) == 1)
{
lean_object* v_val_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_val_923_ = lean_ctor_get(v_args_710_, 0);
v___x_924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_925_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_924_);
v___x_926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_887_, 4);
v___x_927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_887_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Array_append___redArg(v___x_893_, v_val_923_);
v___x_929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_929_, 0, v___x_887_);
lean_ctor_set(v___x_929_, 1, v___x_892_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_887_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_Syntax_node3(v___x_887_, v___x_925_, v___x_927_, v___x_929_, v___x_931_);
v___x_933_ = l_Array_mkArray1___redArg(v___x_932_);
v___y_910_ = v___x_922_;
v___y_911_ = v___y_919_;
v___y_912_ = v___x_933_;
goto v___jp_909_;
}
else
{
lean_object* v___x_934_; 
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_713_);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_910_ = v___x_922_;
v___y_911_ = v___y_919_;
v___y_912_ = v___x_934_;
goto v___jp_909_;
}
}
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = l_Array_append___redArg(v___x_893_, v___y_936_);
lean_dec_ref(v___y_936_);
lean_inc(v___x_887_);
v___x_938_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_938_, 0, v___x_887_);
lean_ctor_set(v___x_938_, 1, v___x_892_);
lean_ctor_set(v___x_938_, 2, v___x_937_);
if (lean_obj_tag(v_only_711_) == 1)
{
lean_object* v_val_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_val_939_ = lean_ctor_get(v_only_711_, 0);
v___x_940_ = l_Lean_SourceInfo_fromRef(v_val_939_, v___x_712_);
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Array_mkArray1___redArg(v___x_942_);
v___y_919_ = v___x_938_;
v___y_920_ = v___x_943_;
goto v___jp_918_;
}
else
{
lean_object* v___x_944_; 
v___x_944_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_919_ = v___x_938_;
v___y_920_ = v___x_944_;
goto v___jp_918_;
}
}
}
else
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1015_; 
lean_del_object(v___x_883_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_unfold_717_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v_unfold_717_, 0);
lean_dec(v_unused_1016_);
v___x_950_ = v_unfold_717_;
v_isShared_951_ = v_isSharedCheck_1015_;
goto v_resetjp_949_;
}
else
{
lean_dec(v_unfold_717_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1015_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_ref_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_1002_; 
v_ref_952_ = lean_ctor_get(v___y_727_, 5);
v___x_953_ = 0;
v___x_954_ = l_Lean_SourceInfo_fromRef(v_ref_952_, v___x_953_);
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__13));
lean_inc_ref_n(v___x_715_, 2);
lean_inc_ref_n(v___x_714_, 2);
lean_inc_ref_n(v___x_713_, 2);
v___x_956_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_955_);
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__14));
lean_inc(v___x_954_);
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_954_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__11));
v___x_960_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_959_);
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_962_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_716_) == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_1002_ = v___x_1011_;
goto v___jp_1001_;
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_val_1012_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v___y_716_, 1);
v___x_1013_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_1014_ = lean_array_push(v___x_1013_, v_val_1012_);
v___y_1002_ = v___x_1014_;
goto v___jp_1001_;
}
v___jp_963_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_968_ = l_Array_append___redArg(v___x_962_, v___y_967_);
lean_dec_ref(v___y_967_);
lean_inc_n(v___x_954_, 2);
v___x_969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_969_, 0, v___x_954_);
lean_ctor_set(v___x_969_, 1, v___x_961_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
v___x_970_ = l_Lean_Syntax_node5(v___x_954_, v___x_960_, v___x_708_, v___y_965_, v___y_964_, v___y_966_, v___x_969_);
v___x_971_ = l_Lean_Syntax_node2(v___x_954_, v___x_956_, v___x_958_, v___x_970_);
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 0);
lean_ctor_set(v___x_950_, 0, v___x_971_);
v___x_973_ = v___x_950_;
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
v___jp_975_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = l_Array_append___redArg(v___x_962_, v___y_978_);
lean_dec_ref(v___y_978_);
lean_inc(v___x_954_);
v___x_980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_980_, 0, v___x_954_);
lean_ctor_set(v___x_980_, 1, v___x_961_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
if (lean_obj_tag(v_loc_720_) == 1)
{
lean_object* v_val_981_; lean_object* v___x_982_; 
v_val_981_ = lean_ctor_get(v_loc_720_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v_loc_720_, 1);
v___x_982_ = l_Array_mkArray1___redArg(v_val_981_);
v___y_964_ = v___y_976_;
v___y_965_ = v___y_977_;
v___y_966_ = v___x_980_;
v___y_967_ = v___x_982_;
goto v___jp_963_;
}
else
{
lean_object* v___x_983_; 
lean_dec(v_loc_720_);
v___x_983_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_964_ = v___y_976_;
v___y_965_ = v___y_977_;
v___y_966_ = v___x_980_;
v___y_967_ = v___x_983_;
goto v___jp_963_;
}
}
v___jp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_Array_append___redArg(v___x_962_, v___y_986_);
lean_dec_ref(v___y_986_);
lean_inc(v___x_954_);
v___x_988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_988_, 0, v___x_954_);
lean_ctor_set(v___x_988_, 1, v___x_961_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
if (lean_obj_tag(v_args_710_) == 1)
{
lean_object* v_val_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_val_989_ = lean_ctor_get(v_args_710_, 0);
v___x_990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_991_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_990_);
v___x_992_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_954_, 4);
v___x_993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_954_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Array_append___redArg(v___x_962_, v_val_989_);
v___x_995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_995_, 0, v___x_954_);
lean_ctor_set(v___x_995_, 1, v___x_961_);
lean_ctor_set(v___x_995_, 2, v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_954_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_Syntax_node3(v___x_954_, v___x_991_, v___x_993_, v___x_995_, v___x_997_);
v___x_999_ = l_Array_mkArray1___redArg(v___x_998_);
v___y_976_ = v___x_988_;
v___y_977_ = v___y_985_;
v___y_978_ = v___x_999_;
goto v___jp_975_;
}
else
{
lean_object* v___x_1000_; 
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_713_);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_976_ = v___x_988_;
v___y_977_ = v___y_985_;
v___y_978_ = v___x_1000_;
goto v___jp_975_;
}
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = l_Array_append___redArg(v___x_962_, v___y_1002_);
lean_dec_ref(v___y_1002_);
lean_inc(v___x_954_);
v___x_1004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1004_, 0, v___x_954_);
lean_ctor_set(v___x_1004_, 1, v___x_961_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
if (lean_obj_tag(v_only_711_) == 1)
{
lean_object* v_val_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_val_1005_ = lean_ctor_get(v_only_711_, 0);
v___x_1006_ = l_Lean_SourceInfo_fromRef(v_val_1005_, v___x_712_);
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_1008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Array_mkArray1___redArg(v___x_1008_);
v___y_985_ = v___x_1004_;
v___y_986_ = v___x_1009_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_985_ = v___x_1004_;
v___y_986_ = v___x_1010_;
goto v___jp_984_;
}
}
}
}
}
}
}
v___jp_730_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_inc_ref(v___y_738_);
v___x_740_ = l_Array_append___redArg(v___y_738_, v___y_739_);
lean_dec_ref(v___y_739_);
lean_inc(v___y_734_);
lean_inc(v___y_732_);
v___x_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_741_, 0, v___y_732_);
lean_ctor_set(v___x_741_, 1, v___y_734_);
lean_ctor_set(v___x_741_, 2, v___x_740_);
v___x_742_ = l_Lean_Syntax_node6(v___y_732_, v___y_736_, v___y_735_, v___x_708_, v___y_733_, v___y_731_, v___y_737_, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
v___jp_744_:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_inc_ref(v___y_751_);
v___x_753_ = l_Array_append___redArg(v___y_751_, v___y_752_);
lean_dec_ref(v___y_752_);
lean_inc(v___y_748_);
lean_inc(v___y_746_);
v___x_754_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_754_, 0, v___y_746_);
lean_ctor_set(v___x_754_, 1, v___y_748_);
lean_ctor_set(v___x_754_, 2, v___x_753_);
if (lean_obj_tag(v_loc_720_) == 1)
{
lean_object* v_val_755_; lean_object* v___x_756_; 
v_val_755_ = lean_ctor_get(v_loc_720_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v_loc_720_, 1);
v___x_756_ = l_Array_mkArray1___redArg(v_val_755_);
v___y_731_ = v___y_745_;
v___y_732_ = v___y_746_;
v___y_733_ = v___y_747_;
v___y_734_ = v___y_748_;
v___y_735_ = v___y_749_;
v___y_736_ = v___y_750_;
v___y_737_ = v___x_754_;
v___y_738_ = v___y_751_;
v___y_739_ = v___x_756_;
goto v___jp_730_;
}
else
{
lean_object* v___x_757_; 
lean_dec(v_loc_720_);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_731_ = v___y_745_;
v___y_732_ = v___y_746_;
v___y_733_ = v___y_747_;
v___y_734_ = v___y_748_;
v___y_735_ = v___y_749_;
v___y_736_ = v___y_750_;
v___y_737_ = v___x_754_;
v___y_738_ = v___y_751_;
v___y_739_ = v___x_757_;
goto v___jp_730_;
}
}
v___jp_758_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_inc_ref(v___y_764_);
v___x_766_ = l_Array_append___redArg(v___y_764_, v___y_765_);
lean_dec_ref(v___y_765_);
lean_inc(v___y_761_);
lean_inc(v___y_759_);
v___x_767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_767_, 0, v___y_759_);
lean_ctor_set(v___x_767_, 1, v___y_761_);
lean_ctor_set(v___x_767_, 2, v___x_766_);
if (lean_obj_tag(v_args_710_) == 1)
{
lean_object* v_val_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_val_768_ = lean_ctor_get(v_args_710_, 0);
v___x_769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_759_, 3);
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v___y_759_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_inc_ref(v___y_764_);
v___x_771_ = l_Array_append___redArg(v___y_764_, v_val_768_);
lean_inc(v___y_761_);
v___x_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_772_, 0, v___y_759_);
lean_ctor_set(v___x_772_, 1, v___y_761_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_774_, 0, v___y_759_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Array_mkArray3___redArg(v___x_770_, v___x_772_, v___x_774_);
v___y_745_ = v___x_767_;
v___y_746_ = v___y_759_;
v___y_747_ = v___y_760_;
v___y_748_ = v___y_761_;
v___y_749_ = v___y_762_;
v___y_750_ = v___y_763_;
v___y_751_ = v___y_764_;
v___y_752_ = v___x_775_;
goto v___jp_744_;
}
else
{
lean_object* v___x_776_; 
v___x_776_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_745_ = v___x_767_;
v___y_746_ = v___y_759_;
v___y_747_ = v___y_760_;
v___y_748_ = v___y_761_;
v___y_749_ = v___y_762_;
v___y_750_ = v___y_763_;
v___y_751_ = v___y_764_;
v___y_752_ = v___x_776_;
goto v___jp_744_;
}
}
v___jp_777_:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc_ref(v___y_782_);
v___x_784_ = l_Array_append___redArg(v___y_782_, v___y_783_);
lean_dec_ref(v___y_783_);
lean_inc(v___y_779_);
lean_inc(v___y_778_);
v___x_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_785_, 0, v___y_778_);
lean_ctor_set(v___x_785_, 1, v___y_779_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
if (lean_obj_tag(v_only_711_) == 1)
{
lean_object* v_val_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_val_786_ = lean_ctor_get(v_only_711_, 0);
v___x_787_ = l_Lean_SourceInfo_fromRef(v_val_786_, v___x_712_);
v___x_788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Array_mkArray1___redArg(v___x_789_);
v___y_759_ = v___y_778_;
v___y_760_ = v___x_785_;
v___y_761_ = v___y_779_;
v___y_762_ = v___y_780_;
v___y_763_ = v___y_781_;
v___y_764_ = v___y_782_;
v___y_765_ = v___x_790_;
goto v___jp_758_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_759_ = v___y_778_;
v___y_760_ = v___x_785_;
v___y_761_ = v___y_779_;
v___y_762_ = v___y_780_;
v___y_763_ = v___y_781_;
v___y_764_ = v___y_782_;
v___y_765_ = v___x_791_;
goto v___jp_758_;
}
}
v___jp_792_:
{
lean_object* v_ref_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_ref_794_ = lean_ctor_get(v___y_727_, 5);
v___x_795_ = l_Lean_SourceInfo_fromRef(v_ref_794_, v___y_793_);
v___x_796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
v___x_797_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_796_);
lean_inc(v___x_795_);
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
v___x_799_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_800_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_716_) == 0)
{
lean_object* v___x_801_; 
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_778_ = v___x_795_;
v___y_779_ = v___x_799_;
v___y_780_ = v___x_798_;
v___y_781_ = v___x_797_;
v___y_782_ = v___x_800_;
v___y_783_ = v___x_801_;
goto v___jp_777_;
}
else
{
lean_object* v_val_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_val_802_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_val_802_);
lean_dec_ref_known(v___y_716_, 1);
v___x_803_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_804_ = lean_array_push(v___x_803_, v_val_802_);
v___y_778_ = v___x_795_;
v___y_779_ = v___x_799_;
v___y_780_ = v___x_798_;
v___y_781_ = v___x_797_;
v___y_782_ = v___x_800_;
v___y_783_ = v___x_804_;
goto v___jp_777_;
}
}
v___jp_805_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_inc_ref(v___y_806_);
v___x_815_ = l_Array_append___redArg(v___y_806_, v___y_814_);
lean_dec_ref(v___y_814_);
lean_inc(v___y_808_);
lean_inc(v___y_809_);
v___x_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_816_, 0, v___y_809_);
lean_ctor_set(v___x_816_, 1, v___y_808_);
lean_ctor_set(v___x_816_, 2, v___x_815_);
v___x_817_ = l_Lean_Syntax_node6(v___y_809_, v___y_810_, v___y_813_, v___x_708_, v___y_812_, v___y_807_, v___y_811_, v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
v___jp_819_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_inc_ref(v___y_820_);
v___x_828_ = l_Array_append___redArg(v___y_820_, v___y_827_);
lean_dec_ref(v___y_827_);
lean_inc(v___y_822_);
lean_inc(v___y_823_);
v___x_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_829_, 0, v___y_823_);
lean_ctor_set(v___x_829_, 1, v___y_822_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
if (lean_obj_tag(v_loc_720_) == 1)
{
lean_object* v_val_830_; lean_object* v___x_831_; 
v_val_830_ = lean_ctor_get(v_loc_720_, 0);
lean_inc(v_val_830_);
lean_dec_ref_known(v_loc_720_, 1);
v___x_831_ = l_Array_mkArray1___redArg(v_val_830_);
v___y_806_ = v___y_820_;
v___y_807_ = v___y_821_;
v___y_808_ = v___y_822_;
v___y_809_ = v___y_823_;
v___y_810_ = v___y_824_;
v___y_811_ = v___x_829_;
v___y_812_ = v___y_825_;
v___y_813_ = v___y_826_;
v___y_814_ = v___x_831_;
goto v___jp_805_;
}
else
{
lean_object* v___x_832_; 
lean_dec(v_loc_720_);
v___x_832_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_806_ = v___y_820_;
v___y_807_ = v___y_821_;
v___y_808_ = v___y_822_;
v___y_809_ = v___y_823_;
v___y_810_ = v___y_824_;
v___y_811_ = v___x_829_;
v___y_812_ = v___y_825_;
v___y_813_ = v___y_826_;
v___y_814_ = v___x_832_;
goto v___jp_805_;
}
}
v___jp_833_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc_ref(v___y_834_);
v___x_841_ = l_Array_append___redArg(v___y_834_, v___y_840_);
lean_dec_ref(v___y_840_);
lean_inc(v___y_835_);
lean_inc(v___y_836_);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___y_836_);
lean_ctor_set(v___x_842_, 1, v___y_835_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
if (lean_obj_tag(v_args_710_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_val_843_ = lean_ctor_get(v_args_710_, 0);
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_836_, 3);
v___x_845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_845_, 0, v___y_836_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
lean_inc_ref(v___y_834_);
v___x_846_ = l_Array_append___redArg(v___y_834_, v_val_843_);
lean_inc(v___y_835_);
v___x_847_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_847_, 0, v___y_836_);
lean_ctor_set(v___x_847_, 1, v___y_835_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_849_, 0, v___y_836_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Array_mkArray3___redArg(v___x_845_, v___x_847_, v___x_849_);
v___y_820_ = v___y_834_;
v___y_821_ = v___x_842_;
v___y_822_ = v___y_835_;
v___y_823_ = v___y_836_;
v___y_824_ = v___y_837_;
v___y_825_ = v___y_838_;
v___y_826_ = v___y_839_;
v___y_827_ = v___x_850_;
goto v___jp_819_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_820_ = v___y_834_;
v___y_821_ = v___x_842_;
v___y_822_ = v___y_835_;
v___y_823_ = v___y_836_;
v___y_824_ = v___y_837_;
v___y_825_ = v___y_838_;
v___y_826_ = v___y_839_;
v___y_827_ = v___x_851_;
goto v___jp_819_;
}
}
v___jp_852_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_inc_ref(v___y_853_);
v___x_859_ = l_Array_append___redArg(v___y_853_, v___y_858_);
lean_dec_ref(v___y_858_);
lean_inc(v___y_854_);
lean_inc(v___y_855_);
v___x_860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_860_, 0, v___y_855_);
lean_ctor_set(v___x_860_, 1, v___y_854_);
lean_ctor_set(v___x_860_, 2, v___x_859_);
if (lean_obj_tag(v_only_711_) == 1)
{
lean_object* v_val_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_val_861_ = lean_ctor_get(v_only_711_, 0);
v___x_862_ = l_Lean_SourceInfo_fromRef(v_val_861_, v___x_712_);
v___x_863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Array_mkArray1___redArg(v___x_864_);
v___y_834_ = v___y_853_;
v___y_835_ = v___y_854_;
v___y_836_ = v___y_855_;
v___y_837_ = v___y_856_;
v___y_838_ = v___x_860_;
v___y_839_ = v___y_857_;
v___y_840_ = v___x_865_;
goto v___jp_833_;
}
else
{
lean_object* v___x_866_; 
v___x_866_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_834_ = v___y_853_;
v___y_835_ = v___y_854_;
v___y_836_ = v___y_855_;
v___y_837_ = v___y_856_;
v___y_838_ = v___x_860_;
v___y_839_ = v___y_857_;
v___y_840_ = v___x_866_;
goto v___jp_833_;
}
}
v___jp_867_:
{
if (lean_obj_tag(v_unfold_717_) == 0)
{
v___y_793_ = v___y_868_;
goto v___jp_792_;
}
else
{
lean_dec_ref_known(v_unfold_717_, 1);
if (v___x_718_ == 0)
{
v___y_793_ = v___x_718_;
goto v___jp_792_;
}
else
{
lean_object* v_ref_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_ref_869_ = lean_ctor_get(v___y_727_, 5);
v___x_870_ = l_Lean_SourceInfo_fromRef(v_ref_869_, v___y_868_);
v___x_871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__7));
v___x_872_ = l_Lean_Name_mkStr4(v___x_713_, v___x_714_, v___x_715_, v___x_871_);
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__8));
lean_inc(v___x_870_);
v___x_874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_870_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_876_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_716_) == 0)
{
lean_object* v___x_877_; 
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___y_853_ = v___x_876_;
v___y_854_ = v___x_875_;
v___y_855_ = v___x_870_;
v___y_856_ = v___x_872_;
v___y_857_ = v___x_874_;
v___y_858_ = v___x_877_;
goto v___jp_852_;
}
else
{
lean_object* v_val_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_val_878_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v___y_716_, 1);
v___x_879_ = lean_mk_empty_array_with_capacity(v___x_709_);
v___x_880_ = lean_array_push(v___x_879_, v_val_878_);
v___y_853_ = v___x_876_;
v___y_854_ = v___x_875_;
v___y_855_ = v___x_870_;
v___y_856_ = v___x_872_;
v___y_857_ = v___x_874_;
v___y_858_ = v___x_880_;
goto v___jp_852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(lean_object** _args){
lean_object* v___x_1019_ = _args[0];
lean_object* v___x_1020_ = _args[1];
lean_object* v_args_1021_ = _args[2];
lean_object* v_only_1022_ = _args[3];
lean_object* v___x_1023_ = _args[4];
lean_object* v___x_1024_ = _args[5];
lean_object* v___x_1025_ = _args[6];
lean_object* v___x_1026_ = _args[7];
lean_object* v___y_1027_ = _args[8];
lean_object* v_unfold_1028_ = _args[9];
lean_object* v___x_1029_ = _args[10];
lean_object* v_squeeze_1030_ = _args[11];
lean_object* v_loc_1031_ = _args[12];
lean_object* v___y_1032_ = _args[13];
lean_object* v___y_1033_ = _args[14];
lean_object* v___y_1034_ = _args[15];
lean_object* v___y_1035_ = _args[16];
lean_object* v___y_1036_ = _args[17];
lean_object* v___y_1037_ = _args[18];
lean_object* v___y_1038_ = _args[19];
lean_object* v___y_1039_ = _args[20];
lean_object* v___y_1040_ = _args[21];
_start:
{
uint8_t v___x_90434__boxed_1041_; uint8_t v___x_90439__boxed_1042_; lean_object* v_res_1043_; 
v___x_90434__boxed_1041_ = lean_unbox(v___x_1023_);
v___x_90439__boxed_1042_ = lean_unbox(v___x_1029_);
v_res_1043_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(v___x_1019_, v___x_1020_, v_args_1021_, v_only_1022_, v___x_90434__boxed_1041_, v___x_1024_, v___x_1025_, v___x_1026_, v___y_1027_, v_unfold_1028_, v___x_90439__boxed_1042_, v_squeeze_1030_, v_loc_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v_only_1022_);
lean_dec(v_args_1021_);
lean_dec(v___x_1020_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(lean_object* v_a_1044_, lean_object* v_trees_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; 
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
v___x_1055_ = lean_apply_9(v_a_1044_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, lean_box(0));
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_a_1056_);
lean_ctor_set(v___x_1060_, 1, v_trees_1045_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
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
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_trees_1045_);
v_a_1065_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1055_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1055_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(lean_object* v_a_1073_, lean_object* v_trees_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(v_a_1073_, v_trees_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1084_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__0));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__2));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(lean_object* v_a_1091_, lean_object* v_a_1092_, uint8_t v___x_1093_, uint8_t v___x_1094_, lean_object* v_a_1095_, lean_object* v_mvarCounter_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, uint8_t v_useReducible_1099_, uint8_t v___x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
lean_inc(v_a_1091_);
v___x_1110_ = l_Lean_MVarId_getType(v_a_1091_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_n(v_a_1111_, 2);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = l_Lean_mkIdent(v_a_1092_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_a_1111_);
v___x_1114_ = l_Lean_Elab_Term_elabTerm(v___x_1112_, v___x_1113_, v___x_1093_, v___x_1093_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___x_1149_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1149_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1094_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1290_; 
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1149_, 0);
lean_dec(v_unused_1291_);
v___x_1151_ = v___x_1149_;
v_isShared_1152_ = v_isSharedCheck_1290_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v___x_1149_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1290_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; 
lean_inc(v___y_1108_);
lean_inc_ref(v___y_1107_);
lean_inc(v___y_1106_);
lean_inc_ref(v___y_1105_);
lean_inc(v_a_1115_);
v___x_1153_ = lean_infer_type(v_a_1115_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; uint8_t v_____do__lift_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
if (v_useReducible_1099_ == 0)
{
lean_object* v___x_1174_; uint8_t v_foApprox_1175_; uint8_t v_ctxApprox_1176_; uint8_t v_quasiPatternApprox_1177_; uint8_t v_constApprox_1178_; uint8_t v_isDefEqStuckEx_1179_; uint8_t v_unificationHints_1180_; uint8_t v_proofIrrelevance_1181_; uint8_t v_offsetCnstrs_1182_; uint8_t v_transparency_1183_; uint8_t v_etaStruct_1184_; uint8_t v_univApprox_1185_; uint8_t v_iota_1186_; uint8_t v_beta_1187_; uint8_t v_proj_1188_; uint8_t v_zeta_1189_; uint8_t v_zetaDelta_1190_; uint8_t v_zetaUnused_1191_; uint8_t v_zetaHave_1192_; uint8_t v_canUnfoldPredicateConfig_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1224_; 
v___x_1174_ = l_Lean_Meta_Context_config(v___y_1105_);
v_foApprox_1175_ = lean_ctor_get_uint8(v___x_1174_, 0);
v_ctxApprox_1176_ = lean_ctor_get_uint8(v___x_1174_, 1);
v_quasiPatternApprox_1177_ = lean_ctor_get_uint8(v___x_1174_, 2);
v_constApprox_1178_ = lean_ctor_get_uint8(v___x_1174_, 3);
v_isDefEqStuckEx_1179_ = lean_ctor_get_uint8(v___x_1174_, 4);
v_unificationHints_1180_ = lean_ctor_get_uint8(v___x_1174_, 5);
v_proofIrrelevance_1181_ = lean_ctor_get_uint8(v___x_1174_, 6);
v_offsetCnstrs_1182_ = lean_ctor_get_uint8(v___x_1174_, 8);
v_transparency_1183_ = lean_ctor_get_uint8(v___x_1174_, 9);
v_etaStruct_1184_ = lean_ctor_get_uint8(v___x_1174_, 10);
v_univApprox_1185_ = lean_ctor_get_uint8(v___x_1174_, 11);
v_iota_1186_ = lean_ctor_get_uint8(v___x_1174_, 12);
v_beta_1187_ = lean_ctor_get_uint8(v___x_1174_, 13);
v_proj_1188_ = lean_ctor_get_uint8(v___x_1174_, 14);
v_zeta_1189_ = lean_ctor_get_uint8(v___x_1174_, 15);
v_zetaDelta_1190_ = lean_ctor_get_uint8(v___x_1174_, 16);
v_zetaUnused_1191_ = lean_ctor_get_uint8(v___x_1174_, 17);
v_zetaHave_1192_ = lean_ctor_get_uint8(v___x_1174_, 18);
v_canUnfoldPredicateConfig_1193_ = lean_ctor_get_uint8(v___x_1174_, 19);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1195_ = v___x_1174_;
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v___x_1174_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
uint8_t v_trackZetaDelta_1197_; lean_object* v_zetaDeltaSet_1198_; lean_object* v_lctx_1199_; lean_object* v_localInstances_1200_; lean_object* v_defEqCtx_x3f_1201_; lean_object* v_synthPendingDepth_1202_; lean_object* v_customCanUnfoldPredicate_x3f_1203_; uint8_t v_univApprox_1204_; uint8_t v_inTypeClassResolution_1205_; uint8_t v_cacheInferType_1206_; lean_object* v___x_1208_; 
v_trackZetaDelta_1197_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7);
v_zetaDeltaSet_1198_ = lean_ctor_get(v___y_1105_, 1);
v_lctx_1199_ = lean_ctor_get(v___y_1105_, 2);
v_localInstances_1200_ = lean_ctor_get(v___y_1105_, 3);
v_defEqCtx_x3f_1201_ = lean_ctor_get(v___y_1105_, 4);
v_synthPendingDepth_1202_ = lean_ctor_get(v___y_1105_, 5);
v_customCanUnfoldPredicate_x3f_1203_ = lean_ctor_get(v___y_1105_, 6);
v_univApprox_1204_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1205_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7 + 2);
v_cacheInferType_1206_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7 + 3);
if (v_isShared_1196_ == 0)
{
v___x_1208_ = v___x_1195_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 0, v_foApprox_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 1, v_ctxApprox_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 2, v_quasiPatternApprox_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 3, v_constApprox_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 4, v_isDefEqStuckEx_1179_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 5, v_unificationHints_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 6, v_proofIrrelevance_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 8, v_offsetCnstrs_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 9, v_transparency_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 10, v_etaStruct_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 11, v_univApprox_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 12, v_iota_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 13, v_beta_1187_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 14, v_proj_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 15, v_zeta_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 16, v_zetaDelta_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 17, v_zetaUnused_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 18, v_zetaHave_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, 19, v_canUnfoldPredicateConfig_1193_);
v___x_1208_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
uint64_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_ctor_set_uint8(v___x_1208_, 7, v___x_1100_);
v___x_1209_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1208_);
v___x_1210_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set_uint64(v___x_1210_, sizeof(void*)*1, v___x_1209_);
lean_inc(v_customCanUnfoldPredicate_x3f_1203_);
lean_inc(v_synthPendingDepth_1202_);
lean_inc(v_defEqCtx_x3f_1201_);
lean_inc_ref(v_localInstances_1200_);
lean_inc_ref(v_lctx_1199_);
lean_inc(v_zetaDeltaSet_1198_);
v___x_1211_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_zetaDeltaSet_1198_);
lean_ctor_set(v___x_1211_, 2, v_lctx_1199_);
lean_ctor_set(v___x_1211_, 3, v_localInstances_1200_);
lean_ctor_set(v___x_1211_, 4, v_defEqCtx_x3f_1201_);
lean_ctor_set(v___x_1211_, 5, v_synthPendingDepth_1202_);
lean_ctor_set(v___x_1211_, 6, v_customCanUnfoldPredicate_x3f_1203_);
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*7, v_trackZetaDelta_1197_);
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*7 + 1, v_univApprox_1204_);
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1205_);
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*7 + 3, v_cacheInferType_1206_);
lean_inc(v_a_1154_);
lean_inc(v_a_1111_);
v___x_1212_ = l_Lean_Meta_isExprDefEq(v_a_1111_, v_a_1154_, v___x_1211_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec_ref_known(v___x_1211_, 7);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; uint8_t v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
v_____do__lift_1156_ = v___x_1214_;
v___y_1157_ = v___y_1101_;
v___y_1158_ = v___y_1102_;
v___y_1159_ = v___y_1103_;
v___y_1160_ = v___y_1104_;
v___y_1161_ = v___y_1105_;
v___y_1162_ = v___y_1106_;
v___y_1163_ = v___y_1107_;
v___y_1164_ = v___y_1108_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_a_1154_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1115_);
lean_dec(v_a_1111_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___x_1098_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1091_);
v_a_1215_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1212_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
else
{
lean_object* v_keyedConfig_1225_; uint8_t v_trackZetaDelta_1226_; lean_object* v_zetaDeltaSet_1227_; lean_object* v_lctx_1228_; lean_object* v_localInstances_1229_; lean_object* v_defEqCtx_x3f_1230_; lean_object* v_synthPendingDepth_1231_; lean_object* v_customCanUnfoldPredicate_x3f_1232_; uint8_t v_univApprox_1233_; uint8_t v_inTypeClassResolution_1234_; uint8_t v_cacheInferType_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v_foApprox_1240_; uint8_t v_ctxApprox_1241_; uint8_t v_quasiPatternApprox_1242_; uint8_t v_constApprox_1243_; uint8_t v_isDefEqStuckEx_1244_; uint8_t v_unificationHints_1245_; uint8_t v_proofIrrelevance_1246_; uint8_t v_offsetCnstrs_1247_; uint8_t v_transparency_1248_; uint8_t v_etaStruct_1249_; uint8_t v_univApprox_1250_; uint8_t v_iota_1251_; uint8_t v_beta_1252_; uint8_t v_proj_1253_; uint8_t v_zeta_1254_; uint8_t v_zetaDelta_1255_; uint8_t v_zetaUnused_1256_; uint8_t v_zetaHave_1257_; uint8_t v_canUnfoldPredicateConfig_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1281_; 
v_keyedConfig_1225_ = lean_ctor_get(v___y_1105_, 0);
v_trackZetaDelta_1226_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7);
v_zetaDeltaSet_1227_ = lean_ctor_get(v___y_1105_, 1);
v_lctx_1228_ = lean_ctor_get(v___y_1105_, 2);
v_localInstances_1229_ = lean_ctor_get(v___y_1105_, 3);
v_defEqCtx_x3f_1230_ = lean_ctor_get(v___y_1105_, 4);
v_synthPendingDepth_1231_ = lean_ctor_get(v___y_1105_, 5);
v_customCanUnfoldPredicate_x3f_1232_ = lean_ctor_get(v___y_1105_, 6);
v_univApprox_1233_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1234_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7 + 2);
v_cacheInferType_1235_ = lean_ctor_get_uint8(v___y_1105_, sizeof(void*)*7 + 3);
v___x_1236_ = 2;
lean_inc_ref(v_keyedConfig_1225_);
v___x_1237_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1236_, v_keyedConfig_1225_);
lean_inc(v_customCanUnfoldPredicate_x3f_1232_);
lean_inc(v_synthPendingDepth_1231_);
lean_inc(v_defEqCtx_x3f_1230_);
lean_inc_ref(v_localInstances_1229_);
lean_inc_ref(v_lctx_1228_);
lean_inc(v_zetaDeltaSet_1227_);
v___x_1238_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_zetaDeltaSet_1227_);
lean_ctor_set(v___x_1238_, 2, v_lctx_1228_);
lean_ctor_set(v___x_1238_, 3, v_localInstances_1229_);
lean_ctor_set(v___x_1238_, 4, v_defEqCtx_x3f_1230_);
lean_ctor_set(v___x_1238_, 5, v_synthPendingDepth_1231_);
lean_ctor_set(v___x_1238_, 6, v_customCanUnfoldPredicate_x3f_1232_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*7, v_trackZetaDelta_1226_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*7 + 1, v_univApprox_1233_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1234_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*7 + 3, v_cacheInferType_1235_);
v___x_1239_ = l_Lean_Meta_Context_config(v___x_1238_);
lean_dec_ref_known(v___x_1238_, 7);
v_foApprox_1240_ = lean_ctor_get_uint8(v___x_1239_, 0);
v_ctxApprox_1241_ = lean_ctor_get_uint8(v___x_1239_, 1);
v_quasiPatternApprox_1242_ = lean_ctor_get_uint8(v___x_1239_, 2);
v_constApprox_1243_ = lean_ctor_get_uint8(v___x_1239_, 3);
v_isDefEqStuckEx_1244_ = lean_ctor_get_uint8(v___x_1239_, 4);
v_unificationHints_1245_ = lean_ctor_get_uint8(v___x_1239_, 5);
v_proofIrrelevance_1246_ = lean_ctor_get_uint8(v___x_1239_, 6);
v_offsetCnstrs_1247_ = lean_ctor_get_uint8(v___x_1239_, 8);
v_transparency_1248_ = lean_ctor_get_uint8(v___x_1239_, 9);
v_etaStruct_1249_ = lean_ctor_get_uint8(v___x_1239_, 10);
v_univApprox_1250_ = lean_ctor_get_uint8(v___x_1239_, 11);
v_iota_1251_ = lean_ctor_get_uint8(v___x_1239_, 12);
v_beta_1252_ = lean_ctor_get_uint8(v___x_1239_, 13);
v_proj_1253_ = lean_ctor_get_uint8(v___x_1239_, 14);
v_zeta_1254_ = lean_ctor_get_uint8(v___x_1239_, 15);
v_zetaDelta_1255_ = lean_ctor_get_uint8(v___x_1239_, 16);
v_zetaUnused_1256_ = lean_ctor_get_uint8(v___x_1239_, 17);
v_zetaHave_1257_ = lean_ctor_get_uint8(v___x_1239_, 18);
v_canUnfoldPredicateConfig_1258_ = lean_ctor_get_uint8(v___x_1239_, 19);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1260_ = v___x_1239_;
v_isShared_1261_ = v_isSharedCheck_1281_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v___x_1239_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1281_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 0, v_foApprox_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 1, v_ctxApprox_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 2, v_quasiPatternApprox_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 3, v_constApprox_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 4, v_isDefEqStuckEx_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 5, v_unificationHints_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 6, v_proofIrrelevance_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 8, v_offsetCnstrs_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 9, v_transparency_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 10, v_etaStruct_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 11, v_univApprox_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 12, v_iota_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 13, v_beta_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 14, v_proj_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 15, v_zeta_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 16, v_zetaDelta_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 17, v_zetaUnused_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 18, v_zetaHave_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, 19, v_canUnfoldPredicateConfig_1258_);
v___x_1263_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
uint64_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_ctor_set_uint8(v___x_1263_, 7, v___x_1100_);
v___x_1264_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set_uint64(v___x_1265_, sizeof(void*)*1, v___x_1264_);
lean_inc(v_customCanUnfoldPredicate_x3f_1232_);
lean_inc(v_synthPendingDepth_1231_);
lean_inc(v_defEqCtx_x3f_1230_);
lean_inc_ref(v_localInstances_1229_);
lean_inc_ref(v_lctx_1228_);
lean_inc(v_zetaDeltaSet_1227_);
v___x_1266_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_zetaDeltaSet_1227_);
lean_ctor_set(v___x_1266_, 2, v_lctx_1228_);
lean_ctor_set(v___x_1266_, 3, v_localInstances_1229_);
lean_ctor_set(v___x_1266_, 4, v_defEqCtx_x3f_1230_);
lean_ctor_set(v___x_1266_, 5, v_synthPendingDepth_1231_);
lean_ctor_set(v___x_1266_, 6, v_customCanUnfoldPredicate_x3f_1232_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*7, v_trackZetaDelta_1226_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*7 + 1, v_univApprox_1233_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1234_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*7 + 3, v_cacheInferType_1235_);
lean_inc(v_a_1154_);
lean_inc(v_a_1111_);
v___x_1267_ = l_Lean_Meta_isExprDefEq(v_a_1111_, v_a_1154_, v___x_1266_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec_ref_known(v___x_1266_, 7);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; uint8_t v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = lean_unbox(v_a_1268_);
lean_dec(v_a_1268_);
v_____do__lift_1156_ = v___x_1269_;
v___y_1157_ = v___y_1101_;
v___y_1158_ = v___y_1102_;
v___y_1159_ = v___y_1103_;
v___y_1160_ = v___y_1104_;
v___y_1161_ = v___y_1105_;
v___y_1162_ = v___y_1106_;
v___y_1163_ = v___y_1107_;
v___y_1164_ = v___y_1108_;
goto v___jp_1155_;
}
else
{
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1270_; uint8_t v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1271_ = lean_unbox(v_a_1270_);
lean_dec(v_a_1270_);
v_____do__lift_1156_ = v___x_1271_;
v___y_1157_ = v___y_1101_;
v___y_1158_ = v___y_1102_;
v___y_1159_ = v___y_1103_;
v___y_1160_ = v___y_1104_;
v___y_1161_ = v___y_1105_;
v___y_1162_ = v___y_1106_;
v___y_1163_ = v___y_1107_;
v___y_1164_ = v___y_1108_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_a_1154_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1115_);
lean_dec(v_a_1111_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___x_1098_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1091_);
v_a_1272_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1267_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1267_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
}
v___jp_1155_:
{
if (v_____do__lift_1156_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1165_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__1);
lean_inc_ref(v_a_1095_);
v___x_1166_ = l_Lean_indentExpr(v_a_1095_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___closed__3);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 1);
lean_ctor_set(v___x_1151_, 0, v___x_1169_);
v___x_1171_ = v___x_1151_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; 
lean_inc(v_a_1115_);
v___x_1172_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_1171_, v_a_1111_, v_a_1154_, v_a_1115_, v___x_1098_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec_ref(v___x_1171_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_dec_ref_known(v___x_1172_, 1);
v___y_1117_ = v___y_1157_;
v___y_1118_ = v___y_1158_;
v___y_1119_ = v___y_1159_;
v___y_1120_ = v___y_1160_;
v___y_1121_ = v___y_1161_;
v___y_1122_ = v___y_1162_;
v___y_1123_ = v___y_1163_;
v___y_1124_ = v___y_1164_;
goto v___jp_1116_;
}
else
{
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_a_1115_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1091_);
return v___x_1172_;
}
}
}
else
{
lean_dec(v_a_1154_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1111_);
lean_dec(v___x_1098_);
v___y_1117_ = v___y_1157_;
v___y_1118_ = v___y_1158_;
v___y_1119_ = v___y_1159_;
v___y_1120_ = v___y_1160_;
v___y_1121_ = v___y_1161_;
v___y_1122_ = v___y_1162_;
v___y_1123_ = v___y_1163_;
v___y_1124_ = v___y_1164_;
goto v___jp_1116_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_del_object(v___x_1151_);
lean_dec(v_a_1115_);
lean_dec(v_a_1111_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___x_1098_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1091_);
v_a_1282_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1153_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1153_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
else
{
lean_dec(v_a_1115_);
lean_dec(v_a_1111_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___x_1098_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1091_);
return v___x_1149_;
}
v___jp_1116_:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Meta_getMVars(v_a_1095_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(v_a_1126_, v_mvarCounter_1096_, v___y_1122_);
lean_dec(v_a_1126_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(v_a_1128_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v_a_1128_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref_known(v___x_1129_, 1);
v___x_1130_ = l_Lean_Elab_Tactic_pushGoal___redArg(v_a_1091_, v___y_1118_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = l_Lean_Name_mkStr1(v___x_1097_);
v___x_1132_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(v___x_1131_, v_a_1115_, v___x_1094_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v___x_1132_;
}
else
{
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_a_1115_);
lean_dec_ref(v___x_1097_);
return v___x_1130_;
}
}
else
{
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_a_1115_);
lean_dec_ref(v___x_1097_);
lean_dec(v_a_1091_);
return v___x_1129_;
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_a_1115_);
lean_dec_ref(v___x_1097_);
lean_dec(v_a_1091_);
v_a_1133_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1127_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1127_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_a_1115_);
lean_dec_ref(v___x_1097_);
lean_dec(v_a_1091_);
v_a_1141_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1125_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1125_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_a_1111_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___x_1098_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1091_);
v_a_1292_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1114_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1114_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___x_1098_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1092_);
lean_dec(v_a_1091_);
v_a_1300_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1110_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1110_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(lean_object** _args){
lean_object* v_a_1308_ = _args[0];
lean_object* v_a_1309_ = _args[1];
lean_object* v___x_1310_ = _args[2];
lean_object* v___x_1311_ = _args[3];
lean_object* v_a_1312_ = _args[4];
lean_object* v_mvarCounter_1313_ = _args[5];
lean_object* v___x_1314_ = _args[6];
lean_object* v___x_1315_ = _args[7];
lean_object* v_useReducible_1316_ = _args[8];
lean_object* v___x_1317_ = _args[9];
lean_object* v___y_1318_ = _args[10];
lean_object* v___y_1319_ = _args[11];
lean_object* v___y_1320_ = _args[12];
lean_object* v___y_1321_ = _args[13];
lean_object* v___y_1322_ = _args[14];
lean_object* v___y_1323_ = _args[15];
lean_object* v___y_1324_ = _args[16];
lean_object* v___y_1325_ = _args[17];
lean_object* v___y_1326_ = _args[18];
_start:
{
uint8_t v___x_91149__boxed_1327_; uint8_t v___x_91150__boxed_1328_; uint8_t v_useReducible_boxed_1329_; uint8_t v___x_91154__boxed_1330_; lean_object* v_res_1331_; 
v___x_91149__boxed_1327_ = lean_unbox(v___x_1310_);
v___x_91150__boxed_1328_ = lean_unbox(v___x_1311_);
v_useReducible_boxed_1329_ = lean_unbox(v_useReducible_1316_);
v___x_91154__boxed_1330_ = lean_unbox(v___x_1317_);
v_res_1331_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(v_a_1308_, v_a_1309_, v___x_91149__boxed_1327_, v___x_91150__boxed_1328_, v_a_1312_, v_mvarCounter_1313_, v___x_1314_, v___x_1315_, v_useReducible_boxed_1329_, v___x_91154__boxed_1330_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v_mvarCounter_1313_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(lean_object* v_a_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v_infoState_1343_; lean_object* v_env_1344_; lean_object* v_nextMacroScope_1345_; lean_object* v_ngen_1346_; lean_object* v_auxDeclNGen_1347_; lean_object* v_traceState_1348_; lean_object* v_cache_1349_; lean_object* v_messages_1350_; lean_object* v_snapshotTasks_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1372_; 
v___x_1342_ = lean_st_ref_take(v___y_1340_);
v_infoState_1343_ = lean_ctor_get(v___x_1342_, 7);
v_env_1344_ = lean_ctor_get(v___x_1342_, 0);
v_nextMacroScope_1345_ = lean_ctor_get(v___x_1342_, 1);
v_ngen_1346_ = lean_ctor_get(v___x_1342_, 2);
v_auxDeclNGen_1347_ = lean_ctor_get(v___x_1342_, 3);
v_traceState_1348_ = lean_ctor_get(v___x_1342_, 4);
v_cache_1349_ = lean_ctor_get(v___x_1342_, 5);
v_messages_1350_ = lean_ctor_get(v___x_1342_, 6);
v_snapshotTasks_1351_ = lean_ctor_get(v___x_1342_, 8);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1353_ = v___x_1342_;
v_isShared_1354_ = v_isSharedCheck_1372_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_snapshotTasks_1351_);
lean_inc(v_infoState_1343_);
lean_inc(v_messages_1350_);
lean_inc(v_cache_1349_);
lean_inc(v_traceState_1348_);
lean_inc(v_auxDeclNGen_1347_);
lean_inc(v_ngen_1346_);
lean_inc(v_nextMacroScope_1345_);
lean_inc(v_env_1344_);
lean_dec(v___x_1342_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1372_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v_enabled_1355_; lean_object* v_assignment_1356_; lean_object* v_lazyAssignment_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1370_; 
v_enabled_1355_ = lean_ctor_get_uint8(v_infoState_1343_, sizeof(void*)*3);
v_assignment_1356_ = lean_ctor_get(v_infoState_1343_, 0);
v_lazyAssignment_1357_ = lean_ctor_get(v_infoState_1343_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_infoState_1343_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v_infoState_1343_, 2);
lean_dec(v_unused_1371_);
v___x_1359_ = v_infoState_1343_;
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_lazyAssignment_1357_);
lean_inc(v_assignment_1356_);
lean_dec(v_infoState_1343_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 2, v_a_1332_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_assignment_1356_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_lazyAssignment_1357_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_a_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*3, v_enabled_1355_);
v___x_1362_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 7, v___x_1362_);
v___x_1364_ = v___x_1353_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_env_1344_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_nextMacroScope_1345_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_ngen_1346_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_auxDeclNGen_1347_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_traceState_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 5, v_cache_1349_);
lean_ctor_set(v_reuseFailAlloc_1368_, 6, v_messages_1350_);
lean_ctor_set(v_reuseFailAlloc_1368_, 7, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1368_, 8, v_snapshotTasks_1351_);
v___x_1364_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = lean_st_ref_put(v___y_1340_, v___x_1364_);
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(lean_object* v_a_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(v_a_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1383_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(lean_object* v_a_1384_, lean_object* v_x_1385_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
uint8_t v___x_1386_; 
v___x_1386_ = 0;
return v___x_1386_;
}
else
{
lean_object* v_key_1387_; lean_object* v_tail_1388_; uint8_t v___x_1389_; 
v_key_1387_ = lean_ctor_get(v_x_1385_, 0);
v_tail_1388_ = lean_ctor_get(v_x_1385_, 2);
v___x_1389_ = lean_expr_eqv(v_key_1387_, v_a_1384_);
if (v___x_1389_ == 0)
{
v_x_1385_ = v_tail_1388_;
goto _start;
}
else
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg___boxed(lean_object* v_a_1391_, lean_object* v_x_1392_){
_start:
{
uint8_t v_res_1393_; lean_object* v_r_1394_; 
v_res_1393_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1391_, v_x_1392_);
lean_dec(v_x_1392_);
lean_dec_ref(v_a_1391_);
v_r_1394_ = lean_box(v_res_1393_);
return v_r_1394_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(lean_object* v_m_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_buckets_1397_; lean_object* v___x_1398_; uint64_t v___x_1399_; uint64_t v___x_1400_; uint64_t v___x_1401_; uint64_t v_fold_1402_; uint64_t v___x_1403_; uint64_t v___x_1404_; uint64_t v___x_1405_; size_t v___x_1406_; size_t v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_buckets_1397_ = lean_ctor_get(v_m_1395_, 1);
v___x_1398_ = lean_array_get_size(v_buckets_1397_);
v___x_1399_ = l_Lean_Expr_hash(v_a_1396_);
v___x_1400_ = 32ULL;
v___x_1401_ = lean_uint64_shift_right(v___x_1399_, v___x_1400_);
v_fold_1402_ = lean_uint64_xor(v___x_1399_, v___x_1401_);
v___x_1403_ = 16ULL;
v___x_1404_ = lean_uint64_shift_right(v_fold_1402_, v___x_1403_);
v___x_1405_ = lean_uint64_xor(v_fold_1402_, v___x_1404_);
v___x_1406_ = lean_uint64_to_usize(v___x_1405_);
v___x_1407_ = lean_usize_of_nat(v___x_1398_);
v___x_1408_ = ((size_t)1ULL);
v___x_1409_ = lean_usize_sub(v___x_1407_, v___x_1408_);
v___x_1410_ = lean_usize_land(v___x_1406_, v___x_1409_);
v___x_1411_ = lean_array_uget_borrowed(v_buckets_1397_, v___x_1410_);
v___x_1412_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1396_, v___x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_m_1413_, lean_object* v_a_1414_){
_start:
{
uint8_t v_res_1415_; lean_object* v_r_1416_; 
v_res_1415_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_m_1413_, v_a_1414_);
lean_dec_ref(v_a_1414_);
lean_dec_ref(v_m_1413_);
v_r_1416_ = lean_box(v_res_1415_);
return v_r_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
if (lean_obj_tag(v_x_1418_) == 0)
{
return v_x_1417_;
}
else
{
lean_object* v_key_1419_; lean_object* v_value_1420_; lean_object* v_tail_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1444_; 
v_key_1419_ = lean_ctor_get(v_x_1418_, 0);
v_value_1420_ = lean_ctor_get(v_x_1418_, 1);
v_tail_1421_ = lean_ctor_get(v_x_1418_, 2);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_x_1418_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1423_ = v_x_1418_;
v_isShared_1424_ = v_isSharedCheck_1444_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_tail_1421_);
lean_inc(v_value_1420_);
lean_inc(v_key_1419_);
lean_dec(v_x_1418_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1444_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; uint64_t v___x_1426_; uint64_t v___x_1427_; uint64_t v___x_1428_; uint64_t v_fold_1429_; uint64_t v___x_1430_; uint64_t v___x_1431_; uint64_t v___x_1432_; size_t v___x_1433_; size_t v___x_1434_; size_t v___x_1435_; size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1425_ = lean_array_get_size(v_x_1417_);
v___x_1426_ = l_Lean_Expr_hash(v_key_1419_);
v___x_1427_ = 32ULL;
v___x_1428_ = lean_uint64_shift_right(v___x_1426_, v___x_1427_);
v_fold_1429_ = lean_uint64_xor(v___x_1426_, v___x_1428_);
v___x_1430_ = 16ULL;
v___x_1431_ = lean_uint64_shift_right(v_fold_1429_, v___x_1430_);
v___x_1432_ = lean_uint64_xor(v_fold_1429_, v___x_1431_);
v___x_1433_ = lean_uint64_to_usize(v___x_1432_);
v___x_1434_ = lean_usize_of_nat(v___x_1425_);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_sub(v___x_1434_, v___x_1435_);
v___x_1437_ = lean_usize_land(v___x_1433_, v___x_1436_);
v___x_1438_ = lean_array_uget_borrowed(v_x_1417_, v___x_1437_);
lean_inc(v___x_1438_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 2, v___x_1438_);
v___x_1440_ = v___x_1423_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_key_1419_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_value_1420_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_array_uset(v_x_1417_, v___x_1437_, v___x_1440_);
v_x_1417_ = v___x_1441_;
v_x_1418_ = v_tail_1421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(lean_object* v_i_1445_, lean_object* v_source_1446_, lean_object* v_target_1447_){
_start:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = lean_array_get_size(v_source_1446_);
v___x_1449_ = lean_nat_dec_lt(v_i_1445_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_dec_ref(v_source_1446_);
lean_dec(v_i_1445_);
return v_target_1447_;
}
else
{
lean_object* v_es_1450_; lean_object* v___x_1451_; lean_object* v_source_1452_; lean_object* v_target_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_es_1450_ = lean_array_fget(v_source_1446_, v_i_1445_);
v___x_1451_ = lean_box(0);
v_source_1452_ = lean_array_fset(v_source_1446_, v_i_1445_, v___x_1451_);
v_target_1453_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(v_target_1447_, v_es_1450_);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_i_1445_, v___x_1454_);
lean_dec(v_i_1445_);
v_i_1445_ = v___x_1455_;
v_source_1446_ = v_source_1452_;
v_target_1447_ = v_target_1453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(lean_object* v_data_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_nbuckets_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1458_ = lean_array_get_size(v_data_1457_);
v___x_1459_ = lean_unsigned_to_nat(2u);
v_nbuckets_1460_ = lean_nat_mul(v___x_1458_, v___x_1459_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_mk_array(v_nbuckets_1460_, v___x_1462_);
v___x_1464_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(v___x_1461_, v_data_1457_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(lean_object* v_m_1465_, lean_object* v_a_1466_, lean_object* v_b_1467_){
_start:
{
lean_object* v_size_1468_; lean_object* v_buckets_1469_; lean_object* v___x_1470_; uint64_t v___x_1471_; uint64_t v___x_1472_; uint64_t v___x_1473_; uint64_t v_fold_1474_; uint64_t v___x_1475_; uint64_t v___x_1476_; uint64_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; lean_object* v_bkt_1483_; uint8_t v___x_1484_; 
v_size_1468_ = lean_ctor_get(v_m_1465_, 0);
v_buckets_1469_ = lean_ctor_get(v_m_1465_, 1);
v___x_1470_ = lean_array_get_size(v_buckets_1469_);
v___x_1471_ = l_Lean_Expr_hash(v_a_1466_);
v___x_1472_ = 32ULL;
v___x_1473_ = lean_uint64_shift_right(v___x_1471_, v___x_1472_);
v_fold_1474_ = lean_uint64_xor(v___x_1471_, v___x_1473_);
v___x_1475_ = 16ULL;
v___x_1476_ = lean_uint64_shift_right(v_fold_1474_, v___x_1475_);
v___x_1477_ = lean_uint64_xor(v_fold_1474_, v___x_1476_);
v___x_1478_ = lean_uint64_to_usize(v___x_1477_);
v___x_1479_ = lean_usize_of_nat(v___x_1470_);
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_sub(v___x_1479_, v___x_1480_);
v___x_1482_ = lean_usize_land(v___x_1478_, v___x_1481_);
v_bkt_1483_ = lean_array_uget_borrowed(v_buckets_1469_, v___x_1482_);
v___x_1484_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_1466_, v_bkt_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1505_; 
lean_inc_ref(v_buckets_1469_);
lean_inc(v_size_1468_);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_m_1465_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1506_ = lean_ctor_get(v_m_1465_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_m_1465_, 0);
lean_dec(v_unused_1507_);
v___x_1486_ = v_m_1465_;
v_isShared_1487_ = v_isSharedCheck_1505_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_m_1465_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1505_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v_size_x27_1489_; lean_object* v___x_1490_; lean_object* v_buckets_x27_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1488_ = lean_unsigned_to_nat(1u);
v_size_x27_1489_ = lean_nat_add(v_size_1468_, v___x_1488_);
lean_dec(v_size_1468_);
lean_inc(v_bkt_1483_);
v___x_1490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1466_);
lean_ctor_set(v___x_1490_, 1, v_b_1467_);
lean_ctor_set(v___x_1490_, 2, v_bkt_1483_);
v_buckets_x27_1491_ = lean_array_uset(v_buckets_1469_, v___x_1482_, v___x_1490_);
v___x_1492_ = lean_unsigned_to_nat(4u);
v___x_1493_ = lean_nat_mul(v_size_x27_1489_, v___x_1492_);
v___x_1494_ = lean_unsigned_to_nat(3u);
v___x_1495_ = lean_nat_div(v___x_1493_, v___x_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_array_get_size(v_buckets_x27_1491_);
v___x_1497_ = lean_nat_dec_le(v___x_1495_, v___x_1496_);
lean_dec(v___x_1495_);
if (v___x_1497_ == 0)
{
lean_object* v_val_1498_; lean_object* v___x_1500_; 
v_val_1498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(v_buckets_x27_1491_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v_val_1498_);
lean_ctor_set(v___x_1486_, 0, v_size_x27_1489_);
v___x_1500_ = v___x_1486_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_size_x27_1489_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_val_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
else
{
lean_object* v___x_1503_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v_buckets_x27_1491_);
lean_ctor_set(v___x_1486_, 0, v_size_x27_1489_);
v___x_1503_ = v___x_1486_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_size_x27_1489_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_buckets_x27_1491_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_dec(v_b_1467_);
lean_dec_ref(v_a_1466_);
return v_m_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(lean_object* v_mvarId_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v_mctx_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1512_ = lean_st_ref_get(v___y_1510_);
v_mctx_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc_ref(v_mctx_1513_);
lean_dec(v___x_1512_);
v___x_1514_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1513_, v_mvarId_1508_);
lean_dec_ref(v_mctx_1513_);
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___y_1509_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg___boxed(lean_object* v_mvarId_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec(v_mvarId_1518_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(lean_object* v_mvarId_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v_mctx_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1527_ = lean_st_ref_get(v___y_1525_);
v_mctx_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_ref(v_mctx_1528_);
lean_dec(v___x_1527_);
v___x_1529_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_1528_, v_mvarId_1523_);
lean_dec_ref(v_mctx_1528_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___y_1524_);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg___boxed(lean_object* v_mvarId_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec(v_mvarId_1533_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(lean_object* v_mvarId_1542_, lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_d_1555_; lean_object* v_b_1556_; lean_object* v___y_1557_; uint8_t v___x_1563_; 
v___x_1563_ = l_Lean_Expr_hasExprMVar(v_e_1543_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec_ref(v_e_1543_);
v___x_1564_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v_a_1544_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_a_1544_, v_e_1543_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_box(0);
lean_inc_ref(v_e_1543_);
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_1544_, v_e_1543_, v___x_1568_);
switch(lean_obj_tag(v_e_1543_))
{
case 11:
{
lean_object* v_struct_1570_; 
v_struct_1570_ = lean_ctor_get(v_e_1543_, 2);
lean_inc_ref(v_struct_1570_);
lean_dec_ref_known(v_e_1543_, 3);
v_e_1543_ = v_struct_1570_;
v_a_1544_ = v___x_1569_;
goto _start;
}
case 7:
{
lean_object* v_binderType_1572_; lean_object* v_body_1573_; 
v_binderType_1572_ = lean_ctor_get(v_e_1543_, 1);
lean_inc_ref(v_binderType_1572_);
v_body_1573_ = lean_ctor_get(v_e_1543_, 2);
lean_inc_ref(v_body_1573_);
lean_dec_ref_known(v_e_1543_, 3);
v_d_1555_ = v_binderType_1572_;
v_b_1556_ = v_body_1573_;
v___y_1557_ = v___x_1569_;
goto v___jp_1554_;
}
case 6:
{
lean_object* v_binderType_1574_; lean_object* v_body_1575_; 
v_binderType_1574_ = lean_ctor_get(v_e_1543_, 1);
lean_inc_ref(v_binderType_1574_);
v_body_1575_ = lean_ctor_get(v_e_1543_, 2);
lean_inc_ref(v_body_1575_);
lean_dec_ref_known(v_e_1543_, 3);
v_d_1555_ = v_binderType_1574_;
v_b_1556_ = v_body_1575_;
v___y_1557_ = v___x_1569_;
goto v___jp_1554_;
}
case 8:
{
lean_object* v_type_1576_; lean_object* v_value_1577_; lean_object* v_body_1578_; lean_object* v___x_1579_; 
v_type_1576_ = lean_ctor_get(v_e_1543_, 1);
lean_inc_ref(v_type_1576_);
v_value_1577_ = lean_ctor_get(v_e_1543_, 2);
lean_inc_ref(v_value_1577_);
v_body_1578_ = lean_ctor_get(v_e_1543_, 3);
lean_inc_ref(v_body_1578_);
lean_dec_ref_known(v_e_1543_, 4);
v___x_1579_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1542_, v_type_1576_, v___x_1569_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v_fst_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
v_fst_1581_ = lean_ctor_get(v_a_1580_, 0);
if (lean_obj_tag(v_fst_1581_) == 0)
{
lean_dec(v_a_1580_);
lean_dec_ref(v_body_1578_);
lean_dec_ref(v_value_1577_);
return v___x_1579_;
}
else
{
lean_object* v_snd_1582_; lean_object* v___x_1583_; 
lean_dec_ref_known(v___x_1579_, 1);
v_snd_1582_ = lean_ctor_get(v_a_1580_, 1);
lean_inc(v_snd_1582_);
lean_dec(v_a_1580_);
v___x_1583_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1542_, v_value_1577_, v_snd_1582_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v_fst_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
v_fst_1585_ = lean_ctor_get(v_a_1584_, 0);
if (lean_obj_tag(v_fst_1585_) == 0)
{
lean_dec(v_a_1584_);
lean_dec_ref(v_body_1578_);
return v___x_1583_;
}
else
{
lean_object* v_snd_1586_; 
lean_dec_ref_known(v___x_1583_, 1);
v_snd_1586_ = lean_ctor_get(v_a_1584_, 1);
lean_inc(v_snd_1586_);
lean_dec(v_a_1584_);
v_e_1543_ = v_body_1578_;
v_a_1544_ = v_snd_1586_;
goto _start;
}
}
else
{
lean_dec_ref(v_body_1578_);
return v___x_1583_;
}
}
}
else
{
lean_dec_ref(v_body_1578_);
lean_dec_ref(v_value_1577_);
return v___x_1579_;
}
}
case 10:
{
lean_object* v_expr_1588_; 
v_expr_1588_ = lean_ctor_get(v_e_1543_, 1);
lean_inc_ref(v_expr_1588_);
lean_dec_ref_known(v_e_1543_, 2);
v_e_1543_ = v_expr_1588_;
v_a_1544_ = v___x_1569_;
goto _start;
}
case 5:
{
lean_object* v_fn_1590_; lean_object* v_arg_1591_; lean_object* v___x_1592_; 
v_fn_1590_ = lean_ctor_get(v_e_1543_, 0);
lean_inc_ref(v_fn_1590_);
v_arg_1591_ = lean_ctor_get(v_e_1543_, 1);
lean_inc_ref(v_arg_1591_);
lean_dec_ref_known(v_e_1543_, 2);
v___x_1592_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1542_, v_fn_1590_, v___x_1569_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v_fst_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
v_fst_1594_ = lean_ctor_get(v_a_1593_, 0);
if (lean_obj_tag(v_fst_1594_) == 0)
{
lean_dec(v_a_1593_);
lean_dec_ref(v_arg_1591_);
return v___x_1592_;
}
else
{
lean_object* v_snd_1595_; 
lean_dec_ref_known(v___x_1592_, 1);
v_snd_1595_ = lean_ctor_get(v_a_1593_, 1);
lean_inc(v_snd_1595_);
lean_dec(v_a_1593_);
v_e_1543_ = v_arg_1591_;
v_a_1544_ = v_snd_1595_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1591_);
return v___x_1592_;
}
}
case 2:
{
lean_object* v_mvarId_1597_; lean_object* v___x_1598_; 
v_mvarId_1597_ = lean_ctor_get(v_e_1543_, 0);
lean_inc(v_mvarId_1597_);
lean_dec_ref_known(v_e_1543_, 1);
v___x_1598_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_1542_, v_mvarId_1597_, v___x_1569_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1598_;
}
default: 
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref(v_e_1543_);
v___x_1599_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v___x_1569_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref(v_e_1543_);
v___x_1602_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_a_1544_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
v___jp_1554_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1542_, v_d_1555_, v___y_1557_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v_fst_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
v_fst_1560_ = lean_ctor_get(v_a_1559_, 0);
if (lean_obj_tag(v_fst_1560_) == 0)
{
lean_dec(v_a_1559_);
lean_dec_ref(v_b_1556_);
return v___x_1558_;
}
else
{
lean_object* v_snd_1561_; 
lean_dec_ref_known(v___x_1558_, 1);
v_snd_1561_ = lean_ctor_get(v_a_1559_, 1);
lean_inc(v_snd_1561_);
lean_dec(v_a_1559_);
v_e_1543_ = v_b_1556_;
v_a_1544_ = v_snd_1561_;
goto _start;
}
}
else
{
lean_dec_ref(v_b_1556_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(lean_object* v_mvarId_1605_, lean_object* v_mvarId_x27_1606_, lean_object* v_a_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = l_Lean_instBEqMVarId_beq(v_mvarId_1605_, v_mvarId_x27_1606_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_x27_1606_, v_a_1607_, v___y_1613_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1702_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1702_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1702_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_fst_1623_; 
v_fst_1623_ = lean_ctor_get(v_a_1619_, 0);
lean_inc(v_fst_1623_);
if (lean_obj_tag(v_fst_1623_) == 0)
{
lean_object* v_snd_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_mvarId_x27_1606_);
v_snd_1624_ = lean_ctor_get(v_a_1619_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_a_1619_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v_a_1619_, 0);
lean_dec(v_unused_1643_);
v___x_1626_ = v_a_1619_;
v_isShared_1627_ = v_isSharedCheck_1642_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snd_1624_);
lean_dec(v_a_1619_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1642_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1641_; 
v_a_1628_ = lean_ctor_get(v_fst_1623_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_fst_1623_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1630_ = v_fst_1623_;
v_isShared_1631_ = v_isSharedCheck_1641_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v_fst_1623_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1641_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1633_);
v___x_1635_ = v___x_1626_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_snd_1624_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1635_);
v___x_1637_ = v___x_1621_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
else
{
lean_object* v_a_1644_; 
lean_del_object(v___x_1621_);
v_a_1644_ = lean_ctor_get(v_fst_1623_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v_fst_1623_, 1);
if (lean_obj_tag(v_a_1644_) == 0)
{
lean_object* v_snd_1645_; lean_object* v___x_1646_; 
v_snd_1645_ = lean_ctor_get(v_a_1619_, 1);
lean_inc(v_snd_1645_);
lean_dec(v_a_1619_);
v___x_1646_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_x27_1606_, v_snd_1645_, v___y_1613_);
lean_dec(v_mvarId_x27_1606_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1690_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1690_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1690_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fst_1651_; 
v_fst_1651_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_fst_1651_);
if (lean_obj_tag(v_fst_1651_) == 0)
{
lean_object* v_snd_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1670_; 
v_snd_1652_ = lean_ctor_get(v_a_1647_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_a_1647_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_a_1647_, 0);
lean_dec(v_unused_1671_);
v___x_1654_ = v_a_1647_;
v_isShared_1655_ = v_isSharedCheck_1670_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_snd_1652_);
lean_dec(v_a_1647_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1670_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1669_; 
v_a_1656_ = lean_ctor_get(v_fst_1651_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_fst_1651_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1658_ = v_fst_1651_;
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v_fst_1651_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1661_);
v___x_1663_ = v___x_1654_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_snd_1652_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1663_);
v___x_1665_ = v___x_1649_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
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
lean_object* v_a_1672_; 
v_a_1672_ = lean_ctor_get(v_fst_1651_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v_fst_1651_, 1);
if (lean_obj_tag(v_a_1672_) == 0)
{
lean_object* v_snd_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1684_; 
v_snd_1673_ = lean_ctor_get(v_a_1647_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_a_1647_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_a_1647_, 0);
lean_dec(v_unused_1685_);
v___x_1675_ = v_a_1647_;
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_snd_1673_);
lean_dec(v_a_1647_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__0));
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_snd_1673_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1679_);
v___x_1681_ = v___x_1649_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_val_1686_; lean_object* v_snd_1687_; lean_object* v_mvarIdPending_1688_; 
lean_del_object(v___x_1649_);
v_val_1686_ = lean_ctor_get(v_a_1672_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v_a_1672_, 1);
v_snd_1687_ = lean_ctor_get(v_a_1647_, 1);
lean_inc(v_snd_1687_);
lean_dec(v_a_1647_);
v_mvarIdPending_1688_ = lean_ctor_get(v_val_1686_, 1);
lean_inc(v_mvarIdPending_1688_);
lean_dec(v_val_1686_);
v_mvarId_x27_1606_ = v_mvarIdPending_1688_;
v_a_1607_ = v_snd_1687_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1646_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1646_);
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
else
{
lean_object* v_snd_1699_; lean_object* v_val_1700_; lean_object* v___x_1701_; 
lean_dec(v_mvarId_x27_1606_);
v_snd_1699_ = lean_ctor_get(v_a_1619_, 1);
lean_inc(v_snd_1699_);
lean_dec(v_a_1619_);
v_val_1700_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v_a_1644_, 1);
v___x_1701_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1605_, v_val_1700_, v_snd_1699_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_mvarId_x27_1606_);
v_a_1703_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1618_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1618_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v_mvarId_x27_1606_);
v___x_1711_ = ((lean_object*)(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___closed__1));
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
lean_ctor_set(v___x_1712_, 1, v_a_1607_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___boxed(lean_object* v_mvarId_1714_, lean_object* v_mvarId_x27_1715_, lean_object* v_a_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(v_mvarId_1714_, v_mvarId_x27_1715_, v_a_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v_mvarId_1714_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(lean_object* v_mvarId_1727_, lean_object* v_e_1728_, lean_object* v_a_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1727_, v_e_1728_, v_a_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v_mvarId_1727_);
return v_res_1739_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_unsigned_to_nat(16u);
v___x_1742_ = lean_mk_array(v___x_1741_, v___x_1740_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v___x_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(lean_object* v_mvarId_1746_, lean_object* v_e_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = l_Lean_Expr_hasExprMVar(v_e_1747_);
if (v___x_1757_ == 0)
{
uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec_ref(v_e_1747_);
v___x_1758_ = 1;
v___x_1759_ = lean_box(v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_obj_once(&l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1, &l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once, _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
v___x_1762_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_1746_, v_e_1747_, v___x_1761_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1777_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1777_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1777_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_fst_1767_; 
v_fst_1767_ = lean_ctor_get(v_a_1763_, 0);
lean_inc(v_fst_1767_);
lean_dec(v_a_1763_);
if (lean_obj_tag(v_fst_1767_) == 0)
{
uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec_ref_known(v_fst_1767_, 1);
v___x_1768_ = 0;
v___x_1769_ = lean_box(v___x_1768_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1769_);
v___x_1771_ = v___x_1765_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
lean_dec_ref_known(v_fst_1767_, 1);
v___x_1773_ = lean_box(v___x_1757_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1773_);
v___x_1775_ = v___x_1765_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_a_1778_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1762_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1762_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(lean_object* v_mvarId_1786_, lean_object* v_e_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_1786_, v_e_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_mvarId_1786_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(lean_object* v___y_1798_, lean_object* v_mkInfoTree_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v_a_1807_, lean_object* v_a_x3f_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v_infoState_1811_; lean_object* v_trees_1812_; lean_object* v___x_1813_; 
v___x_1810_ = lean_st_ref_get(v___y_1798_);
v_infoState_1811_ = lean_ctor_get(v___x_1810_, 7);
lean_inc_ref(v_infoState_1811_);
lean_dec(v___x_1810_);
v_trees_1812_ = lean_ctor_get(v_infoState_1811_, 2);
lean_inc_ref(v_trees_1812_);
lean_dec_ref(v_infoState_1811_);
lean_inc(v___y_1798_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
lean_inc(v___y_1801_);
lean_inc_ref(v___y_1800_);
v___x_1813_ = lean_apply_10(v_mkInfoTree_1799_, v_trees_1812_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1798_, lean_box(0));
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1852_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1852_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1852_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v_infoState_1819_; lean_object* v_env_1820_; lean_object* v_nextMacroScope_1821_; lean_object* v_ngen_1822_; lean_object* v_auxDeclNGen_1823_; lean_object* v_traceState_1824_; lean_object* v_cache_1825_; lean_object* v_messages_1826_; lean_object* v_snapshotTasks_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1851_; 
v___x_1818_ = lean_st_ref_take(v___y_1798_);
v_infoState_1819_ = lean_ctor_get(v___x_1818_, 7);
v_env_1820_ = lean_ctor_get(v___x_1818_, 0);
v_nextMacroScope_1821_ = lean_ctor_get(v___x_1818_, 1);
v_ngen_1822_ = lean_ctor_get(v___x_1818_, 2);
v_auxDeclNGen_1823_ = lean_ctor_get(v___x_1818_, 3);
v_traceState_1824_ = lean_ctor_get(v___x_1818_, 4);
v_cache_1825_ = lean_ctor_get(v___x_1818_, 5);
v_messages_1826_ = lean_ctor_get(v___x_1818_, 6);
v_snapshotTasks_1827_ = lean_ctor_get(v___x_1818_, 8);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1829_ = v___x_1818_;
v_isShared_1830_ = v_isSharedCheck_1851_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snapshotTasks_1827_);
lean_inc(v_infoState_1819_);
lean_inc(v_messages_1826_);
lean_inc(v_cache_1825_);
lean_inc(v_traceState_1824_);
lean_inc(v_auxDeclNGen_1823_);
lean_inc(v_ngen_1822_);
lean_inc(v_nextMacroScope_1821_);
lean_inc(v_env_1820_);
lean_dec(v___x_1818_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1851_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
uint8_t v_enabled_1831_; lean_object* v_assignment_1832_; lean_object* v_lazyAssignment_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1849_; 
v_enabled_1831_ = lean_ctor_get_uint8(v_infoState_1819_, sizeof(void*)*3);
v_assignment_1832_ = lean_ctor_get(v_infoState_1819_, 0);
v_lazyAssignment_1833_ = lean_ctor_get(v_infoState_1819_, 1);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_infoState_1819_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_infoState_1819_, 2);
lean_dec(v_unused_1850_);
v___x_1835_ = v_infoState_1819_;
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_lazyAssignment_1833_);
lean_inc(v_assignment_1832_);
lean_dec(v_infoState_1819_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = l_Lean_PersistentArray_push___redArg(v_a_1807_, v_a_1814_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 2, v___x_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_assignment_1832_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_lazyAssignment_1833_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v___x_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1848_, sizeof(void*)*3, v_enabled_1831_);
v___x_1839_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 7, v___x_1839_);
v___x_1841_ = v___x_1829_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_env_1820_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_nextMacroScope_1821_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_ngen_1822_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_auxDeclNGen_1823_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_traceState_1824_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_cache_1825_);
lean_ctor_set(v_reuseFailAlloc_1847_, 6, v_messages_1826_);
lean_ctor_set(v_reuseFailAlloc_1847_, 7, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1847_, 8, v_snapshotTasks_1827_);
v___x_1841_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1842_ = lean_st_ref_put(v___y_1798_, v___x_1841_);
v___x_1843_ = lean_box(0);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1843_);
v___x_1845_ = v___x_1816_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_a_1807_);
v_a_1853_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1813_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1813_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0___boxed(lean_object* v___y_1861_, lean_object* v_mkInfoTree_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v_a_1870_, lean_object* v_a_x3f_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1861_, v_mkInfoTree_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v_a_1870_, v_a_x3f_1871_);
lean_dec(v_a_x3f_1871_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1861_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(lean_object* v_x_1874_, lean_object* v_mkInfoTree_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; lean_object* v_infoState_1886_; uint8_t v_enabled_1887_; 
v___x_1885_ = lean_st_ref_get(v___y_1883_);
v_infoState_1886_ = lean_ctor_get(v___x_1885_, 7);
lean_inc_ref(v_infoState_1886_);
lean_dec(v___x_1885_);
v_enabled_1887_ = lean_ctor_get_uint8(v_infoState_1886_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1886_);
if (v_enabled_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_dec_ref(v_mkInfoTree_1875_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1878_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
v___x_1888_ = lean_apply_9(v_x_1874_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, lean_box(0));
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; lean_object* v_a_1890_; lean_object* v_r_1891_; 
v___x_1889_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_1883_);
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
lean_inc(v___y_1879_);
lean_inc_ref(v___y_1878_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
v_r_1891_ = lean_apply_9(v_x_1874_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, lean_box(0));
if (lean_obj_tag(v_r_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1916_; 
v_a_1892_ = lean_ctor_get(v_r_1891_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_r_1891_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1894_ = v_r_1891_;
v_isShared_1895_ = v_isSharedCheck_1916_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v_r_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1916_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
lean_inc(v_a_1892_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 1);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1883_, v_mkInfoTree_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v_a_1890_, v___x_1897_);
lean_dec_ref(v___x_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v___x_1898_, 0);
lean_dec(v_unused_1906_);
v___x_1900_ = v___x_1898_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_dec(v___x_1898_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v_a_1892_);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1892_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_a_1892_);
v_a_1907_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1898_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1898_);
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
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v_r_1891_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v_r_1891_, 1);
v___x_1918_ = lean_box(0);
v___x_1919_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___lam__0(v___y_1883_, v_mkInfoTree_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v_a_1890_, v___x_1918_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1919_, 0);
lean_dec(v_unused_1927_);
v___x_1921_ = v___x_1919_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_dec(v___x_1919_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 1);
lean_ctor_set(v___x_1921_, 0, v_a_1917_);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1917_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1917_);
v_a_1928_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(lean_object* v_x_1936_, lean_object* v_mkInfoTree_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_1936_, v_mkInfoTree_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(lean_object* v_msg_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_ref_1954_; lean_object* v___x_1955_; lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1964_; 
v_ref_1954_ = lean_ctor_get(v___y_1951_, 5);
v___x_1955_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__2(v_msg_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_inc(v_ref_1954_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_ref_1954_);
lean_ctor_set(v___x_1960_, 1, v_a_1956_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 1);
lean_ctor_set(v___x_1958_, 0, v___x_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(lean_object* v_x_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_){
_start:
{
lean_object* v_ks_1976_; lean_object* v_vs_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2001_; 
v_ks_1976_ = lean_ctor_get(v_x_1972_, 0);
v_vs_1977_ = lean_ctor_get(v_x_1972_, 1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_x_1972_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1979_ = v_x_1972_;
v_isShared_1980_ = v_isSharedCheck_2001_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_vs_1977_);
lean_inc(v_ks_1976_);
lean_dec(v_x_1972_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2001_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_array_get_size(v_ks_1976_);
v___x_1982_ = lean_nat_dec_lt(v_x_1973_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
lean_dec(v_x_1973_);
v___x_1983_ = lean_array_push(v_ks_1976_, v_x_1974_);
v___x_1984_ = lean_array_push(v_vs_1977_, v_x_1975_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1984_);
lean_ctor_set(v___x_1979_, 0, v___x_1983_);
v___x_1986_ = v___x_1979_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
else
{
lean_object* v_k_x27_1988_; uint8_t v___x_1989_; 
v_k_x27_1988_ = lean_array_fget_borrowed(v_ks_1976_, v_x_1973_);
v___x_1989_ = l_Lean_instBEqMVarId_beq(v_x_1974_, v_k_x27_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1991_; 
if (v_isShared_1980_ == 0)
{
v___x_1991_ = v___x_1979_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_ks_1976_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_vs_1977_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_add(v_x_1973_, v___x_1992_);
lean_dec(v_x_1973_);
v_x_1972_ = v___x_1991_;
v_x_1973_ = v___x_1993_;
goto _start;
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1996_ = lean_array_fset(v_ks_1976_, v_x_1973_, v_x_1974_);
v___x_1997_ = lean_array_fset(v_vs_1977_, v_x_1973_, v_x_1975_);
lean_dec(v_x_1973_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1997_);
lean_ctor_set(v___x_1979_, 0, v___x_1996_);
v___x_1999_ = v___x_1979_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___x_1997_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(lean_object* v_n_2002_, lean_object* v_k_2003_, lean_object* v_v_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(v_n_2002_, v___x_2005_, v_k_2003_, v_v_2004_);
return v___x_2006_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(lean_object* v_x_2008_, size_t v_x_2009_, size_t v_x_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
lean_object* v_es_2013_; size_t v___x_2014_; size_t v___x_2015_; lean_object* v_j_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_es_2013_ = lean_ctor_get(v_x_2008_, 0);
v___x_2014_ = ((size_t)31ULL);
v___x_2015_ = lean_usize_land(v_x_2009_, v___x_2014_);
v_j_2016_ = lean_usize_to_nat(v___x_2015_);
v___x_2017_ = lean_array_get_size(v_es_2013_);
v___x_2018_ = lean_nat_dec_lt(v_j_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_dec(v_j_2016_);
lean_dec(v_x_2012_);
lean_dec(v_x_2011_);
return v_x_2008_;
}
else
{
lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2057_; 
lean_inc_ref(v_es_2013_);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_x_2008_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_x_2008_, 0);
lean_dec(v_unused_2058_);
v___x_2020_ = v_x_2008_;
v_isShared_2021_ = v_isSharedCheck_2057_;
goto v_resetjp_2019_;
}
else
{
lean_dec(v_x_2008_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2057_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_v_2022_; lean_object* v___x_2023_; lean_object* v_xs_x27_2024_; lean_object* v___y_2026_; 
v_v_2022_ = lean_array_fget(v_es_2013_, v_j_2016_);
v___x_2023_ = lean_box(0);
v_xs_x27_2024_ = lean_array_fset(v_es_2013_, v_j_2016_, v___x_2023_);
switch(lean_obj_tag(v_v_2022_))
{
case 0:
{
lean_object* v_key_2031_; lean_object* v_val_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2042_; 
v_key_2031_ = lean_ctor_get(v_v_2022_, 0);
v_val_2032_ = lean_ctor_get(v_v_2022_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_v_2022_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2034_ = v_v_2022_;
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_val_2032_);
lean_inc(v_key_2031_);
lean_dec(v_v_2022_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
uint8_t v___x_2036_; 
v___x_2036_ = l_Lean_instBEqMVarId_beq(v_x_2011_, v_key_2031_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_del_object(v___x_2034_);
v___x_2037_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2031_, v_val_2032_, v_x_2011_, v_x_2012_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___y_2026_ = v___x_2038_;
goto v___jp_2025_;
}
else
{
lean_object* v___x_2040_; 
lean_dec(v_val_2032_);
lean_dec(v_key_2031_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_x_2012_);
lean_ctor_set(v___x_2034_, 0, v_x_2011_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_x_2011_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_x_2012_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v___y_2026_ = v___x_2040_;
goto v___jp_2025_;
}
}
}
}
case 1:
{
lean_object* v_node_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2055_; 
v_node_2043_ = lean_ctor_get(v_v_2022_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_v_2022_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2045_ = v_v_2022_;
v_isShared_2046_ = v_isSharedCheck_2055_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_node_2043_);
lean_dec(v_v_2022_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2055_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
size_t v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2047_ = ((size_t)5ULL);
v___x_2048_ = lean_usize_shift_right(v_x_2009_, v___x_2047_);
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_x_2010_, v___x_2049_);
v___x_2051_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_node_2043_, v___x_2048_, v___x_2050_, v_x_2011_, v_x_2012_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2051_);
v___x_2053_ = v___x_2045_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
v___y_2026_ = v___x_2053_;
goto v___jp_2025_;
}
}
}
default: 
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_x_2011_);
lean_ctor_set(v___x_2056_, 1, v_x_2012_);
v___y_2026_ = v___x_2056_;
goto v___jp_2025_;
}
}
v___jp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_array_fset(v_xs_x27_2024_, v_j_2016_, v___y_2026_);
lean_dec(v_j_2016_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2027_);
v___x_2029_ = v___x_2020_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v_ks_2059_; lean_object* v_vs_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2078_; 
v_ks_2059_ = lean_ctor_get(v_x_2008_, 0);
v_vs_2060_ = lean_ctor_get(v_x_2008_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_x_2008_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2062_ = v_x_2008_;
v_isShared_2063_ = v_isSharedCheck_2078_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_vs_2060_);
lean_inc(v_ks_2059_);
lean_dec(v_x_2008_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2078_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_ks_2059_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_vs_2060_);
v___x_2065_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v_newNode_2066_; size_t v___x_2067_; uint8_t v___x_2068_; 
v_newNode_2066_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(v___x_2065_, v_x_2011_, v_x_2012_);
v___x_2067_ = ((size_t)7ULL);
v___x_2068_ = lean_usize_dec_le(v___x_2067_, v_x_2010_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2069_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2066_);
v___x_2070_ = lean_unsigned_to_nat(4u);
v___x_2071_ = lean_nat_dec_lt(v___x_2069_, v___x_2070_);
lean_dec(v___x_2069_);
if (v___x_2071_ == 0)
{
lean_object* v_ks_2072_; lean_object* v_vs_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_ks_2072_ = lean_ctor_get(v_newNode_2066_, 0);
lean_inc_ref(v_ks_2072_);
v_vs_2073_ = lean_ctor_get(v_newNode_2066_, 1);
lean_inc_ref(v_vs_2073_);
lean_dec_ref(v_newNode_2066_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___closed__0);
v___x_2076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_x_2010_, v_ks_2072_, v_vs_2073_, v___x_2074_, v___x_2075_);
lean_dec_ref(v_vs_2073_);
lean_dec_ref(v_ks_2072_);
return v___x_2076_;
}
else
{
return v_newNode_2066_;
}
}
else
{
return v_newNode_2066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(size_t v_depth_2079_, lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_i_2082_, lean_object* v_entries_2083_){
_start:
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = lean_array_get_size(v_keys_2080_);
v___x_2085_ = lean_nat_dec_lt(v_i_2082_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec(v_i_2082_);
return v_entries_2083_;
}
else
{
lean_object* v_k_2086_; lean_object* v_v_2087_; uint64_t v___x_2088_; size_t v_h_2089_; size_t v___x_2090_; lean_object* v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; size_t v_h_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_k_2086_ = lean_array_fget_borrowed(v_keys_2080_, v_i_2082_);
v_v_2087_ = lean_array_fget_borrowed(v_vals_2081_, v_i_2082_);
v___x_2088_ = l_Lean_instHashableMVarId_hash(v_k_2086_);
v_h_2089_ = lean_uint64_to_usize(v___x_2088_);
v___x_2090_ = ((size_t)5ULL);
v___x_2091_ = lean_unsigned_to_nat(1u);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_sub(v_depth_2079_, v___x_2092_);
v___x_2094_ = lean_usize_mul(v___x_2090_, v___x_2093_);
v_h_2095_ = lean_usize_shift_right(v_h_2089_, v___x_2094_);
v___x_2096_ = lean_nat_add(v_i_2082_, v___x_2091_);
lean_dec(v_i_2082_);
lean_inc(v_v_2087_);
lean_inc(v_k_2086_);
v___x_2097_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_entries_2083_, v_h_2095_, v_depth_2079_, v_k_2086_, v_v_2087_);
v_i_2082_ = v___x_2096_;
v_entries_2083_ = v___x_2097_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg___boxed(lean_object* v_depth_2099_, lean_object* v_keys_2100_, lean_object* v_vals_2101_, lean_object* v_i_2102_, lean_object* v_entries_2103_){
_start:
{
size_t v_depth_boxed_2104_; lean_object* v_res_2105_; 
v_depth_boxed_2104_ = lean_unbox_usize(v_depth_2099_);
lean_dec(v_depth_2099_);
v_res_2105_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_depth_boxed_2104_, v_keys_2100_, v_vals_2101_, v_i_2102_, v_entries_2103_);
lean_dec_ref(v_vals_2101_);
lean_dec_ref(v_keys_2100_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg___boxed(lean_object* v_x_2106_, lean_object* v_x_2107_, lean_object* v_x_2108_, lean_object* v_x_2109_, lean_object* v_x_2110_){
_start:
{
size_t v_x_92630__boxed_2111_; size_t v_x_92631__boxed_2112_; lean_object* v_res_2113_; 
v_x_92630__boxed_2111_ = lean_unbox_usize(v_x_2107_);
lean_dec(v_x_2107_);
v_x_92631__boxed_2112_ = lean_unbox_usize(v_x_2108_);
lean_dec(v_x_2108_);
v_res_2113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_2106_, v_x_92630__boxed_2111_, v_x_92631__boxed_2112_, v_x_2109_, v_x_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_){
_start:
{
uint64_t v___x_2117_; size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2117_ = l_Lean_instHashableMVarId_hash(v_x_2115_);
v___x_2118_ = lean_uint64_to_usize(v___x_2117_);
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_2114_, v___x_2118_, v___x_2119_, v_x_2115_, v_x_2116_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(lean_object* v_mvarId_2121_, lean_object* v_val_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v_mctx_2126_; lean_object* v_cache_2127_; lean_object* v_zetaDeltaFVarIds_2128_; lean_object* v_postponed_2129_; lean_object* v_diag_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2159_; 
v___x_2125_ = lean_st_ref_take(v___y_2123_);
v_mctx_2126_ = lean_ctor_get(v___x_2125_, 0);
v_cache_2127_ = lean_ctor_get(v___x_2125_, 1);
v_zetaDeltaFVarIds_2128_ = lean_ctor_get(v___x_2125_, 2);
v_postponed_2129_ = lean_ctor_get(v___x_2125_, 3);
v_diag_2130_ = lean_ctor_get(v___x_2125_, 4);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2132_ = v___x_2125_;
v_isShared_2133_ = v_isSharedCheck_2159_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_diag_2130_);
lean_inc(v_postponed_2129_);
lean_inc(v_zetaDeltaFVarIds_2128_);
lean_inc(v_cache_2127_);
lean_inc(v_mctx_2126_);
lean_dec(v___x_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2159_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_depth_2134_; lean_object* v_levelAssignDepth_2135_; lean_object* v_lmvarCounter_2136_; lean_object* v_mvarCounter_2137_; lean_object* v_lDecls_2138_; lean_object* v_decls_2139_; lean_object* v_userNames_2140_; lean_object* v_lAssignment_2141_; lean_object* v_eAssignment_2142_; lean_object* v_dAssignment_2143_; lean_object* v_instanceTypedMVars_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2158_; 
v_depth_2134_ = lean_ctor_get(v_mctx_2126_, 0);
v_levelAssignDepth_2135_ = lean_ctor_get(v_mctx_2126_, 1);
v_lmvarCounter_2136_ = lean_ctor_get(v_mctx_2126_, 2);
v_mvarCounter_2137_ = lean_ctor_get(v_mctx_2126_, 3);
v_lDecls_2138_ = lean_ctor_get(v_mctx_2126_, 4);
v_decls_2139_ = lean_ctor_get(v_mctx_2126_, 5);
v_userNames_2140_ = lean_ctor_get(v_mctx_2126_, 6);
v_lAssignment_2141_ = lean_ctor_get(v_mctx_2126_, 7);
v_eAssignment_2142_ = lean_ctor_get(v_mctx_2126_, 8);
v_dAssignment_2143_ = lean_ctor_get(v_mctx_2126_, 9);
v_instanceTypedMVars_2144_ = lean_ctor_get(v_mctx_2126_, 10);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_mctx_2126_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2146_ = v_mctx_2126_;
v_isShared_2147_ = v_isSharedCheck_2158_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_instanceTypedMVars_2144_);
lean_inc(v_dAssignment_2143_);
lean_inc(v_eAssignment_2142_);
lean_inc(v_lAssignment_2141_);
lean_inc(v_userNames_2140_);
lean_inc(v_decls_2139_);
lean_inc(v_lDecls_2138_);
lean_inc(v_mvarCounter_2137_);
lean_inc(v_lmvarCounter_2136_);
lean_inc(v_levelAssignDepth_2135_);
lean_inc(v_depth_2134_);
lean_dec(v_mctx_2126_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2158_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_2142_, v_mvarId_2121_, v_val_2122_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 8, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_depth_2134_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_levelAssignDepth_2135_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_lmvarCounter_2136_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_mvarCounter_2137_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_lDecls_2138_);
lean_ctor_set(v_reuseFailAlloc_2157_, 5, v_decls_2139_);
lean_ctor_set(v_reuseFailAlloc_2157_, 6, v_userNames_2140_);
lean_ctor_set(v_reuseFailAlloc_2157_, 7, v_lAssignment_2141_);
lean_ctor_set(v_reuseFailAlloc_2157_, 8, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2157_, 9, v_dAssignment_2143_);
lean_ctor_set(v_reuseFailAlloc_2157_, 10, v_instanceTypedMVars_2144_);
v___x_2150_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2150_);
v___x_2152_ = v___x_2132_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_cache_2127_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_zetaDeltaFVarIds_2128_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_postponed_2129_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_diag_2130_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_st_ref_put(v___y_2123_, v___x_2152_);
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(lean_object* v_mvarId_2160_, lean_object* v_val_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_2160_, v_val_2161_, v___y_2162_);
lean_dec(v___y_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(lean_object* v_o_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; lean_object* v_env_2169_; lean_object* v___x_2170_; lean_object* v_toEnvExtension_2171_; lean_object* v_asyncMode_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_merged_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2184_; 
v___x_2168_ = lean_st_ref_get(v___y_2166_);
v_env_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_ref(v_env_2169_);
lean_dec(v___x_2168_);
v___x_2170_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2171_ = lean_ctor_get(v___x_2170_, 0);
v_asyncMode_2172_ = lean_ctor_get(v_toEnvExtension_2171_, 2);
v___x_2173_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2174_ = lean_box(0);
v___x_2175_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2173_, v___x_2170_, v_env_2169_, v_asyncMode_2172_, v___x_2174_);
v_merged_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v___x_2175_, 1);
lean_dec(v_unused_2185_);
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_merged_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v_merged_2176_);
lean_ctor_set(v___x_2178_, 0, v_o_2165_);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_o_2165_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_merged_2176_);
v___x_2181_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(lean_object* v_o_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_2186_, v___y_2187_);
lean_dec(v___y_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_options_2199_; lean_object* v___x_2200_; 
v_options_2199_ = lean_ctor_get(v___y_2196_, 2);
lean_inc_ref(v_options_2199_);
v___x_2200_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_2199_, v___y_2197_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2210_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__7));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(lean_object* v_usingArg_2226_, lean_object* v_snd_2227_, uint8_t v___x_2228_, uint8_t v___x_2229_, lean_object* v___x_2230_, uint8_t v_useReducible_2231_, uint8_t v___x_2232_, lean_object* v___x_2233_, lean_object* v___x_2234_, lean_object* v_simprocs_2235_, lean_object* v_discharge_x3f_2236_, lean_object* v_snd_2237_, lean_object* v___f_2238_, lean_object* v___x_2239_, lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v___x_2242_, lean_object* v___f_2243_, lean_object* v_a_2244_, lean_object* v___x_2245_, lean_object* v___f_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; 
if (lean_obj_tag(v_usingArg_2226_) == 1)
{
lean_object* v_val_2470_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___x_2522_; lean_object* v_infoState_2523_; uint8_t v_enabled_2524_; 
v_val_2470_ = lean_ctor_get(v_usingArg_2226_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v_usingArg_2226_, 1);
v___x_2522_ = lean_st_ref_get(v___y_2254_);
v_infoState_2523_ = lean_ctor_get(v___x_2522_, 7);
lean_inc_ref(v_infoState_2523_);
lean_dec(v___x_2522_);
v_enabled_2524_ = lean_ctor_get_uint8(v_infoState_2523_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2523_);
if (v_enabled_2524_ == 0)
{
lean_dec_ref(v___f_2246_);
v___y_2472_ = v___y_2247_;
v___y_2473_ = v___y_2248_;
v___y_2474_ = v___y_2249_;
v___y_2475_ = v___y_2250_;
v___y_2476_ = v___y_2251_;
v___y_2477_ = v___y_2252_;
v___y_2478_ = v___y_2253_;
v___y_2479_ = v___y_2254_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2525_; lean_object* v_a_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; 
v___x_2525_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___y_2254_);
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v___x_2525_);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed), 10, 1);
lean_closure_set(v___f_2527_, 0, v_a_2526_);
v___x_2528_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___f_2527_, v___f_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_dec_ref_known(v___x_2528_, 1);
v___y_2472_ = v___y_2247_;
v___y_2473_ = v___y_2248_;
v___y_2474_ = v___y_2249_;
v___y_2475_ = v___y_2250_;
v___y_2476_ = v___y_2251_;
v___y_2477_ = v___y_2252_;
v___y_2478_ = v___y_2253_;
v___y_2479_ = v___y_2254_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_val_2470_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
v___jp_2471_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_st_ref_get(v___y_2477_);
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Lean_Elab_Tactic_elabTerm(v_val_2470_, v___x_2481_, v___x_2228_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc_n(v_a_2483_, 2);
lean_dec_ref_known(v___x_2482_, 1);
v___x_2484_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_2227_, v_a_2483_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_mctx_2485_; lean_object* v_a_2486_; uint8_t v___x_2487_; 
v_mctx_2485_ = lean_ctor_get(v___x_2480_, 0);
lean_inc_ref(v_mctx_2485_);
lean_dec(v___x_2480_);
v_a_2486_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2484_, 1);
v___x_2487_ = lean_unbox(v_a_2486_);
lean_dec(v_a_2486_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec_ref(v_mctx_2485_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
v___x_2488_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__6);
v___x_2489_ = l_Lean_indentExpr(v_a_2483_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__8);
v___x_2492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = l_Lean_Expr_mvar___override(v_snd_2227_);
v___x_2494_ = l_Lean_MessageData_ofExpr(v___x_2493_);
v___x_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2492_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v___x_2495_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v_mvarCounter_2505_; 
v_mvarCounter_2505_ = lean_ctor_get(v_mctx_2485_, 3);
lean_inc(v_mvarCounter_2505_);
lean_dec_ref(v_mctx_2485_);
lean_inc(v_a_2483_);
v___y_2321_ = v_mvarCounter_2505_;
v___y_2322_ = v_a_2483_;
v___y_2323_ = v___x_2481_;
v___y_2324_ = v_a_2483_;
v___y_2325_ = v___x_2481_;
v___y_2326_ = v___y_2472_;
v___y_2327_ = v___y_2473_;
v___y_2328_ = v___y_2474_;
v___y_2329_ = v___y_2475_;
v___y_2330_ = v___y_2476_;
v___y_2331_ = v___y_2477_;
v___y_2332_ = v___y_2478_;
v___y_2333_ = v___y_2479_;
goto v___jp_2320_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2483_);
lean_dec(v___x_2480_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2506_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2484_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2484_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v___x_2480_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2514_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2482_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2482_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
else
{
lean_object* v_lctx_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v___f_2246_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v___x_2230_);
lean_dec(v_usingArg_2226_);
v_lctx_2537_ = lean_ctor_get(v___y_2251_, 2);
v___x_2538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__10));
v___x_2539_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2537_, v___x_2538_);
if (lean_obj_tag(v___x_2539_) == 1)
{
lean_object* v_val_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_val_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___x_2541_ = l_Lean_LocalDecl_fvarId(v_val_2540_);
lean_dec(v_val_2540_);
v___x_2542_ = lean_mk_empty_array_with_capacity(v___x_2233_);
v___x_2543_ = lean_array_push(v___x_2542_, v___x_2541_);
lean_inc_ref(v_snd_2237_);
v___x_2544_ = l_Lean_Meta_simpGoal(v_snd_2227_, v___x_2234_, v_simprocs_2235_, v_discharge_x3f_2236_, v___x_2229_, v___x_2543_, v_snd_2237_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2573_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2573_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2573_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_fst_2549_; 
v_fst_2549_ = lean_ctor_get(v_a_2545_, 0);
if (lean_obj_tag(v_fst_2549_) == 1)
{
lean_object* v_val_2550_; lean_object* v_snd_2551_; lean_object* v_snd_2552_; lean_object* v___x_2553_; 
lean_del_object(v___x_2547_);
lean_dec_ref(v_snd_2237_);
v_val_2550_ = lean_ctor_get(v_fst_2549_, 0);
lean_inc(v_val_2550_);
v_snd_2551_ = lean_ctor_get(v_a_2545_, 1);
lean_inc(v_snd_2551_);
lean_dec(v_a_2545_);
v_snd_2552_ = lean_ctor_get(v_val_2550_, 1);
lean_inc(v_snd_2552_);
lean_dec(v_val_2550_);
v___x_2553_ = l_Lean_MVarId_assumption(v_snd_2552_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2560_ == 0)
{
lean_object* v_unused_2561_; 
v_unused_2561_ = lean_ctor_get(v___x_2553_, 0);
lean_dec(v_unused_2561_);
v___x_2555_ = v___x_2553_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_dec(v___x_2553_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_snd_2551_);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_snd_2551_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec(v_snd_2551_);
v_a_2562_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2553_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2553_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v___x_2571_; 
lean_dec(v_a_2545_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_snd_2237_);
v___x_2571_ = v___x_2547_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_snd_2237_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_snd_2237_);
v_a_2574_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2544_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2544_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v___x_2582_; 
lean_dec(v___x_2539_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
v___x_2582_ = l_Lean_MVarId_assumption(v_snd_2227_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v___x_2582_, 0);
lean_dec(v_unused_2590_);
v___x_2584_ = v___x_2582_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_dec(v___x_2582_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v_snd_2237_);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_snd_2237_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_snd_2237_);
v_a_2591_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2582_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2582_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
v___jp_2256_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v___x_2260_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_2227_, v___y_2257_, v___y_2259_);
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
lean_ctor_set(v___x_2262_, 0, v___y_2258_);
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___y_2258_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
v___jp_2269_:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Core_mkFreshUserName(v___y_2276_, v___y_2279_, v___y_2277_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc_n(v_a_2287_, 2);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l_Lean_MVarId_rename(v___y_2281_, v___y_2285_, v_a_2287_, v___y_2275_, v___y_2273_, v___y_2279_, v___y_2277_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc_n(v_a_2289_, 2);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = lean_box(v___x_2228_);
v___x_2291_ = lean_box(v___x_2229_);
v___x_2292_ = lean_box(v_useReducible_2231_);
v___x_2293_ = lean_box(v___x_2232_);
v___f_2294_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed), 19, 10);
lean_closure_set(v___f_2294_, 0, v_a_2289_);
lean_closure_set(v___f_2294_, 1, v_a_2287_);
lean_closure_set(v___f_2294_, 2, v___x_2290_);
lean_closure_set(v___f_2294_, 3, v___x_2291_);
lean_closure_set(v___f_2294_, 4, v___y_2272_);
lean_closure_set(v___f_2294_, 5, v___y_2270_);
lean_closure_set(v___f_2294_, 6, v___x_2230_);
lean_closure_set(v___f_2294_, 7, v___y_2271_);
lean_closure_set(v___f_2294_, 8, v___x_2292_);
lean_closure_set(v___f_2294_, 9, v___x_2293_);
v___x_2295_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_a_2289_, v___f_2294_, v___y_2284_, v___y_2283_, v___y_2278_, v___y_2280_, v___y_2275_, v___y_2273_, v___y_2279_, v___y_2277_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_dec_ref_known(v___x_2295_, 1);
v___y_2257_ = v___y_2274_;
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2273_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v___y_2282_);
lean_dec_ref(v___y_2274_);
lean_dec(v_snd_2227_);
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_a_2287_);
lean_dec_ref(v___y_2282_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2304_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2288_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2288_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2312_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2286_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2286_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
v___jp_2320_:
{
lean_object* v___x_2334_; 
lean_inc(v_snd_2227_);
v___x_2334_ = l_Lean_MVarId_getType(v_snd_2227_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
lean_inc(v_snd_2227_);
v___x_2336_ = l_Lean_MVarId_getTag(v_snd_2227_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2335_, v_a_2337_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l_Lean_Expr_mvarId_x21(v_a_2339_);
v___x_2341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1));
lean_inc_ref(v___y_2324_);
v___x_2342_ = l_Lean_MVarId_note(v___x_2340_, v___x_2341_, v___y_2324_, v___y_2325_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v_fst_2344_; lean_object* v_snd_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v_fst_2344_ = lean_ctor_get(v_a_2343_, 0);
lean_inc_n(v_fst_2344_, 2);
v_snd_2345_ = lean_ctor_get(v_a_2343_, 1);
lean_inc(v_snd_2345_);
lean_dec(v_a_2343_);
v___x_2346_ = lean_mk_empty_array_with_capacity(v___x_2233_);
v___x_2347_ = lean_array_push(v___x_2346_, v_fst_2344_);
v___x_2348_ = l_Lean_Meta_simpGoal(v_snd_2345_, v___x_2234_, v_simprocs_2235_, v_discharge_x3f_2236_, v___x_2229_, v___x_2347_, v_snd_2237_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v_fst_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v_fst_2350_ = lean_ctor_get(v_a_2349_, 0);
if (lean_obj_tag(v_fst_2350_) == 0)
{
lean_object* v_snd_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_fst_2344_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___x_2230_);
v_snd_2351_ = lean_ctor_get(v_a_2349_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_a_2349_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; 
v_unused_2422_ = lean_ctor_get(v_a_2349_, 0);
lean_dec(v_unused_2422_);
v___x_2353_ = v_a_2349_;
v_isShared_2354_ = v_isSharedCheck_2421_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_snd_2351_);
lean_dec(v_a_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2421_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v_a_2356_; uint8_t v___x_2357_; 
v___x_2355_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2356_);
lean_dec(v_a_2356_);
if (v___x_2357_ == 0)
{
lean_del_object(v___x_2353_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
v___y_2257_ = v_a_2339_;
v___y_2258_ = v_snd_2351_;
v___y_2259_ = v___y_2331_;
goto v___jp_2256_;
}
else
{
if (lean_obj_tag(v___y_2324_) == 1)
{
lean_object* v_fvarId_2358_; lean_object* v_lctx_2359_; lean_object* v___x_2360_; 
v_fvarId_2358_ = lean_ctor_get(v___y_2324_, 0);
lean_inc(v_fvarId_2358_);
lean_dec_ref_known(v___y_2324_, 1);
v_lctx_2359_ = lean_ctor_get(v___y_2330_, 2);
lean_inc_ref(v_lctx_2359_);
v___x_2360_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(v_lctx_2359_, v_fvarId_2358_);
if (lean_obj_tag(v___x_2360_) == 1)
{
lean_object* v_val_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2420_; 
v_val_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2420_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_val_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2420_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; 
lean_inc_ref(v___f_2238_);
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
v___x_2365_ = lean_apply_9(v___f_2238_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, lean_box(0));
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
v___x_2367_ = lean_apply_9(v___f_2238_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, lean_box(0));
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v_ref_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc_n(v_a_2368_, 2);
lean_dec_ref_known(v___x_2367_, 1);
v_ref_2369_ = lean_ctor_get(v___y_2332_, 5);
v___x_2370_ = l_Lean_mkIdent(v_val_2361_);
lean_inc(v_a_2366_);
v___x_2371_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2239_, v___x_2370_);
v___x_2372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2));
lean_inc_ref(v___x_2242_);
lean_inc_ref(v___x_2241_);
lean_inc_ref(v___x_2240_);
v___x_2373_ = l_Lean_Name_mkStr4(v___x_2240_, v___x_2241_, v___x_2242_, v___x_2372_);
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3));
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 2);
lean_ctor_set(v___x_2353_, 1, v___x_2374_);
lean_ctor_set(v___x_2353_, 0, v_a_2368_);
v___x_2376_ = v___x_2353_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2368_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2377_ = l_Lean_Syntax_node1(v_a_2366_, v___x_2373_, v___x_2371_);
v___x_2378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4));
v___x_2379_ = l_Lean_Name_mkStr4(v___x_2240_, v___x_2241_, v___x_2242_, v___x_2378_);
v___x_2380_ = l_Lean_Syntax_node2(v_a_2368_, v___x_2379_, v___x_2376_, v___x_2377_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2380_);
v___x_2382_ = v___x_2363_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; 
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
v___x_2383_ = lean_apply_10(v___f_2243_, v___x_2382_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, lean_box(0));
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
lean_inc(v_ref_2369_);
v___x_2385_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2244_, v_ref_2369_, v_a_2384_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_dec_ref_known(v___x_2385_, 1);
v___y_2257_ = v_a_2339_;
v___y_2258_ = v_snd_2351_;
v___y_2259_ = v___y_2331_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_snd_2351_);
lean_dec(v_a_2339_);
lean_dec(v_snd_2227_);
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_snd_2351_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2244_);
lean_dec(v_snd_2227_);
v_a_2394_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2383_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2383_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_2366_);
lean_del_object(v___x_2363_);
lean_dec(v_val_2361_);
lean_del_object(v___x_2353_);
lean_dec(v_snd_2351_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec(v_snd_2227_);
v_a_2404_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2367_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2367_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_del_object(v___x_2363_);
lean_dec(v_val_2361_);
lean_del_object(v___x_2353_);
lean_dec(v_snd_2351_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec(v_snd_2227_);
v_a_2412_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2365_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2365_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
else
{
lean_dec(v___x_2360_);
lean_del_object(v___x_2353_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
v___y_2257_ = v_a_2339_;
v___y_2258_ = v_snd_2351_;
v___y_2259_ = v___y_2331_;
goto v___jp_2256_;
}
}
else
{
lean_del_object(v___x_2353_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
v___y_2257_ = v_a_2339_;
v___y_2258_ = v_snd_2351_;
v___y_2259_ = v___y_2331_;
goto v___jp_2256_;
}
}
}
}
else
{
lean_object* v_val_2423_; lean_object* v_snd_2424_; lean_object* v_fst_2425_; lean_object* v_snd_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
lean_dec_ref(v___y_2324_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
v_val_2423_ = lean_ctor_get(v_fst_2350_, 0);
lean_inc(v_val_2423_);
v_snd_2424_ = lean_ctor_get(v_a_2349_, 1);
lean_inc(v_snd_2424_);
lean_dec(v_a_2349_);
v_fst_2425_ = lean_ctor_get(v_val_2423_, 0);
lean_inc(v_fst_2425_);
v_snd_2426_ = lean_ctor_get(v_val_2423_, 1);
lean_inc(v_snd_2426_);
lean_dec(v_val_2423_);
v___x_2427_ = lean_array_get_size(v_fst_2425_);
v___x_2428_ = lean_nat_dec_lt(v___x_2245_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_dec(v_fst_2425_);
v___y_2270_ = v___y_2321_;
v___y_2271_ = v___y_2323_;
v___y_2272_ = v___y_2322_;
v___y_2273_ = v___y_2331_;
v___y_2274_ = v_a_2339_;
v___y_2275_ = v___y_2330_;
v___y_2276_ = v___x_2341_;
v___y_2277_ = v___y_2333_;
v___y_2278_ = v___y_2328_;
v___y_2279_ = v___y_2332_;
v___y_2280_ = v___y_2329_;
v___y_2281_ = v_snd_2426_;
v___y_2282_ = v_snd_2424_;
v___y_2283_ = v___y_2327_;
v___y_2284_ = v___y_2326_;
v___y_2285_ = v_fst_2344_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2429_; 
lean_dec(v_fst_2344_);
v___x_2429_ = lean_array_fget(v_fst_2425_, v___x_2245_);
lean_dec(v_fst_2425_);
v___y_2270_ = v___y_2321_;
v___y_2271_ = v___y_2323_;
v___y_2272_ = v___y_2322_;
v___y_2273_ = v___y_2331_;
v___y_2274_ = v_a_2339_;
v___y_2275_ = v___y_2330_;
v___y_2276_ = v___x_2341_;
v___y_2277_ = v___y_2333_;
v___y_2278_ = v___y_2328_;
v___y_2279_ = v___y_2332_;
v___y_2280_ = v___y_2329_;
v___y_2281_ = v_snd_2426_;
v___y_2282_ = v_snd_2424_;
v___y_2283_ = v___y_2327_;
v___y_2284_ = v___y_2326_;
v___y_2285_ = v___x_2429_;
goto v___jp_2269_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_fst_2344_);
lean_dec(v_a_2339_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2430_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2348_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2348_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v_a_2339_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2438_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2342_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2342_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2446_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2338_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2338_);
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
lean_dec(v_a_2335_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2454_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2336_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2336_);
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
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v_a_2244_);
lean_dec_ref(v___f_2243_);
lean_dec_ref(v___x_2242_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v___x_2240_);
lean_dec(v___x_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v_snd_2237_);
lean_dec(v_discharge_x3f_2236_);
lean_dec_ref(v_simprocs_2235_);
lean_dec_ref(v___x_2234_);
lean_dec_ref(v___x_2230_);
lean_dec(v_snd_2227_);
v_a_2462_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2334_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2334_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(lean_object** _args){
lean_object* v_usingArg_2599_ = _args[0];
lean_object* v_snd_2600_ = _args[1];
lean_object* v___x_2601_ = _args[2];
lean_object* v___x_2602_ = _args[3];
lean_object* v___x_2603_ = _args[4];
lean_object* v_useReducible_2604_ = _args[5];
lean_object* v___x_2605_ = _args[6];
lean_object* v___x_2606_ = _args[7];
lean_object* v___x_2607_ = _args[8];
lean_object* v_simprocs_2608_ = _args[9];
lean_object* v_discharge_x3f_2609_ = _args[10];
lean_object* v_snd_2610_ = _args[11];
lean_object* v___f_2611_ = _args[12];
lean_object* v___x_2612_ = _args[13];
lean_object* v___x_2613_ = _args[14];
lean_object* v___x_2614_ = _args[15];
lean_object* v___x_2615_ = _args[16];
lean_object* v___f_2616_ = _args[17];
lean_object* v_a_2617_ = _args[18];
lean_object* v___x_2618_ = _args[19];
lean_object* v___f_2619_ = _args[20];
lean_object* v___y_2620_ = _args[21];
lean_object* v___y_2621_ = _args[22];
lean_object* v___y_2622_ = _args[23];
lean_object* v___y_2623_ = _args[24];
lean_object* v___y_2624_ = _args[25];
lean_object* v___y_2625_ = _args[26];
lean_object* v___y_2626_ = _args[27];
lean_object* v___y_2627_ = _args[28];
lean_object* v___y_2628_ = _args[29];
_start:
{
uint8_t v___x_92939__boxed_2629_; uint8_t v___x_92940__boxed_2630_; uint8_t v_useReducible_boxed_2631_; uint8_t v___x_92942__boxed_2632_; lean_object* v_res_2633_; 
v___x_92939__boxed_2629_ = lean_unbox(v___x_2601_);
v___x_92940__boxed_2630_ = lean_unbox(v___x_2602_);
v_useReducible_boxed_2631_ = lean_unbox(v_useReducible_2604_);
v___x_92942__boxed_2632_ = lean_unbox(v___x_2605_);
v_res_2633_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(v_usingArg_2599_, v_snd_2600_, v___x_92939__boxed_2629_, v___x_92940__boxed_2630_, v___x_2603_, v_useReducible_boxed_2631_, v___x_92942__boxed_2632_, v___x_2606_, v___x_2607_, v_simprocs_2608_, v_discharge_x3f_2609_, v_snd_2610_, v___f_2611_, v___x_2612_, v___x_2613_, v___x_2614_, v___x_2615_, v___f_2616_, v_a_2617_, v___x_2618_, v___f_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___x_2618_);
lean_dec(v___x_2606_);
return v_res_2633_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0(void){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2634_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_unsigned_to_nat(32u);
v___x_2638_ = lean_mk_empty_array_with_capacity(v___x_2637_);
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(lean_object* v___x_2640_, lean_object* v_tk_2641_, lean_object* v___x_2642_, lean_object* v___x_2643_, lean_object* v___x_2644_, lean_object* v_simprocs_2645_, uint8_t v___x_2646_, lean_object* v_usingArg_2647_, uint8_t v___x_2648_, lean_object* v___x_2649_, uint8_t v_useReducible_2650_, uint8_t v___x_2651_, lean_object* v___x_2652_, lean_object* v___f_2653_, lean_object* v___x_2654_, lean_object* v___x_2655_, lean_object* v___x_2656_, lean_object* v___f_2657_, lean_object* v_a_2658_, lean_object* v_usingTk_x3f_2659_, lean_object* v_discharge_x3f_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___y_2671_; 
if (lean_obj_tag(v_usingTk_x3f_2659_) == 0)
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_box(0);
v___y_2671_ = v___x_2785_;
goto v___jp_2670_;
}
else
{
lean_object* v_val_2786_; 
v_val_2786_ = lean_ctor_get(v_usingTk_x3f_2659_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v_usingTk_x3f_2659_, 1);
v___y_2671_ = v_val_2786_;
goto v___jp_2670_;
}
v___jp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2672_ = lean_mk_empty_array_with_capacity(v___x_2640_);
v___x_2673_ = lean_array_push(v___x_2672_, v_tk_2641_);
v___x_2674_ = lean_array_push(v___x_2673_, v___y_2671_);
v___x_2675_ = lean_box(2);
lean_inc(v___x_2642_);
v___x_2676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
lean_ctor_set(v___x_2676_, 1, v___x_2642_);
lean_ctor_set(v___x_2676_, 2, v___x_2674_);
v___x_2677_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_2676_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v___x_2679_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2662_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; size_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = lean_mk_empty_array_with_capacity(v___x_2643_);
v___x_2682_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1);
lean_inc_n(v___x_2643_, 3);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v___x_2643_);
v___x_2684_ = lean_unsigned_to_nat(32u);
v___x_2685_ = lean_mk_empty_array_with_capacity(v___x_2684_);
v___x_2686_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2);
v___x_2687_ = ((size_t)5ULL);
v___x_2688_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
lean_ctor_set(v___x_2688_, 1, v___x_2685_);
lean_ctor_set(v___x_2688_, 2, v___x_2643_);
lean_ctor_set(v___x_2688_, 3, v___x_2643_);
lean_ctor_set_usize(v___x_2688_, 4, v___x_2687_);
v___x_2689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2682_);
lean_ctor_set(v___x_2689_, 1, v___x_2682_);
lean_ctor_set(v___x_2689_, 2, v___x_2682_);
lean_ctor_set(v___x_2689_, 3, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2683_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
lean_inc_ref(v___x_2690_);
lean_inc(v_discharge_x3f_2660_);
lean_inc_ref(v_simprocs_2645_);
lean_inc_ref(v___x_2644_);
v___x_2691_ = l_Lean_Meta_simpGoal(v_a_2680_, v___x_2644_, v_simprocs_2645_, v_discharge_x3f_2660_, v___x_2646_, v___x_2681_, v___x_2690_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v_fst_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v_fst_2693_ = lean_ctor_get(v_a_2692_, 0);
if (lean_obj_tag(v_fst_2693_) == 1)
{
lean_object* v_val_2694_; lean_object* v_snd_2695_; lean_object* v_snd_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref_known(v___x_2690_, 2);
v_val_2694_ = lean_ctor_get(v_fst_2693_, 0);
lean_inc(v_val_2694_);
v_snd_2695_ = lean_ctor_get(v_a_2692_, 1);
lean_inc(v_snd_2695_);
lean_dec(v_a_2692_);
v_snd_2696_ = lean_ctor_get(v_val_2694_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_val_2694_);
if (v_isSharedCheck_2720_ == 0)
{
lean_object* v_unused_2721_; 
v_unused_2721_ = lean_ctor_get(v_val_2694_, 0);
lean_dec(v_unused_2721_);
v___x_2698_ = v_val_2694_;
v_isShared_2699_ = v_isSharedCheck_2720_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_snd_2696_);
lean_dec(v_val_2694_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2720_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = lean_box(0);
lean_inc(v_snd_2696_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 1);
lean_ctor_set(v___x_2698_, 1, v___x_2700_);
lean_ctor_set(v___x_2698_, 0, v_snd_2696_);
v___x_2702_ = v___x_2698_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_snd_2696_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2702_, v___y_2662_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v___f_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___y_2709_; lean_object* v___x_2710_; 
lean_dec_ref_known(v___x_2703_, 1);
v___f_2704_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2704_, 0, v_a_2678_);
v___x_2705_ = lean_box(v___x_2646_);
v___x_2706_ = lean_box(v___x_2648_);
v___x_2707_ = lean_box(v_useReducible_2650_);
v___x_2708_ = lean_box(v___x_2651_);
lean_inc(v_snd_2696_);
v___y_2709_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed), 30, 21);
lean_closure_set(v___y_2709_, 0, v_usingArg_2647_);
lean_closure_set(v___y_2709_, 1, v_snd_2696_);
lean_closure_set(v___y_2709_, 2, v___x_2705_);
lean_closure_set(v___y_2709_, 3, v___x_2706_);
lean_closure_set(v___y_2709_, 4, v___x_2649_);
lean_closure_set(v___y_2709_, 5, v___x_2707_);
lean_closure_set(v___y_2709_, 6, v___x_2708_);
lean_closure_set(v___y_2709_, 7, v___x_2652_);
lean_closure_set(v___y_2709_, 8, v___x_2644_);
lean_closure_set(v___y_2709_, 9, v_simprocs_2645_);
lean_closure_set(v___y_2709_, 10, v_discharge_x3f_2660_);
lean_closure_set(v___y_2709_, 11, v_snd_2695_);
lean_closure_set(v___y_2709_, 12, v___f_2653_);
lean_closure_set(v___y_2709_, 13, v___x_2642_);
lean_closure_set(v___y_2709_, 14, v___x_2654_);
lean_closure_set(v___y_2709_, 15, v___x_2655_);
lean_closure_set(v___y_2709_, 16, v___x_2656_);
lean_closure_set(v___y_2709_, 17, v___f_2657_);
lean_closure_set(v___y_2709_, 18, v_a_2658_);
lean_closure_set(v___y_2709_, 19, v___x_2643_);
lean_closure_set(v___y_2709_, 20, v___f_2704_);
v___x_2710_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___redArg(v_snd_2696_, v___y_2709_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2710_;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_snd_2696_);
lean_dec(v_snd_2695_);
lean_dec(v_a_2678_);
lean_dec(v_discharge_x3f_2660_);
lean_dec_ref(v_a_2658_);
lean_dec_ref(v___f_2657_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v___x_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___f_2653_);
lean_dec(v___x_2652_);
lean_dec_ref(v___x_2649_);
lean_dec(v_usingArg_2647_);
lean_dec_ref(v_simprocs_2645_);
lean_dec_ref(v___x_2644_);
lean_dec(v___x_2643_);
lean_dec(v___x_2642_);
v_a_2711_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2703_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2703_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
}
else
{
lean_object* v___x_2722_; lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2692_);
lean_dec(v_a_2678_);
lean_dec(v_discharge_x3f_2660_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v___x_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___f_2653_);
lean_dec(v___x_2652_);
lean_dec_ref(v___x_2649_);
lean_dec(v_usingArg_2647_);
lean_dec_ref(v_simprocs_2645_);
lean_dec_ref(v___x_2644_);
lean_dec(v___x_2643_);
lean_dec(v___x_2642_);
v___x_2722_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2760_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2760_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
uint8_t v___x_2727_; 
v___x_2727_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_2723_);
lean_dec(v_a_2723_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2729_; 
lean_dec_ref(v_a_2658_);
lean_dec_ref(v___f_2657_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2690_);
v___x_2729_ = v___x_2725_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2690_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
else
{
lean_object* v_ref_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_del_object(v___x_2725_);
v_ref_2731_ = lean_ctor_get(v___y_2667_, 5);
v___x_2732_ = lean_box(0);
lean_inc(v___y_2668_);
lean_inc_ref(v___y_2667_);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
lean_inc(v___y_2662_);
lean_inc_ref(v___y_2661_);
v___x_2733_ = lean_apply_10(v___f_2657_, v___x_2732_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, lean_box(0));
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
lean_inc(v_ref_2731_);
v___x_2735_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa(v_a_2658_, v_ref_2731_, v_a_2734_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; 
v_unused_2743_ = lean_ctor_get(v___x_2735_, 0);
lean_dec(v_unused_2743_);
v___x_2737_ = v___x_2735_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_dec(v___x_2735_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2690_);
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2690_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref_known(v___x_2690_, 2);
v_a_2744_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2735_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2735_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref_known(v___x_2690_, 2);
lean_dec_ref(v_a_2658_);
v_a_2752_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2733_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2733_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref_known(v___x_2690_, 2);
lean_dec(v_a_2678_);
lean_dec(v_discharge_x3f_2660_);
lean_dec_ref(v_a_2658_);
lean_dec_ref(v___f_2657_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v___x_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___f_2653_);
lean_dec(v___x_2652_);
lean_dec_ref(v___x_2649_);
lean_dec(v_usingArg_2647_);
lean_dec_ref(v_simprocs_2645_);
lean_dec_ref(v___x_2644_);
lean_dec(v___x_2643_);
lean_dec(v___x_2642_);
v_a_2761_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2691_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2691_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2678_);
lean_dec(v_discharge_x3f_2660_);
lean_dec_ref(v_a_2658_);
lean_dec_ref(v___f_2657_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v___x_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___f_2653_);
lean_dec(v___x_2652_);
lean_dec_ref(v___x_2649_);
lean_dec(v_usingArg_2647_);
lean_dec_ref(v_simprocs_2645_);
lean_dec_ref(v___x_2644_);
lean_dec(v___x_2643_);
lean_dec(v___x_2642_);
v_a_2769_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2679_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2679_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_discharge_x3f_2660_);
lean_dec_ref(v_a_2658_);
lean_dec_ref(v___f_2657_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v___x_2655_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___f_2653_);
lean_dec(v___x_2652_);
lean_dec_ref(v___x_2649_);
lean_dec(v_usingArg_2647_);
lean_dec_ref(v_simprocs_2645_);
lean_dec_ref(v___x_2644_);
lean_dec(v___x_2643_);
lean_dec(v___x_2642_);
v_a_2777_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2677_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2677_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(lean_object** _args){
lean_object* v___x_2787_ = _args[0];
lean_object* v_tk_2788_ = _args[1];
lean_object* v___x_2789_ = _args[2];
lean_object* v___x_2790_ = _args[3];
lean_object* v___x_2791_ = _args[4];
lean_object* v_simprocs_2792_ = _args[5];
lean_object* v___x_2793_ = _args[6];
lean_object* v_usingArg_2794_ = _args[7];
lean_object* v___x_2795_ = _args[8];
lean_object* v___x_2796_ = _args[9];
lean_object* v_useReducible_2797_ = _args[10];
lean_object* v___x_2798_ = _args[11];
lean_object* v___x_2799_ = _args[12];
lean_object* v___f_2800_ = _args[13];
lean_object* v___x_2801_ = _args[14];
lean_object* v___x_2802_ = _args[15];
lean_object* v___x_2803_ = _args[16];
lean_object* v___f_2804_ = _args[17];
lean_object* v_a_2805_ = _args[18];
lean_object* v_usingTk_x3f_2806_ = _args[19];
lean_object* v_discharge_x3f_2807_ = _args[20];
lean_object* v___y_2808_ = _args[21];
lean_object* v___y_2809_ = _args[22];
lean_object* v___y_2810_ = _args[23];
lean_object* v___y_2811_ = _args[24];
lean_object* v___y_2812_ = _args[25];
lean_object* v___y_2813_ = _args[26];
lean_object* v___y_2814_ = _args[27];
lean_object* v___y_2815_ = _args[28];
lean_object* v___y_2816_ = _args[29];
_start:
{
uint8_t v___x_93734__boxed_2817_; uint8_t v___x_93735__boxed_2818_; uint8_t v_useReducible_boxed_2819_; uint8_t v___x_93737__boxed_2820_; lean_object* v_res_2821_; 
v___x_93734__boxed_2817_ = lean_unbox(v___x_2793_);
v___x_93735__boxed_2818_ = lean_unbox(v___x_2795_);
v_useReducible_boxed_2819_ = lean_unbox(v_useReducible_2797_);
v___x_93737__boxed_2820_ = lean_unbox(v___x_2798_);
v_res_2821_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(v___x_2787_, v_tk_2788_, v___x_2789_, v___x_2790_, v___x_2791_, v_simprocs_2792_, v___x_93734__boxed_2817_, v_usingArg_2794_, v___x_93735__boxed_2818_, v___x_2796_, v_useReducible_boxed_2819_, v___x_93737__boxed_2820_, v___x_2799_, v___f_2800_, v___x_2801_, v___x_2802_, v___x_2803_, v___f_2804_, v_a_2805_, v_usingTk_x3f_2806_, v_discharge_x3f_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___x_2787_);
return v_res_2821_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2827_ = lean_unsigned_to_nat(38u);
v___x_2828_ = lean_unsigned_to_nat(159u);
v___x_2829_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2831_ = l_mkPanicMessageWithDecl(v___x_2830_, v___x_2829_, v___x_2828_, v___x_2827_, v___x_2826_);
return v___x_2831_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__3));
v___x_2840_ = lean_unsigned_to_nat(15u);
v___x_2841_ = lean_unsigned_to_nat(160u);
v___x_2842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__2));
v___x_2843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__1));
v___x_2844_ = l_mkPanicMessageWithDecl(v___x_2843_, v___x_2842_, v___x_2841_, v___x_2840_, v___x_2839_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(lean_object* v_tk_2846_, lean_object* v___x_2847_, lean_object* v___x_2848_, lean_object* v___x_2849_, lean_object* v___x_2850_, uint8_t v___x_2851_, lean_object* v___x_2852_, lean_object* v___x_2853_, uint8_t v_useReducible_2854_, lean_object* v___f_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v___x_2858_, lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v___x_2861_, lean_object* v_usingArg_2862_, lean_object* v___x_2863_, uint8_t v___x_2864_, lean_object* v___f_2865_, lean_object* v_usingTk_x3f_2866_, lean_object* v_squeeze_2867_, lean_object* v_unfold_2868_, lean_object* v_args_2869_, lean_object* v_only_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___y_2882_; lean_object* v___y_2886_; lean_object* v_stx_2887_; lean_object* v___y_2888_; lean_object* v_ref_2889_; lean_object* v___y_2890_; lean_object* v___y_2909_; lean_object* v_stx_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2873_, v___y_2875_, v___y_2877_, v___y_2879_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v_options_2937_; lean_object* v_ref_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; uint8_t v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; uint8_t v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v_args_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; uint8_t v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v_only_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; uint8_t v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; uint8_t v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; lean_object* v___y_3500_; uint8_t v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3572_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v_options_2937_ = lean_ctor_get(v___y_2878_, 2);
v_ref_2938_ = lean_ctor_get(v___y_2878_, 5);
v___x_2939_ = 0;
v___x_2940_ = l_Lean_SourceInfo_fromRef(v_ref_2938_, v___x_2939_);
v___x_2941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__3));
lean_inc_ref(v___x_2849_);
lean_inc_ref(v___x_2848_);
lean_inc_ref(v___x_2847_);
v___x_2942_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_2941_);
lean_inc(v___x_2940_);
v___x_2943_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2940_);
lean_ctor_set(v___x_2943_, 1, v___x_2941_);
v___x_2944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_2945_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_2871_) == 0)
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3572_ = v___x_3581_;
goto v___jp_3571_;
}
else
{
lean_object* v_val_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_val_3582_ = lean_ctor_get(v___y_2871_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v___y_2871_, 1);
v___x_3583_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___x_3584_ = lean_array_push(v___x_3583_, v_val_3582_);
v___y_3572_ = v___x_3584_;
goto v___jp_3571_;
}
v___jp_2946_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2958_ = l_Array_append___redArg(v___x_2945_, v___y_2957_);
lean_dec_ref(v___y_2957_);
lean_inc_n(v___y_2947_, 2);
v___x_2959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2959_, 0, v___y_2947_);
lean_ctor_set(v___x_2959_, 1, v___x_2944_);
lean_ctor_set(v___x_2959_, 2, v___x_2958_);
v___x_2960_ = l_Lean_Syntax_node5(v___y_2947_, v___x_2852_, v___y_2955_, v___y_2950_, v___y_2949_, v___y_2951_, v___x_2959_);
v___x_2961_ = l_Lean_Syntax_node2(v___y_2947_, v___y_2953_, v___y_2956_, v___x_2960_);
v___y_2909_ = v___y_2952_;
v_stx_2910_ = v___x_2961_;
v___y_2911_ = v___y_2954_;
v___y_2912_ = v___y_2948_;
goto v___jp_2908_;
}
v___jp_2962_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = l_Array_append___redArg(v___x_2945_, v___y_2973_);
lean_dec_ref(v___y_2973_);
lean_inc(v___y_2963_);
v___x_2975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2975_, 0, v___y_2963_);
lean_ctor_set(v___x_2975_, 1, v___x_2944_);
lean_ctor_set(v___x_2975_, 2, v___x_2974_);
if (lean_obj_tag(v___y_2968_) == 1)
{
lean_object* v_val_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec(v___x_2850_);
v_val_2976_ = lean_ctor_get(v___y_2968_, 0);
lean_inc(v_val_2976_);
lean_dec_ref_known(v___y_2968_, 1);
v___x_2977_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_2963_);
v___x_2978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___y_2963_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = l_Array_mkArray2___redArg(v___x_2978_, v_val_2976_);
v___y_2947_ = v___y_2963_;
v___y_2948_ = v___y_2966_;
v___y_2949_ = v___y_2965_;
v___y_2950_ = v___y_2964_;
v___y_2951_ = v___x_2975_;
v___y_2952_ = v___y_2967_;
v___y_2953_ = v___y_2969_;
v___y_2954_ = v___y_2970_;
v___y_2955_ = v___y_2971_;
v___y_2956_ = v___y_2972_;
v___y_2957_ = v___x_2979_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2980_; 
lean_dec(v___y_2968_);
v___x_2980_ = lean_mk_empty_array_with_capacity(v___x_2850_);
lean_dec(v___x_2850_);
v___y_2947_ = v___y_2963_;
v___y_2948_ = v___y_2966_;
v___y_2949_ = v___y_2965_;
v___y_2950_ = v___y_2964_;
v___y_2951_ = v___x_2975_;
v___y_2952_ = v___y_2967_;
v___y_2953_ = v___y_2969_;
v___y_2954_ = v___y_2970_;
v___y_2955_ = v___y_2971_;
v___y_2956_ = v___y_2972_;
v___y_2957_ = v___x_2980_;
goto v___jp_2946_;
}
}
v___jp_2981_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = l_Array_append___redArg(v___x_2945_, v___y_2992_);
lean_dec_ref(v___y_2992_);
lean_inc(v___y_2982_);
v___x_2994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2994_, 0, v___y_2982_);
lean_ctor_set(v___x_2994_, 1, v___x_2944_);
lean_ctor_set(v___x_2994_, 2, v___x_2993_);
if (lean_obj_tag(v___y_2989_) == 1)
{
lean_object* v_val_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_val_2995_ = lean_ctor_get(v___y_2989_, 0);
lean_inc(v_val_2995_);
lean_dec_ref_known(v___y_2989_, 1);
v___x_2996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_2997_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_2996_);
v___x_2998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_2982_, 4);
v___x_2999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___y_2982_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_Array_append___redArg(v___x_2945_, v_val_2995_);
lean_dec(v_val_2995_);
v___x_3001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3001_, 0, v___y_2982_);
lean_ctor_set(v___x_3001_, 1, v___x_2944_);
lean_ctor_set(v___x_3001_, 2, v___x_3000_);
v___x_3002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___y_2982_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = l_Lean_Syntax_node3(v___y_2982_, v___x_2997_, v___x_2999_, v___x_3001_, v___x_3003_);
v___x_3005_ = l_Array_mkArray1___redArg(v___x_3004_);
v___y_2963_ = v___y_2982_;
v___y_2964_ = v___y_2984_;
v___y_2965_ = v___x_2994_;
v___y_2966_ = v___y_2983_;
v___y_2967_ = v___y_2985_;
v___y_2968_ = v___y_2986_;
v___y_2969_ = v___y_2987_;
v___y_2970_ = v___y_2988_;
v___y_2971_ = v___y_2990_;
v___y_2972_ = v___y_2991_;
v___y_2973_ = v___x_3005_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_3006_; 
lean_dec(v___y_2989_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3006_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_2963_ = v___y_2982_;
v___y_2964_ = v___y_2984_;
v___y_2965_ = v___x_2994_;
v___y_2966_ = v___y_2983_;
v___y_2967_ = v___y_2985_;
v___y_2968_ = v___y_2986_;
v___y_2969_ = v___y_2987_;
v___y_2970_ = v___y_2988_;
v___y_2971_ = v___y_2990_;
v___y_2972_ = v___y_2991_;
v___y_2973_ = v___x_3006_;
goto v___jp_2962_;
}
}
v___jp_3007_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = l_Array_append___redArg(v___x_2945_, v___y_3018_);
lean_dec_ref(v___y_3018_);
lean_inc(v___y_3008_);
v___x_3020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3020_, 0, v___y_3008_);
lean_ctor_set(v___x_3020_, 1, v___x_2944_);
lean_ctor_set(v___x_3020_, 2, v___x_3019_);
if (lean_obj_tag(v___y_3011_) == 1)
{
lean_object* v_val_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_val_3021_ = lean_ctor_get(v___y_3011_, 0);
lean_inc(v_val_3021_);
lean_dec_ref_known(v___y_3011_, 1);
v___x_3022_ = l_Lean_SourceInfo_fromRef(v_val_3021_, v___x_2851_);
lean_dec(v_val_3021_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3024_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Array_mkArray1___redArg(v___x_3024_);
v___y_2982_ = v___y_3008_;
v___y_2983_ = v___y_3009_;
v___y_2984_ = v___x_3020_;
v___y_2985_ = v___y_3010_;
v___y_2986_ = v___y_3012_;
v___y_2987_ = v___y_3013_;
v___y_2988_ = v___y_3014_;
v___y_2989_ = v___y_3015_;
v___y_2990_ = v___y_3016_;
v___y_2991_ = v___y_3017_;
v___y_2992_ = v___x_3025_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3026_; 
lean_dec(v___y_3011_);
v___x_3026_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_2982_ = v___y_3008_;
v___y_2983_ = v___y_3009_;
v___y_2984_ = v___x_3020_;
v___y_2985_ = v___y_3010_;
v___y_2986_ = v___y_3012_;
v___y_2987_ = v___y_3013_;
v___y_2988_ = v___y_3014_;
v___y_2989_ = v___y_3015_;
v___y_2990_ = v___y_3016_;
v___y_2991_ = v___y_3017_;
v___y_2992_ = v___x_3026_;
goto v___jp_2981_;
}
}
v___jp_3027_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3042_ = l_Array_append___redArg(v___x_2945_, v___y_3041_);
lean_dec_ref(v___y_3041_);
lean_inc_n(v___y_3037_, 3);
v___x_3043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3043_, 0, v___y_3037_);
lean_ctor_set(v___x_3043_, 1, v___x_2944_);
lean_ctor_set(v___x_3043_, 2, v___x_3042_);
v___x_3044_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___y_3037_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_Syntax_node6(v___y_3037_, v___y_3029_, v___y_3031_, v___y_3040_, v___y_3032_, v___x_3043_, v___x_3045_, v___y_3033_);
v___x_3047_ = l_Lean_Syntax_node4(v___y_3037_, v___y_3038_, v___y_3039_, v___y_3036_, v___y_3035_, v___x_3046_);
v___y_2909_ = v___y_3034_;
v_stx_2910_ = v___x_3047_;
v___y_2911_ = v___y_3030_;
v___y_2912_ = v___y_3028_;
goto v___jp_2908_;
}
v___jp_3048_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = l_Array_append___redArg(v___x_2945_, v___y_3062_);
lean_dec_ref(v___y_3062_);
lean_inc(v___y_3058_);
v___x_3064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3064_, 0, v___y_3058_);
lean_ctor_set(v___x_3064_, 1, v___x_2944_);
lean_ctor_set(v___x_3064_, 2, v___x_3063_);
if (lean_obj_tag(v___y_3056_) == 1)
{
lean_object* v_val_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec(v___x_2850_);
v_val_3065_ = lean_ctor_get(v___y_3056_, 0);
lean_inc(v_val_3065_);
lean_dec_ref_known(v___y_3056_, 1);
v___x_3066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3067_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3066_);
v___x_3068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3058_, 4);
v___x_3069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___y_3058_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = l_Array_append___redArg(v___x_2945_, v_val_3065_);
lean_dec(v_val_3065_);
v___x_3071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3058_);
lean_ctor_set(v___x_3071_, 1, v___x_2944_);
lean_ctor_set(v___x_3071_, 2, v___x_3070_);
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___y_3058_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = l_Lean_Syntax_node3(v___y_3058_, v___x_3067_, v___x_3069_, v___x_3071_, v___x_3073_);
v___x_3075_ = l_Array_mkArray1___redArg(v___x_3074_);
v___y_3028_ = v___y_3049_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v___y_3051_;
v___y_3031_ = v___y_3052_;
v___y_3032_ = v___x_3064_;
v___y_3033_ = v___y_3053_;
v___y_3034_ = v___y_3054_;
v___y_3035_ = v___y_3055_;
v___y_3036_ = v___y_3057_;
v___y_3037_ = v___y_3058_;
v___y_3038_ = v___y_3059_;
v___y_3039_ = v___y_3060_;
v___y_3040_ = v___y_3061_;
v___y_3041_ = v___x_3075_;
goto v___jp_3027_;
}
else
{
lean_object* v___x_3076_; 
lean_dec(v___y_3056_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3076_ = lean_mk_empty_array_with_capacity(v___x_2850_);
lean_dec(v___x_2850_);
v___y_3028_ = v___y_3049_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v___y_3051_;
v___y_3031_ = v___y_3052_;
v___y_3032_ = v___x_3064_;
v___y_3033_ = v___y_3053_;
v___y_3034_ = v___y_3054_;
v___y_3035_ = v___y_3055_;
v___y_3036_ = v___y_3057_;
v___y_3037_ = v___y_3058_;
v___y_3038_ = v___y_3059_;
v___y_3039_ = v___y_3060_;
v___y_3040_ = v___y_3061_;
v___y_3041_ = v___x_3076_;
goto v___jp_3027_;
}
}
v___jp_3077_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = l_Array_append___redArg(v___x_2945_, v___y_3091_);
lean_dec_ref(v___y_3091_);
lean_inc(v___y_3088_);
v___x_3093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3093_, 0, v___y_3088_);
lean_ctor_set(v___x_3093_, 1, v___x_2944_);
lean_ctor_set(v___x_3093_, 2, v___x_3092_);
if (lean_obj_tag(v___y_3079_) == 1)
{
lean_object* v_val_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_val_3094_ = lean_ctor_get(v___y_3079_, 0);
lean_inc(v_val_3094_);
lean_dec_ref_known(v___y_3079_, 1);
v___x_3095_ = l_Lean_SourceInfo_fromRef(v_val_3094_, v___x_2851_);
lean_dec(v_val_3094_);
v___x_3096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Array_mkArray1___redArg(v___x_3097_);
v___y_3049_ = v___y_3078_;
v___y_3050_ = v___y_3080_;
v___y_3051_ = v___y_3081_;
v___y_3052_ = v___y_3082_;
v___y_3053_ = v___y_3083_;
v___y_3054_ = v___y_3084_;
v___y_3055_ = v___y_3085_;
v___y_3056_ = v___y_3086_;
v___y_3057_ = v___y_3087_;
v___y_3058_ = v___y_3088_;
v___y_3059_ = v___y_3089_;
v___y_3060_ = v___y_3090_;
v___y_3061_ = v___x_3093_;
v___y_3062_ = v___x_3098_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3099_; 
lean_dec(v___y_3079_);
v___x_3099_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3049_ = v___y_3078_;
v___y_3050_ = v___y_3080_;
v___y_3051_ = v___y_3081_;
v___y_3052_ = v___y_3082_;
v___y_3053_ = v___y_3083_;
v___y_3054_ = v___y_3084_;
v___y_3055_ = v___y_3085_;
v___y_3056_ = v___y_3086_;
v___y_3057_ = v___y_3087_;
v___y_3058_ = v___y_3088_;
v___y_3059_ = v___y_3089_;
v___y_3060_ = v___y_3090_;
v___y_3061_ = v___x_3093_;
v___y_3062_ = v___x_3099_;
goto v___jp_3048_;
}
}
v___jp_3100_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3112_ = l_Array_append___redArg(v___x_2945_, v___y_3111_);
lean_dec_ref(v___y_3111_);
lean_inc_n(v___y_3102_, 2);
v___x_3113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3113_, 0, v___y_3102_);
lean_ctor_set(v___x_3113_, 1, v___x_2944_);
lean_ctor_set(v___x_3113_, 2, v___x_3112_);
v___x_3114_ = l_Lean_Syntax_node5(v___y_3102_, v___x_2852_, v___y_3109_, v___y_3104_, v___y_3108_, v___y_3107_, v___x_3113_);
lean_inc(v___y_3110_);
v___x_3115_ = l_Lean_Syntax_node4(v___y_3102_, v___x_2853_, v___y_3103_, v___y_3110_, v___y_3110_, v___x_3114_);
v___y_2909_ = v___y_3105_;
v_stx_2910_ = v___x_3115_;
v___y_2911_ = v___y_3106_;
v___y_2912_ = v___y_3101_;
goto v___jp_2908_;
}
v___jp_3116_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = l_Array_append___redArg(v___x_2945_, v___y_3127_);
lean_dec_ref(v___y_3127_);
lean_inc(v___y_3118_);
v___x_3129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3129_, 0, v___y_3118_);
lean_ctor_set(v___x_3129_, 1, v___x_2944_);
lean_ctor_set(v___x_3129_, 2, v___x_3128_);
if (lean_obj_tag(v___y_3122_) == 1)
{
lean_object* v_val_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v___x_2850_);
v_val_3130_ = lean_ctor_get(v___y_3122_, 0);
lean_inc(v_val_3130_);
lean_dec_ref_known(v___y_3122_, 1);
v___x_3131_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
lean_inc(v___y_3118_);
v___x_3132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___y_3118_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = l_Array_mkArray2___redArg(v___x_3132_, v_val_3130_);
v___y_3101_ = v___y_3117_;
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3120_;
v___y_3104_ = v___y_3119_;
v___y_3105_ = v___y_3121_;
v___y_3106_ = v___y_3124_;
v___y_3107_ = v___x_3129_;
v___y_3108_ = v___y_3123_;
v___y_3109_ = v___y_3125_;
v___y_3110_ = v___y_3126_;
v___y_3111_ = v___x_3133_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3134_; 
lean_dec(v___y_3122_);
v___x_3134_ = lean_mk_empty_array_with_capacity(v___x_2850_);
lean_dec(v___x_2850_);
v___y_3101_ = v___y_3117_;
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3120_;
v___y_3104_ = v___y_3119_;
v___y_3105_ = v___y_3121_;
v___y_3106_ = v___y_3124_;
v___y_3107_ = v___x_3129_;
v___y_3108_ = v___y_3123_;
v___y_3109_ = v___y_3125_;
v___y_3110_ = v___y_3126_;
v___y_3111_ = v___x_3134_;
goto v___jp_3100_;
}
}
v___jp_3135_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = l_Array_append___redArg(v___x_2945_, v___y_3146_);
lean_dec_ref(v___y_3146_);
lean_inc(v___y_3137_);
v___x_3148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3148_, 0, v___y_3137_);
lean_ctor_set(v___x_3148_, 1, v___x_2944_);
lean_ctor_set(v___x_3148_, 2, v___x_3147_);
if (lean_obj_tag(v___y_3143_) == 1)
{
lean_object* v_val_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_val_3149_ = lean_ctor_get(v___y_3143_, 0);
lean_inc(v_val_3149_);
lean_dec_ref_known(v___y_3143_, 1);
v___x_3150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3151_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3150_);
v___x_3152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3137_, 4);
v___x_3153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___y_3137_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = l_Array_append___redArg(v___x_2945_, v_val_3149_);
lean_dec(v_val_3149_);
v___x_3155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3155_, 0, v___y_3137_);
lean_ctor_set(v___x_3155_, 1, v___x_2944_);
lean_ctor_set(v___x_3155_, 2, v___x_3154_);
v___x_3156_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___y_3137_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Lean_Syntax_node3(v___y_3137_, v___x_3151_, v___x_3153_, v___x_3155_, v___x_3157_);
v___x_3159_ = l_Array_mkArray1___redArg(v___x_3158_);
v___y_3117_ = v___y_3136_;
v___y_3118_ = v___y_3137_;
v___y_3119_ = v___y_3139_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3140_;
v___y_3122_ = v___y_3141_;
v___y_3123_ = v___x_3148_;
v___y_3124_ = v___y_3142_;
v___y_3125_ = v___y_3144_;
v___y_3126_ = v___y_3145_;
v___y_3127_ = v___x_3159_;
goto v___jp_3116_;
}
else
{
lean_object* v___x_3160_; 
lean_dec(v___y_3143_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3160_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3117_ = v___y_3136_;
v___y_3118_ = v___y_3137_;
v___y_3119_ = v___y_3139_;
v___y_3120_ = v___y_3138_;
v___y_3121_ = v___y_3140_;
v___y_3122_ = v___y_3141_;
v___y_3123_ = v___x_3148_;
v___y_3124_ = v___y_3142_;
v___y_3125_ = v___y_3144_;
v___y_3126_ = v___y_3145_;
v___y_3127_ = v___x_3160_;
goto v___jp_3116_;
}
}
v___jp_3161_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = l_Array_append___redArg(v___x_2945_, v___y_3172_);
lean_dec_ref(v___y_3172_);
lean_inc(v___y_3163_);
v___x_3174_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___y_3163_);
lean_ctor_set(v___x_3174_, 1, v___x_2944_);
lean_ctor_set(v___x_3174_, 2, v___x_3173_);
if (lean_obj_tag(v___y_3166_) == 1)
{
lean_object* v_val_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_val_3175_ = lean_ctor_get(v___y_3166_, 0);
lean_inc(v_val_3175_);
lean_dec_ref_known(v___y_3166_, 1);
v___x_3176_ = l_Lean_SourceInfo_fromRef(v_val_3175_, v___x_2851_);
lean_dec(v_val_3175_);
v___x_3177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3176_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = l_Array_mkArray1___redArg(v___x_3178_);
v___y_3136_ = v___y_3162_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___x_3174_;
v___y_3140_ = v___y_3165_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3168_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___y_3170_;
v___y_3145_ = v___y_3171_;
v___y_3146_ = v___x_3179_;
goto v___jp_3135_;
}
else
{
lean_object* v___x_3180_; 
lean_dec(v___y_3166_);
v___x_3180_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3136_ = v___y_3162_;
v___y_3137_ = v___y_3163_;
v___y_3138_ = v___y_3164_;
v___y_3139_ = v___x_3174_;
v___y_3140_ = v___y_3165_;
v___y_3141_ = v___y_3167_;
v___y_3142_ = v___y_3168_;
v___y_3143_ = v___y_3169_;
v___y_3144_ = v___y_3170_;
v___y_3145_ = v___y_3171_;
v___y_3146_ = v___x_3180_;
goto v___jp_3135_;
}
}
v___jp_3181_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3195_ = l_Array_append___redArg(v___x_2945_, v___y_3194_);
lean_dec_ref(v___y_3194_);
lean_inc_n(v___y_3193_, 3);
v___x_3196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3196_, 0, v___y_3193_);
lean_ctor_set(v___x_3196_, 1, v___x_2944_);
lean_ctor_set(v___x_3196_, 2, v___x_3195_);
v___x_3197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__6));
v___x_3198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___y_3193_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = l_Lean_Syntax_node6(v___y_3193_, v___y_3190_, v___y_3189_, v___y_3182_, v___y_3186_, v___x_3196_, v___x_3198_, v___y_3183_);
lean_inc(v___y_3185_);
v___x_3200_ = l_Lean_Syntax_node4(v___y_3193_, v___y_3191_, v___y_3188_, v___y_3185_, v___y_3185_, v___x_3199_);
v___y_2909_ = v___y_3192_;
v_stx_2910_ = v___x_3200_;
v___y_2911_ = v___y_3187_;
v___y_2912_ = v___y_3184_;
goto v___jp_2908_;
}
v___jp_3201_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = l_Array_append___redArg(v___x_2945_, v___y_3214_);
lean_dec_ref(v___y_3214_);
lean_inc(v___y_3213_);
v___x_3216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3216_, 0, v___y_3213_);
lean_ctor_set(v___x_3216_, 1, v___x_2944_);
lean_ctor_set(v___x_3216_, 2, v___x_3215_);
if (lean_obj_tag(v___y_3212_) == 1)
{
lean_object* v_val_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec(v___x_2850_);
v_val_3217_ = lean_ctor_get(v___y_3212_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v___y_3212_, 1);
v___x_3218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__12));
v___x_3219_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3218_);
v___x_3220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_3213_, 4);
v___x_3221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___y_3213_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l_Array_append___redArg(v___x_2945_, v_val_3217_);
lean_dec(v_val_3217_);
v___x_3223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3223_, 0, v___y_3213_);
lean_ctor_set(v___x_3223_, 1, v___x_2944_);
lean_ctor_set(v___x_3223_, 2, v___x_3222_);
v___x_3224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___y_3213_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = l_Lean_Syntax_node3(v___y_3213_, v___x_3219_, v___x_3221_, v___x_3223_, v___x_3225_);
v___x_3227_ = l_Array_mkArray1___redArg(v___x_3226_);
v___y_3182_ = v___y_3202_;
v___y_3183_ = v___y_3203_;
v___y_3184_ = v___y_3204_;
v___y_3185_ = v___y_3205_;
v___y_3186_ = v___x_3216_;
v___y_3187_ = v___y_3206_;
v___y_3188_ = v___y_3207_;
v___y_3189_ = v___y_3208_;
v___y_3190_ = v___y_3209_;
v___y_3191_ = v___y_3210_;
v___y_3192_ = v___y_3211_;
v___y_3193_ = v___y_3213_;
v___y_3194_ = v___x_3227_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3228_; 
lean_dec(v___y_3212_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3228_ = lean_mk_empty_array_with_capacity(v___x_2850_);
lean_dec(v___x_2850_);
v___y_3182_ = v___y_3202_;
v___y_3183_ = v___y_3203_;
v___y_3184_ = v___y_3204_;
v___y_3185_ = v___y_3205_;
v___y_3186_ = v___x_3216_;
v___y_3187_ = v___y_3206_;
v___y_3188_ = v___y_3207_;
v___y_3189_ = v___y_3208_;
v___y_3190_ = v___y_3209_;
v___y_3191_ = v___y_3210_;
v___y_3192_ = v___y_3211_;
v___y_3193_ = v___y_3213_;
v___y_3194_ = v___x_3228_;
goto v___jp_3181_;
}
}
v___jp_3229_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = l_Array_append___redArg(v___x_2945_, v___y_3242_);
lean_dec_ref(v___y_3242_);
lean_inc(v___y_3241_);
v___x_3244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3244_, 0, v___y_3241_);
lean_ctor_set(v___x_3244_, 1, v___x_2944_);
lean_ctor_set(v___x_3244_, 2, v___x_3243_);
if (lean_obj_tag(v___y_3233_) == 1)
{
lean_object* v_val_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_val_3245_ = lean_ctor_get(v___y_3233_, 0);
lean_inc(v_val_3245_);
lean_dec_ref_known(v___y_3233_, 1);
v___x_3246_ = l_Lean_SourceInfo_fromRef(v_val_3245_, v___x_2851_);
lean_dec(v_val_3245_);
v___x_3247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = l_Array_mkArray1___redArg(v___x_3248_);
v___y_3202_ = v___x_3244_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3234_;
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3236_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3238_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v___y_3241_;
v___y_3214_ = v___x_3249_;
goto v___jp_3201_;
}
else
{
lean_object* v___x_3250_; 
lean_dec(v___y_3233_);
v___x_3250_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3202_ = v___x_3244_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___y_3234_;
v___y_3207_ = v___y_3235_;
v___y_3208_ = v___y_3236_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3238_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v___y_3241_;
v___y_3214_ = v___x_3250_;
goto v___jp_3201_;
}
}
v___jp_3251_:
{
if (v___y_3260_ == 0)
{
if (v_useReducible_2854_ == 0)
{
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_dec(v___y_3266_);
lean_dec(v___y_3264_);
lean_dec(v___y_3257_);
lean_dec(v___y_3253_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___y_2915_ = v___y_3262_;
v___y_2916_ = v___y_3265_;
v___y_2917_ = v___y_3259_;
v___y_2918_ = v___y_3254_;
v___y_2919_ = v___y_3261_;
v___y_2920_ = v___y_3258_;
v___y_2921_ = v___y_3256_;
v___y_2922_ = v___y_3255_;
v___y_2923_ = v___y_3252_;
goto v___jp_2914_;
}
else
{
lean_object* v_val_3267_; lean_object* v___x_3268_; 
v_val_3267_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_val_3267_);
lean_dec_ref_known(v___y_3263_, 1);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3255_);
v___x_3268_ = lean_apply_9(v___f_2855_, v___y_3265_, v___y_3259_, v___y_3254_, v___y_3261_, v___y_3258_, v___y_3256_, v___y_3255_, v___y_3252_, lean_box(0));
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc_n(v_a_3269_, 3);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2849_, 2);
lean_inc_ref_n(v___x_2848_, 2);
lean_inc_ref_n(v___x_2847_, 2);
v___x_3271_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_a_3269_);
lean_ctor_set(v___x_3272_, 1, v___x_2856_);
v___x_3273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3273_, 0, v_a_3269_);
lean_ctor_set(v___x_3273_, 1, v___x_2944_);
lean_ctor_set(v___x_3273_, 2, v___x_2945_);
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3275_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3274_);
if (lean_obj_tag(v___y_3266_) == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3230_ = v_val_3267_;
v___y_3231_ = v___y_3252_;
v___y_3232_ = v___x_3273_;
v___y_3233_ = v___y_3253_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___x_3272_;
v___y_3236_ = v___y_3257_;
v___y_3237_ = v___x_3275_;
v___y_3238_ = v___x_3271_;
v___y_3239_ = v___y_3262_;
v___y_3240_ = v___y_3264_;
v___y_3241_ = v_a_3269_;
v___y_3242_ = v___x_3276_;
goto v___jp_3229_;
}
else
{
lean_object* v_val_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_val_3277_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3277_);
lean_dec_ref_known(v___y_3266_, 1);
v___x_3278_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___x_3279_ = lean_array_push(v___x_3278_, v_val_3277_);
v___y_3230_ = v_val_3267_;
v___y_3231_ = v___y_3252_;
v___y_3232_ = v___x_3273_;
v___y_3233_ = v___y_3253_;
v___y_3234_ = v___y_3255_;
v___y_3235_ = v___x_3272_;
v___y_3236_ = v___y_3257_;
v___y_3237_ = v___x_3275_;
v___y_3238_ = v___x_3271_;
v___y_3239_ = v___y_3262_;
v___y_3240_ = v___y_3264_;
v___y_3241_ = v_a_3269_;
v___y_3242_ = v___x_3279_;
goto v___jp_3229_;
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v_val_3267_);
lean_dec(v___y_3266_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___x_2856_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3280_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3268_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3268_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
else
{
lean_object* v___x_3288_; 
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3255_);
v___x_3288_ = lean_apply_9(v___f_2855_, v___y_3265_, v___y_3259_, v___y_3254_, v___y_3261_, v___y_3258_, v___y_3256_, v___y_3255_, v___y_3252_, lean_box(0));
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc_n(v_a_3289_, 3);
lean_dec_ref_known(v___x_3288_, 1);
v___x_3290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_a_3289_);
lean_ctor_set(v___x_3290_, 1, v___x_2856_);
v___x_3291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3291_, 0, v_a_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_2944_);
lean_ctor_set(v___x_3291_, 2, v___x_2945_);
if (lean_obj_tag(v___y_3266_) == 0)
{
lean_object* v___x_3292_; 
v___x_3292_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3162_ = v___y_3252_;
v___y_3163_ = v_a_3289_;
v___y_3164_ = v___x_3290_;
v___y_3165_ = v___y_3262_;
v___y_3166_ = v___y_3253_;
v___y_3167_ = v___y_3263_;
v___y_3168_ = v___y_3255_;
v___y_3169_ = v___y_3264_;
v___y_3170_ = v___y_3257_;
v___y_3171_ = v___x_3291_;
v___y_3172_ = v___x_3292_;
goto v___jp_3161_;
}
else
{
lean_object* v_val_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_val_3293_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3293_);
lean_dec_ref_known(v___y_3266_, 1);
v___x_3294_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___x_3295_ = lean_array_push(v___x_3294_, v_val_3293_);
v___y_3162_ = v___y_3252_;
v___y_3163_ = v_a_3289_;
v___y_3164_ = v___x_3290_;
v___y_3165_ = v___y_3262_;
v___y_3166_ = v___y_3253_;
v___y_3167_ = v___y_3263_;
v___y_3168_ = v___y_3255_;
v___y_3169_ = v___y_3264_;
v___y_3170_ = v___y_3257_;
v___y_3171_ = v___x_3291_;
v___y_3172_ = v___x_3295_;
goto v___jp_3161_;
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v___y_3266_);
lean_dec(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___x_2856_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3296_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3288_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3288_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
else
{
lean_dec(v___x_2853_);
if (v_useReducible_2854_ == 0)
{
lean_dec(v___x_2852_);
if (lean_obj_tag(v___y_3263_) == 0)
{
lean_dec(v___y_3266_);
lean_dec(v___y_3264_);
lean_dec(v___y_3257_);
lean_dec(v___y_3253_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___y_2915_ = v___y_3262_;
v___y_2916_ = v___y_3265_;
v___y_2917_ = v___y_3259_;
v___y_2918_ = v___y_3254_;
v___y_2919_ = v___y_3261_;
v___y_2920_ = v___y_3258_;
v___y_2921_ = v___y_3256_;
v___y_2922_ = v___y_3255_;
v___y_2923_ = v___y_3252_;
goto v___jp_2914_;
}
else
{
lean_object* v_val_3304_; lean_object* v___x_3305_; 
v_val_3304_ = lean_ctor_get(v___y_3263_, 0);
lean_inc(v_val_3304_);
lean_dec_ref_known(v___y_3263_, 1);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3255_);
v___x_3305_ = lean_apply_9(v___f_2855_, v___y_3265_, v___y_3259_, v___y_3254_, v___y_3261_, v___y_3258_, v___y_3256_, v___y_3255_, v___y_3252_, lean_box(0));
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc_n(v_a_3306_, 5);
lean_dec_ref_known(v___x_3305_, 1);
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__7));
lean_inc_ref_n(v___x_2849_, 2);
lean_inc_ref_n(v___x_2848_, 2);
lean_inc_ref_n(v___x_2847_, 2);
v___x_3308_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3307_);
v___x_3309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_a_3306_);
lean_ctor_set(v___x_3309_, 1, v___x_2856_);
v___x_3310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3310_, 0, v_a_3306_);
lean_ctor_set(v___x_3310_, 1, v___x_2944_);
lean_ctor_set(v___x_3310_, 2, v___x_2945_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_3312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3312_, 0, v_a_3306_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = l_Lean_Syntax_node1(v_a_3306_, v___x_2944_, v___x_3312_);
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__8));
v___x_3315_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3314_);
if (lean_obj_tag(v___y_3266_) == 0)
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3078_ = v___y_3252_;
v___y_3079_ = v___y_3253_;
v___y_3080_ = v___x_3315_;
v___y_3081_ = v___y_3255_;
v___y_3082_ = v___y_3257_;
v___y_3083_ = v_val_3304_;
v___y_3084_ = v___y_3262_;
v___y_3085_ = v___x_3313_;
v___y_3086_ = v___y_3264_;
v___y_3087_ = v___x_3310_;
v___y_3088_ = v_a_3306_;
v___y_3089_ = v___x_3308_;
v___y_3090_ = v___x_3309_;
v___y_3091_ = v___x_3316_;
goto v___jp_3077_;
}
else
{
lean_object* v_val_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_val_3317_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3317_);
lean_dec_ref_known(v___y_3266_, 1);
v___x_3318_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___x_3319_ = lean_array_push(v___x_3318_, v_val_3317_);
v___y_3078_ = v___y_3252_;
v___y_3079_ = v___y_3253_;
v___y_3080_ = v___x_3315_;
v___y_3081_ = v___y_3255_;
v___y_3082_ = v___y_3257_;
v___y_3083_ = v_val_3304_;
v___y_3084_ = v___y_3262_;
v___y_3085_ = v___x_3313_;
v___y_3086_ = v___y_3264_;
v___y_3087_ = v___x_3310_;
v___y_3088_ = v_a_3306_;
v___y_3089_ = v___x_3308_;
v___y_3090_ = v___x_3309_;
v___y_3091_ = v___x_3319_;
goto v___jp_3077_;
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_val_3304_);
lean_dec(v___y_3266_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___x_2856_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3320_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3305_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3305_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
else
{
lean_object* v___x_3328_; 
lean_dec_ref(v___x_2856_);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3255_);
v___x_3328_ = lean_apply_9(v___f_2855_, v___y_3265_, v___y_3259_, v___y_3254_, v___y_3261_, v___y_3258_, v___y_3256_, v___y_3255_, v___y_3252_, lean_box(0));
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc_n(v_a_3329_, 2);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__10));
lean_inc_ref(v___x_2849_);
lean_inc_ref(v___x_2848_);
lean_inc_ref(v___x_2847_);
v___x_3331_ = l_Lean_Name_mkStr4(v___x_2847_, v___x_2848_, v___x_2849_, v___x_3330_);
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__11));
v___x_3333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3333_, 0, v_a_3329_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
if (lean_obj_tag(v___y_3266_) == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3008_ = v_a_3329_;
v___y_3009_ = v___y_3252_;
v___y_3010_ = v___y_3262_;
v___y_3011_ = v___y_3253_;
v___y_3012_ = v___y_3263_;
v___y_3013_ = v___x_3331_;
v___y_3014_ = v___y_3255_;
v___y_3015_ = v___y_3264_;
v___y_3016_ = v___y_3257_;
v___y_3017_ = v___x_3333_;
v___y_3018_ = v___x_3334_;
goto v___jp_3007_;
}
else
{
lean_object* v_val_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_val_3335_ = lean_ctor_get(v___y_3266_, 0);
lean_inc(v_val_3335_);
lean_dec_ref_known(v___y_3266_, 1);
v___x_3336_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___x_3337_ = lean_array_push(v___x_3336_, v_val_3335_);
v___y_3008_ = v_a_3329_;
v___y_3009_ = v___y_3252_;
v___y_3010_ = v___y_3262_;
v___y_3011_ = v___y_3253_;
v___y_3012_ = v___y_3263_;
v___y_3013_ = v___x_3331_;
v___y_3014_ = v___y_3255_;
v___y_3015_ = v___y_3264_;
v___y_3016_ = v___y_3257_;
v___y_3017_ = v___x_3333_;
v___y_3018_ = v___x_3337_;
goto v___jp_3007_;
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v___y_3266_);
lean_dec(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3338_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3328_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3328_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
}
v___jp_3346_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3363_ = lean_unsigned_to_nat(5u);
v___x_3364_ = l_Lean_Syntax_getArg(v___y_3353_, v___x_3363_);
lean_dec(v___y_3353_);
v___x_3365_ = l_Lean_Syntax_matchesNull(v___x_3364_, v___x_2850_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec(v_args_3354_);
lean_dec(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3367_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3366_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
v___y_2909_ = v___y_3348_;
v_stx_2910_ = v_a_3368_;
v___y_2911_ = v___y_3361_;
v___y_2912_ = v___y_3362_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec_ref(v___y_3348_);
lean_dec(v_tk_2846_);
v_a_3369_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3367_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3367_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_Syntax_getOptional_x3f(v___y_3351_);
lean_dec(v___y_3351_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_box(0);
v___y_3252_ = v___y_3362_;
v___y_3253_ = v___y_3350_;
v___y_3254_ = v___y_3357_;
v___y_3255_ = v___y_3361_;
v___y_3256_ = v___y_3360_;
v___y_3257_ = v___y_3352_;
v___y_3258_ = v___y_3359_;
v___y_3259_ = v___y_3356_;
v___y_3260_ = v___y_3347_;
v___y_3261_ = v___y_3358_;
v___y_3262_ = v___y_3348_;
v___y_3263_ = v___y_3349_;
v___y_3264_ = v_args_3354_;
v___y_3265_ = v___y_3355_;
v___y_3266_ = v___x_3378_;
goto v___jp_3251_;
}
else
{
lean_object* v_val_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_val_3379_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3377_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_val_3379_);
lean_dec(v___x_3377_);
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
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_val_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
v___y_3252_ = v___y_3362_;
v___y_3253_ = v___y_3350_;
v___y_3254_ = v___y_3357_;
v___y_3255_ = v___y_3361_;
v___y_3256_ = v___y_3360_;
v___y_3257_ = v___y_3352_;
v___y_3258_ = v___y_3359_;
v___y_3259_ = v___y_3356_;
v___y_3260_ = v___y_3347_;
v___y_3261_ = v___y_3358_;
v___y_3262_ = v___y_3348_;
v___y_3263_ = v___y_3349_;
v___y_3264_ = v_args_3354_;
v___y_3265_ = v___y_3355_;
v___y_3266_ = v___x_3384_;
goto v___jp_3251_;
}
}
}
}
}
v___jp_3387_:
{
lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3403_ = l_Lean_Syntax_getArg(v___y_3393_, v___x_2857_);
v___x_3404_ = l_Lean_Syntax_isNone(v___x_3403_);
if (v___x_3404_ == 0)
{
uint8_t v___x_3405_; 
lean_inc(v___x_3403_);
v___x_3405_ = l_Lean_Syntax_matchesNull(v___x_3403_, v___x_2858_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
lean_dec(v___x_3403_);
lean_dec(v_only_3394_);
lean_dec(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3407_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3406_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v___y_2909_ = v___y_3389_;
v_stx_2910_ = v_a_3408_;
v___y_2911_ = v___y_3401_;
v___y_2912_ = v___y_3402_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___y_3389_);
lean_dec(v_tk_2846_);
v_a_3409_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3407_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = l_Lean_Syntax_getArg(v___x_3403_, v___x_2859_);
lean_dec(v___x_2859_);
lean_dec(v___x_3403_);
v___x_3418_ = l_Lean_Syntax_getArgs(v___x_3417_);
lean_dec(v___x_3417_);
v___x_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
v___y_3347_ = v___y_3388_;
v___y_3348_ = v___y_3389_;
v___y_3349_ = v___y_3390_;
v___y_3350_ = v_only_3394_;
v___y_3351_ = v___y_3391_;
v___y_3352_ = v___y_3392_;
v___y_3353_ = v___y_3393_;
v_args_3354_ = v___x_3419_;
v___y_3355_ = v___y_3395_;
v___y_3356_ = v___y_3396_;
v___y_3357_ = v___y_3397_;
v___y_3358_ = v___y_3398_;
v___y_3359_ = v___y_3399_;
v___y_3360_ = v___y_3400_;
v___y_3361_ = v___y_3401_;
v___y_3362_ = v___y_3402_;
goto v___jp_3346_;
}
}
else
{
lean_object* v___x_3420_; 
lean_dec(v___x_3403_);
lean_dec(v___x_2859_);
v___x_3420_ = lean_box(0);
v___y_3347_ = v___y_3388_;
v___y_3348_ = v___y_3389_;
v___y_3349_ = v___y_3390_;
v___y_3350_ = v_only_3394_;
v___y_3351_ = v___y_3391_;
v___y_3352_ = v___y_3392_;
v___y_3353_ = v___y_3393_;
v_args_3354_ = v___x_3420_;
v___y_3355_ = v___y_3395_;
v___y_3356_ = v___y_3396_;
v___y_3357_ = v___y_3397_;
v___y_3358_ = v___y_3398_;
v___y_3359_ = v___y_3399_;
v___y_3360_ = v___y_3400_;
v___y_3361_ = v___y_3401_;
v___y_3362_ = v___y_3402_;
goto v___jp_3346_;
}
}
v___jp_3421_:
{
lean_object* v_usedTheorems_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_usedTheorems_3426_ = lean_ctor_get(v___y_3423_, 0);
v___x_3427_ = l_Lean_Syntax_unsetTrailing(v___y_3424_);
v___x_3428_ = l_Lean_Elab_Tactic_mkSimpOnly(v___x_3427_, v_usedTheorems_3426_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; uint8_t v___x_3430_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc_n(v_a_3429_, 2);
lean_dec_ref_known(v___x_3428_, 1);
v___x_3430_ = l_Lean_Syntax_isOfKind(v_a_3429_, v___x_2942_);
lean_dec(v___x_2942_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_inc(v_ref_2938_);
lean_dec(v_a_3429_);
lean_dec(v___y_3425_);
lean_dec(v___x_2861_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3431_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3432_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3431_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
v___y_2886_ = v___y_3423_;
v_stx_2887_ = v_a_3433_;
v___y_2888_ = v___y_2878_;
v_ref_2889_ = v_ref_2938_;
v___y_2890_ = v___y_2879_;
goto v___jp_2885_;
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v___y_3423_);
lean_dec(v_ref_2938_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v_tk_2846_);
v_a_3434_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3432_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3432_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = l_Lean_Syntax_getArg(v_a_3429_, v___x_2859_);
lean_inc(v___x_3442_);
v___x_3443_ = l_Lean_Syntax_isOfKind(v___x_3442_, v___x_2860_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_inc(v_ref_2938_);
lean_dec(v___x_3442_);
lean_dec(v_a_3429_);
lean_dec(v___y_3425_);
lean_dec(v___x_2861_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3444_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3445_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3444_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___y_2886_ = v___y_3423_;
v_stx_2887_ = v_a_3446_;
v___y_2888_ = v___y_2878_;
v_ref_2889_ = v_ref_2938_;
v___y_2890_ = v___y_2879_;
goto v___jp_2885_;
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v___y_3423_);
lean_dec(v_ref_2938_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v_tk_2846_);
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
lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3455_ = l_Lean_Syntax_getArg(v_a_3429_, v___x_2861_);
lean_dec(v___x_2861_);
v___x_3456_ = l_Lean_Syntax_getArg(v_a_3429_, v___x_2858_);
v___x_3457_ = l_Lean_Syntax_isNone(v___x_3456_);
if (v___x_3457_ == 0)
{
uint8_t v___x_3458_; 
lean_inc(v___x_3456_);
v___x_3458_ = l_Lean_Syntax_matchesNull(v___x_3456_, v___x_2859_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_inc(v_ref_2938_);
lean_dec(v___x_3456_);
lean_dec(v___x_3455_);
lean_dec(v___x_3442_);
lean_dec(v_a_3429_);
lean_dec(v___y_3425_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
v___x_3459_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__12);
v___x_3460_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_3459_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___y_2886_ = v___y_3423_;
v_stx_2887_ = v_a_3461_;
v___y_2888_ = v___y_2878_;
v_ref_2889_ = v_ref_2938_;
v___y_2890_ = v___y_2879_;
goto v___jp_2885_;
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v___y_3423_);
lean_dec(v_ref_2938_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v_tk_2846_);
v_a_3462_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3460_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
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
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = l_Lean_Syntax_getArg(v___x_3456_, v___x_2850_);
lean_dec(v___x_3456_);
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___y_3423_;
v___y_3390_ = v___y_3425_;
v___y_3391_ = v___x_3455_;
v___y_3392_ = v___x_3442_;
v___y_3393_ = v_a_3429_;
v_only_3394_ = v___x_3471_;
v___y_3395_ = v___y_2872_;
v___y_3396_ = v___y_2873_;
v___y_3397_ = v___y_2874_;
v___y_3398_ = v___y_2875_;
v___y_3399_ = v___y_2876_;
v___y_3400_ = v___y_2877_;
v___y_3401_ = v___y_2878_;
v___y_3402_ = v___y_2879_;
goto v___jp_3387_;
}
}
else
{
lean_object* v___x_3472_; 
lean_dec(v___x_3456_);
v___x_3472_ = lean_box(0);
v___y_3388_ = v___y_3422_;
v___y_3389_ = v___y_3423_;
v___y_3390_ = v___y_3425_;
v___y_3391_ = v___x_3455_;
v___y_3392_ = v___x_3442_;
v___y_3393_ = v_a_3429_;
v_only_3394_ = v___x_3472_;
v___y_3395_ = v___y_2872_;
v___y_3396_ = v___y_2873_;
v___y_3397_ = v___y_2874_;
v___y_3398_ = v___y_2875_;
v___y_3399_ = v___y_2876_;
v___y_3400_ = v___y_2877_;
v___y_3401_ = v___y_2878_;
v___y_3402_ = v___y_2879_;
goto v___jp_3387_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3423_);
lean_dec(v___x_2942_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___x_2861_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3473_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3428_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3428_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
v___jp_3481_:
{
if (lean_obj_tag(v_usingArg_2862_) == 0)
{
v___y_3422_ = v___y_3482_;
v___y_3423_ = v___y_3483_;
v___y_3424_ = v___y_3484_;
v___y_3425_ = v_usingArg_2862_;
goto v___jp_3421_;
}
else
{
lean_object* v_val_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3493_; 
v_val_3485_ = lean_ctor_get(v_usingArg_2862_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_usingArg_2862_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3487_ = v_usingArg_2862_;
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_val_3485_);
lean_dec(v_usingArg_2862_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3493_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = l_Lean_Syntax_unsetTrailing(v_val_3485_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v___x_3489_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
v___y_3422_ = v___y_3482_;
v___y_3423_ = v___y_3483_;
v___y_3424_ = v___y_3484_;
v___y_3425_ = v___x_3491_;
goto v___jp_3421_;
}
}
}
}
v___jp_3494_:
{
if (v___y_3498_ == 0)
{
lean_dec(v___y_3497_);
lean_dec(v___x_2942_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_usingArg_2862_);
lean_dec(v___x_2861_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v___y_2882_ = v___y_3496_;
goto v___jp_2881_;
}
else
{
v___y_3482_ = v___y_3495_;
v___y_3483_ = v___y_3496_;
v___y_3484_ = v___y_3497_;
goto v___jp_3481_;
}
}
v___jp_3499_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; 
v___x_3505_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_3504_, v___x_2939_);
v___x_3506_ = lean_box(v___x_2851_);
v___x_3507_ = lean_box(v___x_2939_);
v___x_3508_ = lean_box(v_useReducible_2854_);
v___x_3509_ = lean_box(v___x_2864_);
lean_inc_ref(v___x_2849_);
lean_inc_ref(v___x_2848_);
lean_inc_ref(v___x_2847_);
lean_inc_ref(v___f_2855_);
lean_inc(v___x_2859_);
lean_inc_ref(v___x_2856_);
lean_inc(v_usingArg_2862_);
lean_inc(v___x_2850_);
lean_inc(v_tk_2846_);
lean_inc(v___x_2861_);
v___f_3510_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed), 30, 20);
lean_closure_set(v___f_3510_, 0, v___x_2861_);
lean_closure_set(v___f_3510_, 1, v_tk_2846_);
lean_closure_set(v___f_3510_, 2, v___x_2944_);
lean_closure_set(v___f_3510_, 3, v___x_2850_);
lean_closure_set(v___f_3510_, 4, v___x_3505_);
lean_closure_set(v___f_3510_, 5, v___y_3500_);
lean_closure_set(v___f_3510_, 6, v___x_3506_);
lean_closure_set(v___f_3510_, 7, v_usingArg_2862_);
lean_closure_set(v___f_3510_, 8, v___x_3507_);
lean_closure_set(v___f_3510_, 9, v___x_2856_);
lean_closure_set(v___f_3510_, 10, v___x_3508_);
lean_closure_set(v___f_3510_, 11, v___x_3509_);
lean_closure_set(v___f_3510_, 12, v___x_2859_);
lean_closure_set(v___f_3510_, 13, v___f_2855_);
lean_closure_set(v___f_3510_, 14, v___x_2847_);
lean_closure_set(v___f_3510_, 15, v___x_2848_);
lean_closure_set(v___f_3510_, 16, v___x_2849_);
lean_closure_set(v___f_3510_, 17, v___f_2865_);
lean_closure_set(v___f_3510_, 18, v_a_2936_);
lean_closure_set(v___f_3510_, 19, v_usingTk_x3f_2866_);
v___x_3511_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v___y_3502_, v___f_3510_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_3502_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_Elab_Tactic_tactic_simp_trace;
v___x_3514_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1_spec__3(v_options_2937_, v___x_3513_);
if (v___x_3514_ == 0)
{
if (lean_obj_tag(v_squeeze_2867_) == 0)
{
v___y_3495_ = v___y_3501_;
v___y_3496_ = v_a_3512_;
v___y_3497_ = v___y_3503_;
v___y_3498_ = v___x_3514_;
goto v___jp_3494_;
}
else
{
v___y_3495_ = v___y_3501_;
v___y_3496_ = v_a_3512_;
v___y_3497_ = v___y_3503_;
v___y_3498_ = v___x_2864_;
goto v___jp_3494_;
}
}
else
{
v___y_3482_ = v___y_3501_;
v___y_3483_ = v_a_3512_;
v___y_3484_ = v___y_3503_;
goto v___jp_3481_;
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec(v___y_3503_);
lean_dec(v___x_2942_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_usingArg_2862_);
lean_dec(v___x_2861_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3515_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3511_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3511_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
v___jp_3523_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3527_ = l_Array_append___redArg(v___x_2945_, v___y_3526_);
lean_dec_ref(v___y_3526_);
lean_inc_n(v___x_2940_, 2);
v___x_3528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3528_, 0, v___x_2940_);
lean_ctor_set(v___x_3528_, 1, v___x_2944_);
lean_ctor_set(v___x_3528_, 2, v___x_3527_);
v___x_3529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3529_, 0, v___x_2940_);
lean_ctor_set(v___x_3529_, 1, v___x_2944_);
lean_ctor_set(v___x_3529_, 2, v___x_2945_);
lean_inc(v___x_2942_);
v___x_3530_ = l_Lean_Syntax_node6(v___x_2940_, v___x_2942_, v___x_2943_, v___x_2863_, v___y_3525_, v___y_3524_, v___x_3528_, v___x_3529_);
v___x_3531_ = 0;
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__13));
v___x_3533_ = lean_box(v___x_2939_);
v___x_3534_ = lean_box(v___x_3531_);
v___x_3535_ = lean_box(v___x_2939_);
lean_inc(v___x_3530_);
v___x_3536_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_3536_, 0, v___x_3530_);
lean_closure_set(v___x_3536_, 1, v___x_3533_);
lean_closure_set(v___x_3536_, 2, v___x_3534_);
lean_closure_set(v___x_3536_, 3, v___x_3535_);
lean_closure_set(v___x_3536_, 4, v___x_3532_);
v___x_3537_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_3536_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
if (lean_obj_tag(v_unfold_2868_) == 0)
{
lean_object* v_ctx_3539_; lean_object* v_simprocs_3540_; lean_object* v_dischargeWrapper_3541_; 
v_ctx_3539_ = lean_ctor_get(v_a_3538_, 0);
lean_inc_ref(v_ctx_3539_);
v_simprocs_3540_ = lean_ctor_get(v_a_3538_, 1);
lean_inc_ref(v_simprocs_3540_);
v_dischargeWrapper_3541_ = lean_ctor_get(v_a_3538_, 2);
lean_inc(v_dischargeWrapper_3541_);
lean_dec(v_a_3538_);
v___y_3500_ = v_simprocs_3540_;
v___y_3501_ = v___x_2939_;
v___y_3502_ = v_dischargeWrapper_3541_;
v___y_3503_ = v___x_3530_;
v___y_3504_ = v_ctx_3539_;
goto v___jp_3499_;
}
else
{
if (v___x_2864_ == 0)
{
lean_object* v_ctx_3542_; lean_object* v_simprocs_3543_; lean_object* v_dischargeWrapper_3544_; 
v_ctx_3542_ = lean_ctor_get(v_a_3538_, 0);
lean_inc_ref(v_ctx_3542_);
v_simprocs_3543_ = lean_ctor_get(v_a_3538_, 1);
lean_inc_ref(v_simprocs_3543_);
v_dischargeWrapper_3544_ = lean_ctor_get(v_a_3538_, 2);
lean_inc(v_dischargeWrapper_3544_);
lean_dec(v_a_3538_);
v___y_3500_ = v_simprocs_3543_;
v___y_3501_ = v___x_2864_;
v___y_3502_ = v_dischargeWrapper_3544_;
v___y_3503_ = v___x_3530_;
v___y_3504_ = v_ctx_3542_;
goto v___jp_3499_;
}
else
{
lean_object* v_ctx_3545_; lean_object* v_simprocs_3546_; lean_object* v_dischargeWrapper_3547_; lean_object* v___x_3548_; 
v_ctx_3545_ = lean_ctor_get(v_a_3538_, 0);
lean_inc_ref(v_ctx_3545_);
v_simprocs_3546_ = lean_ctor_get(v_a_3538_, 1);
lean_inc_ref(v_simprocs_3546_);
v_dischargeWrapper_3547_ = lean_ctor_get(v_a_3538_, 2);
lean_inc(v_dischargeWrapper_3547_);
lean_dec(v_a_3538_);
v___x_3548_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_3545_);
v___y_3500_ = v_simprocs_3546_;
v___y_3501_ = v___x_2864_;
v___y_3502_ = v_dischargeWrapper_3547_;
v___y_3503_ = v___x_3530_;
v___y_3504_ = v___x_3548_;
goto v___jp_3499_;
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec(v___x_3530_);
lean_dec(v___x_2942_);
lean_dec(v_a_2936_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_usingTk_x3f_2866_);
lean_dec_ref(v___f_2865_);
lean_dec(v_usingArg_2862_);
lean_dec(v___x_2861_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3549_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3537_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3537_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
v___jp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = l_Array_append___redArg(v___x_2945_, v___y_3559_);
lean_dec_ref(v___y_3559_);
lean_inc(v___x_2940_);
v___x_3561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3561_, 0, v___x_2940_);
lean_ctor_set(v___x_3561_, 1, v___x_2944_);
lean_ctor_set(v___x_3561_, 2, v___x_3560_);
if (lean_obj_tag(v_args_2869_) == 1)
{
lean_object* v_val_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_val_3562_ = lean_ctor_get(v_args_2869_, 0);
v___x_3563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___x_2940_, 3);
v___x_3564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_2940_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = l_Array_append___redArg(v___x_2945_, v_val_3562_);
v___x_3566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3566_, 0, v___x_2940_);
lean_ctor_set(v___x_3566_, 1, v___x_2944_);
lean_ctor_set(v___x_3566_, 2, v___x_3565_);
v___x_3567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_3568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_2940_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Array_mkArray3___redArg(v___x_3564_, v___x_3566_, v___x_3568_);
v___y_3524_ = v___x_3561_;
v___y_3525_ = v___y_3558_;
v___y_3526_ = v___x_3569_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3524_ = v___x_3561_;
v___y_3525_ = v___y_3558_;
v___y_3526_ = v___x_3570_;
goto v___jp_3523_;
}
}
v___jp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = l_Array_append___redArg(v___x_2945_, v___y_3572_);
lean_dec_ref(v___y_3572_);
lean_inc(v___x_2940_);
v___x_3574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3574_, 0, v___x_2940_);
lean_ctor_set(v___x_3574_, 1, v___x_2944_);
lean_ctor_set(v___x_3574_, 2, v___x_3573_);
if (lean_obj_tag(v_only_2870_) == 1)
{
lean_object* v_val_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_val_3575_ = lean_ctor_get(v_only_2870_, 0);
v___x_3576_ = l_Lean_SourceInfo_fromRef(v_val_3575_, v___x_2851_);
v___x_3577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_3578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3576_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Array_mkArray1___redArg(v___x_3578_);
v___y_3558_ = v___x_3574_;
v___y_3559_ = v___x_3579_;
goto v___jp_3557_;
}
else
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_mk_empty_array_with_capacity(v___x_2850_);
v___y_3558_ = v___x_3574_;
v___y_3559_ = v___x_3580_;
goto v___jp_3557_;
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec(v_usingTk_x3f_2866_);
lean_dec_ref(v___f_2865_);
lean_dec(v___x_2863_);
lean_dec(v_usingArg_2862_);
lean_dec(v___x_2861_);
lean_dec(v___x_2859_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___f_2855_);
lean_dec(v___x_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2847_);
lean_dec(v_tk_2846_);
v_a_3585_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_2935_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_2935_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
v___jp_2881_:
{
lean_object* v_diag_2883_; lean_object* v___x_2884_; 
v_diag_2883_ = lean_ctor_get(v___y_2882_, 1);
lean_inc_ref(v_diag_2883_);
lean_dec_ref(v___y_2882_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v_diag_2883_);
return v___x_2884_;
}
v___jp_2885_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa___closed__3));
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v_stx_2887_);
v___x_2893_ = lean_box(0);
v___x_2894_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
lean_ctor_set(v___x_2894_, 2, v___x_2893_);
lean_ctor_set(v___x_2894_, 3, v___x_2893_);
lean_ctor_set(v___x_2894_, 4, v___x_2893_);
lean_ctor_set(v___x_2894_, 5, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_ref_2889_);
v___x_2896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__0));
v___x_2897_ = 4;
v___x_2898_ = l_Lean_MessageData_nil;
v___x_2899_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_2846_, v___x_2894_, v___x_2895_, v___x_2896_, v___x_2893_, v___x_2897_, v___x_2898_, v___y_2888_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2888_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_dec_ref_known(v___x_2899_, 1);
v___y_2882_ = v___y_2886_;
goto v___jp_2881_;
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v___y_2886_);
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
v___jp_2908_:
{
lean_object* v_ref_2913_; 
v_ref_2913_ = lean_ctor_get(v___y_2911_, 5);
lean_inc(v_ref_2913_);
v___y_2886_ = v___y_2909_;
v_stx_2887_ = v_stx_2910_;
v___y_2888_ = v___y_2911_;
v_ref_2889_ = v_ref_2913_;
v___y_2890_ = v___y_2912_;
goto v___jp_2885_;
}
v___jp_2914_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__4);
v___x_2925_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v___x_2924_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___y_2909_ = v___y_2915_;
v_stx_2910_ = v_a_2926_;
v___y_2911_ = v___y_2922_;
v___y_2912_ = v___y_2923_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec_ref(v___y_2915_);
lean_dec(v_tk_2846_);
v_a_2927_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2925_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2925_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed(lean_object** _args){
lean_object* v_tk_3593_ = _args[0];
lean_object* v___x_3594_ = _args[1];
lean_object* v___x_3595_ = _args[2];
lean_object* v___x_3596_ = _args[3];
lean_object* v___x_3597_ = _args[4];
lean_object* v___x_3598_ = _args[5];
lean_object* v___x_3599_ = _args[6];
lean_object* v___x_3600_ = _args[7];
lean_object* v_useReducible_3601_ = _args[8];
lean_object* v___f_3602_ = _args[9];
lean_object* v___x_3603_ = _args[10];
lean_object* v___x_3604_ = _args[11];
lean_object* v___x_3605_ = _args[12];
lean_object* v___x_3606_ = _args[13];
lean_object* v___x_3607_ = _args[14];
lean_object* v___x_3608_ = _args[15];
lean_object* v_usingArg_3609_ = _args[16];
lean_object* v___x_3610_ = _args[17];
lean_object* v___x_3611_ = _args[18];
lean_object* v___f_3612_ = _args[19];
lean_object* v_usingTk_x3f_3613_ = _args[20];
lean_object* v_squeeze_3614_ = _args[21];
lean_object* v_unfold_3615_ = _args[22];
lean_object* v_args_3616_ = _args[23];
lean_object* v_only_3617_ = _args[24];
lean_object* v___y_3618_ = _args[25];
lean_object* v___y_3619_ = _args[26];
lean_object* v___y_3620_ = _args[27];
lean_object* v___y_3621_ = _args[28];
lean_object* v___y_3622_ = _args[29];
lean_object* v___y_3623_ = _args[30];
lean_object* v___y_3624_ = _args[31];
lean_object* v___y_3625_ = _args[32];
lean_object* v___y_3626_ = _args[33];
lean_object* v___y_3627_ = _args[34];
_start:
{
uint8_t v___x_94169__boxed_3628_; uint8_t v_useReducible_boxed_3629_; uint8_t v___x_94180__boxed_3630_; lean_object* v_res_3631_; 
v___x_94169__boxed_3628_ = lean_unbox(v___x_3598_);
v_useReducible_boxed_3629_ = lean_unbox(v_useReducible_3601_);
v___x_94180__boxed_3630_ = lean_unbox(v___x_3611_);
v_res_3631_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7(v_tk_3593_, v___x_3594_, v___x_3595_, v___x_3596_, v___x_3597_, v___x_94169__boxed_3628_, v___x_3599_, v___x_3600_, v_useReducible_boxed_3629_, v___f_3602_, v___x_3603_, v___x_3604_, v___x_3605_, v___x_3606_, v___x_3607_, v___x_3608_, v_usingArg_3609_, v___x_3610_, v___x_94180__boxed_3630_, v___f_3612_, v_usingTk_x3f_3613_, v_squeeze_3614_, v_unfold_3615_, v_args_3616_, v_only_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v_only_3617_);
lean_dec(v_args_3616_);
lean_dec(v_unfold_3615_);
lean_dec(v_squeeze_3614_);
lean_dec(v___x_3607_);
lean_dec(v___x_3605_);
lean_dec(v___x_3604_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(uint8_t v_useReducible_3657_, lean_object* v_stx_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_initFn___closed__5_00___x40_Lean_Elab_Tactic_Simpa_2098002731____hygCtx___hyg_4_));
v___x_3669_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0));
v___x_3670_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_logUnnecessarySimpa_spec__0_spec__0_spec__1___redArg___lam__0___closed__1));
v___x_3671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_3672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
lean_inc(v_stx_3658_);
v___x_3673_ = l_Lean_Syntax_isOfKind(v_stx_3658_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; 
lean_dec(v_stx_3658_);
v___x_3674_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3674_;
}
else
{
lean_object* v___f_3675_; lean_object* v___x_3676_; lean_object* v_tk_3677_; lean_object* v___x_3678_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; uint8_t v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; uint8_t v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_usingTk_x3f_3732_; lean_object* v_usingArg_3733_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; uint8_t v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_args_3765_; lean_object* v___y_3777_; lean_object* v___y_3778_; uint8_t v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v_only_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v_unfold_3821_; lean_object* v_squeeze_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___f_3675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3));
v___x_3676_ = lean_unsigned_to_nat(0u);
v_tk_3677_ = l_Lean_Syntax_getArg(v_stx_3658_, v___x_3676_);
v___x_3678_ = lean_unsigned_to_nat(1u);
v___x_3857_ = l_Lean_Syntax_getArg(v_stx_3658_, v___x_3678_);
v___x_3858_ = l_Lean_Syntax_isNone(v___x_3857_);
if (v___x_3858_ == 0)
{
uint8_t v___x_3859_; 
lean_inc(v___x_3857_);
v___x_3859_ = l_Lean_Syntax_matchesNull(v___x_3857_, v___x_3678_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; 
lean_dec(v___x_3857_);
lean_dec(v_tk_3677_);
lean_dec(v_stx_3658_);
v___x_3860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3860_;
}
else
{
lean_object* v_squeeze_3861_; lean_object* v___x_3862_; 
v_squeeze_3861_ = l_Lean_Syntax_getArg(v___x_3857_, v___x_3676_);
lean_dec(v___x_3857_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_squeeze_3861_);
v_squeeze_3840_ = v___x_3862_;
v___y_3841_ = v_a_3659_;
v___y_3842_ = v_a_3660_;
v___y_3843_ = v_a_3661_;
v___y_3844_ = v_a_3662_;
v___y_3845_ = v_a_3663_;
v___y_3846_ = v_a_3664_;
v___y_3847_ = v_a_3665_;
v___y_3848_ = v_a_3666_;
goto v___jp_3839_;
}
}
else
{
lean_object* v___x_3863_; 
lean_dec(v___x_3857_);
v___x_3863_ = lean_box(0);
v_squeeze_3840_ = v___x_3863_;
v___y_3841_ = v_a_3659_;
v___y_3842_ = v_a_3660_;
v___y_3843_ = v_a_3661_;
v___y_3844_ = v_a_3662_;
v___y_3845_ = v_a_3663_;
v___y_3846_ = v_a_3664_;
v___y_3847_ = v_a_3665_;
v___y_3848_ = v_a_3666_;
goto v___jp_3839_;
}
v___jp_3679_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___f_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___f_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3702_ = lean_box(v___x_3673_);
v___x_3703_ = lean_box(v___y_3690_);
lean_inc(v___y_3697_);
lean_inc(v___y_3698_);
lean_inc(v___y_3701_);
lean_inc(v___y_3692_);
lean_inc(v___y_3682_);
lean_inc(v___y_3688_);
v___f_3704_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed), 22, 12);
lean_closure_set(v___f_3704_, 0, v___y_3688_);
lean_closure_set(v___f_3704_, 1, v___x_3676_);
lean_closure_set(v___f_3704_, 2, v___y_3682_);
lean_closure_set(v___f_3704_, 3, v___y_3692_);
lean_closure_set(v___f_3704_, 4, v___x_3702_);
lean_closure_set(v___f_3704_, 5, v___x_3668_);
lean_closure_set(v___f_3704_, 6, v___x_3669_);
lean_closure_set(v___f_3704_, 7, v___x_3670_);
lean_closure_set(v___f_3704_, 8, v___y_3701_);
lean_closure_set(v___f_3704_, 9, v___y_3698_);
lean_closure_set(v___f_3704_, 10, v___x_3703_);
lean_closure_set(v___f_3704_, 11, v___y_3697_);
v___x_3705_ = lean_box(v___x_3673_);
v___x_3706_ = lean_box(v_useReducible_3657_);
v___x_3707_ = lean_box(v___y_3690_);
lean_inc(v___y_3680_);
lean_inc(v___y_3694_);
v___f_3708_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___boxed), 35, 26);
lean_closure_set(v___f_3708_, 0, v_tk_3677_);
lean_closure_set(v___f_3708_, 1, v___x_3668_);
lean_closure_set(v___f_3708_, 2, v___x_3669_);
lean_closure_set(v___f_3708_, 3, v___x_3670_);
lean_closure_set(v___f_3708_, 4, v___x_3676_);
lean_closure_set(v___f_3708_, 5, v___x_3705_);
lean_closure_set(v___f_3708_, 6, v___y_3694_);
lean_closure_set(v___f_3708_, 7, v___x_3672_);
lean_closure_set(v___f_3708_, 8, v___x_3706_);
lean_closure_set(v___f_3708_, 9, v___f_3675_);
lean_closure_set(v___f_3708_, 10, v___x_3671_);
lean_closure_set(v___f_3708_, 11, v___y_3691_);
lean_closure_set(v___f_3708_, 12, v___y_3696_);
lean_closure_set(v___f_3708_, 13, v___x_3678_);
lean_closure_set(v___f_3708_, 14, v___y_3680_);
lean_closure_set(v___f_3708_, 15, v___y_3683_);
lean_closure_set(v___f_3708_, 16, v___y_3685_);
lean_closure_set(v___f_3708_, 17, v___y_3688_);
lean_closure_set(v___f_3708_, 18, v___x_3707_);
lean_closure_set(v___f_3708_, 19, v___f_3704_);
lean_closure_set(v___f_3708_, 20, v___y_3684_);
lean_closure_set(v___f_3708_, 21, v___y_3697_);
lean_closure_set(v___f_3708_, 22, v___y_3698_);
lean_closure_set(v___f_3708_, 23, v___y_3682_);
lean_closure_set(v___f_3708_, 24, v___y_3692_);
lean_closure_set(v___f_3708_, 25, v___y_3701_);
v___x_3709_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics___boxed), 10, 1);
lean_closure_set(v___x_3709_, 0, v___f_3708_);
v___x_3710_ = l_Lean_Elab_Tactic_focus___redArg(v___x_3709_, v___y_3689_, v___y_3681_, v___y_3695_, v___y_3687_, v___y_3686_, v___y_3700_, v___y_3693_, v___y_3699_);
return v___x_3710_;
}
v___jp_3711_:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Lean_Syntax_getOptional_x3f(v___y_3715_);
lean_dec(v___y_3715_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_box(0);
v___y_3680_ = v___y_3712_;
v___y_3681_ = v___y_3713_;
v___y_3682_ = v___y_3714_;
v___y_3683_ = v___y_3716_;
v___y_3684_ = v_usingTk_x3f_3732_;
v___y_3685_ = v_usingArg_3733_;
v___y_3686_ = v___y_3717_;
v___y_3687_ = v___y_3718_;
v___y_3688_ = v___y_3719_;
v___y_3689_ = v___y_3720_;
v___y_3690_ = v___y_3721_;
v___y_3691_ = v___y_3722_;
v___y_3692_ = v___y_3723_;
v___y_3693_ = v___y_3724_;
v___y_3694_ = v___y_3725_;
v___y_3695_ = v___y_3727_;
v___y_3696_ = v___y_3726_;
v___y_3697_ = v___y_3728_;
v___y_3698_ = v___y_3729_;
v___y_3699_ = v___y_3731_;
v___y_3700_ = v___y_3730_;
v___y_3701_ = v___x_3735_;
goto v___jp_3679_;
}
else
{
lean_object* v_val_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
v_val_3736_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3734_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_val_3736_);
lean_dec(v___x_3734_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_val_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
v___y_3680_ = v___y_3712_;
v___y_3681_ = v___y_3713_;
v___y_3682_ = v___y_3714_;
v___y_3683_ = v___y_3716_;
v___y_3684_ = v_usingTk_x3f_3732_;
v___y_3685_ = v_usingArg_3733_;
v___y_3686_ = v___y_3717_;
v___y_3687_ = v___y_3718_;
v___y_3688_ = v___y_3719_;
v___y_3689_ = v___y_3720_;
v___y_3690_ = v___y_3721_;
v___y_3691_ = v___y_3722_;
v___y_3692_ = v___y_3723_;
v___y_3693_ = v___y_3724_;
v___y_3694_ = v___y_3725_;
v___y_3695_ = v___y_3727_;
v___y_3696_ = v___y_3726_;
v___y_3697_ = v___y_3728_;
v___y_3698_ = v___y_3729_;
v___y_3699_ = v___y_3731_;
v___y_3700_ = v___y_3730_;
v___y_3701_ = v___x_3741_;
goto v___jp_3679_;
}
}
}
}
v___jp_3744_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3766_ = lean_unsigned_to_nat(4u);
v___x_3767_ = l_Lean_Syntax_getArg(v___y_3760_, v___x_3766_);
lean_dec(v___y_3760_);
v___x_3768_ = l_Lean_Syntax_isNone(v___x_3767_);
if (v___x_3768_ == 0)
{
uint8_t v___x_3769_; 
lean_inc(v___x_3767_);
v___x_3769_ = l_Lean_Syntax_matchesNull(v___x_3767_, v___y_3749_);
lean_dec(v___y_3749_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; 
lean_dec(v___x_3767_);
lean_dec(v_args_3765_);
lean_dec(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec(v___y_3759_);
lean_dec(v___y_3755_);
lean_dec(v___y_3752_);
lean_dec(v___y_3748_);
lean_dec(v___y_3747_);
lean_dec(v_tk_3677_);
v___x_3770_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3770_;
}
else
{
lean_object* v_usingTk_x3f_3771_; lean_object* v_usingArg_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v_usingTk_x3f_3771_ = l_Lean_Syntax_getArg(v___x_3767_, v___x_3676_);
v_usingArg_3772_ = l_Lean_Syntax_getArg(v___x_3767_, v___x_3678_);
lean_dec(v___x_3767_);
v___x_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3773_, 0, v_usingTk_x3f_3771_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v_usingArg_3772_);
v___y_3712_ = v___y_3745_;
v___y_3713_ = v___y_3746_;
v___y_3714_ = v_args_3765_;
v___y_3715_ = v___y_3747_;
v___y_3716_ = v___y_3748_;
v___y_3717_ = v___y_3750_;
v___y_3718_ = v___y_3751_;
v___y_3719_ = v___y_3752_;
v___y_3720_ = v___y_3753_;
v___y_3721_ = v___y_3754_;
v___y_3722_ = v___x_3766_;
v___y_3723_ = v___y_3755_;
v___y_3724_ = v___y_3756_;
v___y_3725_ = v___y_3757_;
v___y_3726_ = v___y_3759_;
v___y_3727_ = v___y_3758_;
v___y_3728_ = v___y_3761_;
v___y_3729_ = v___y_3762_;
v___y_3730_ = v___y_3764_;
v___y_3731_ = v___y_3763_;
v_usingTk_x3f_3732_ = v___x_3773_;
v_usingArg_3733_ = v___x_3774_;
goto v___jp_3711_;
}
}
else
{
lean_object* v___x_3775_; 
lean_dec(v___x_3767_);
lean_dec(v___y_3749_);
v___x_3775_ = lean_box(0);
v___y_3712_ = v___y_3745_;
v___y_3713_ = v___y_3746_;
v___y_3714_ = v_args_3765_;
v___y_3715_ = v___y_3747_;
v___y_3716_ = v___y_3748_;
v___y_3717_ = v___y_3750_;
v___y_3718_ = v___y_3751_;
v___y_3719_ = v___y_3752_;
v___y_3720_ = v___y_3753_;
v___y_3721_ = v___y_3754_;
v___y_3722_ = v___x_3766_;
v___y_3723_ = v___y_3755_;
v___y_3724_ = v___y_3756_;
v___y_3725_ = v___y_3757_;
v___y_3726_ = v___y_3759_;
v___y_3727_ = v___y_3758_;
v___y_3728_ = v___y_3761_;
v___y_3729_ = v___y_3762_;
v___y_3730_ = v___y_3764_;
v___y_3731_ = v___y_3763_;
v_usingTk_x3f_3732_ = v___x_3775_;
v_usingArg_3733_ = v___x_3775_;
goto v___jp_3711_;
}
}
v___jp_3776_:
{
lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = l_Lean_Syntax_getArg(v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
v___x_3799_ = l_Lean_Syntax_isNone(v___x_3798_);
if (v___x_3799_ == 0)
{
uint8_t v___x_3800_; 
lean_inc(v___x_3798_);
v___x_3800_ = l_Lean_Syntax_matchesNull(v___x_3798_, v___x_3678_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; 
lean_dec(v___x_3798_);
lean_dec(v_only_3789_);
lean_dec(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec(v___y_3777_);
lean_dec(v_tk_3677_);
v___x_3801_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3801_;
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3802_ = l_Lean_Syntax_getArg(v___x_3798_, v___x_3676_);
lean_dec(v___x_3798_);
v___x_3803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_3802_);
v___x_3804_ = l_Lean_Syntax_isOfKind(v___x_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; 
lean_dec(v___x_3802_);
lean_dec(v_only_3789_);
lean_dec(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec(v___y_3777_);
lean_dec(v_tk_3677_);
v___x_3805_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3805_;
}
else
{
lean_object* v___x_3806_; lean_object* v_args_3807_; lean_object* v___x_3808_; 
v___x_3806_ = l_Lean_Syntax_getArg(v___x_3802_, v___x_3678_);
lean_dec(v___x_3802_);
v_args_3807_ = l_Lean_Syntax_getArgs(v___x_3806_);
lean_dec(v___x_3806_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_args_3807_);
v___y_3745_ = v___y_3778_;
v___y_3746_ = v___y_3791_;
v___y_3747_ = v___y_3788_;
v___y_3748_ = v___y_3784_;
v___y_3749_ = v___y_3787_;
v___y_3750_ = v___y_3794_;
v___y_3751_ = v___y_3793_;
v___y_3752_ = v___y_3777_;
v___y_3753_ = v___y_3790_;
v___y_3754_ = v___y_3779_;
v___y_3755_ = v_only_3789_;
v___y_3756_ = v___y_3796_;
v___y_3757_ = v___y_3780_;
v___y_3758_ = v___y_3792_;
v___y_3759_ = v___y_3781_;
v___y_3760_ = v___y_3785_;
v___y_3761_ = v___y_3782_;
v___y_3762_ = v___y_3783_;
v___y_3763_ = v___y_3797_;
v___y_3764_ = v___y_3795_;
v_args_3765_ = v___x_3808_;
goto v___jp_3744_;
}
}
}
else
{
lean_object* v___x_3809_; 
lean_dec(v___x_3798_);
v___x_3809_ = lean_box(0);
v___y_3745_ = v___y_3778_;
v___y_3746_ = v___y_3791_;
v___y_3747_ = v___y_3788_;
v___y_3748_ = v___y_3784_;
v___y_3749_ = v___y_3787_;
v___y_3750_ = v___y_3794_;
v___y_3751_ = v___y_3793_;
v___y_3752_ = v___y_3777_;
v___y_3753_ = v___y_3790_;
v___y_3754_ = v___y_3779_;
v___y_3755_ = v_only_3789_;
v___y_3756_ = v___y_3796_;
v___y_3757_ = v___y_3780_;
v___y_3758_ = v___y_3792_;
v___y_3759_ = v___y_3781_;
v___y_3760_ = v___y_3785_;
v___y_3761_ = v___y_3782_;
v___y_3762_ = v___y_3783_;
v___y_3763_ = v___y_3797_;
v___y_3764_ = v___y_3795_;
v_args_3765_ = v___x_3809_;
goto v___jp_3744_;
}
}
v___jp_3810_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v___x_3822_ = lean_unsigned_to_nat(3u);
v___x_3823_ = l_Lean_Syntax_getArg(v_stx_3658_, v___x_3822_);
lean_dec(v_stx_3658_);
v___x_3824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
lean_inc(v___x_3823_);
v___x_3825_ = l_Lean_Syntax_isOfKind(v___x_3823_, v___x_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; 
lean_dec(v___x_3823_);
lean_dec(v_unfold_3821_);
lean_dec(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec(v_tk_3677_);
v___x_3826_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3826_;
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v___x_3827_ = l_Lean_Syntax_getArg(v___x_3823_, v___x_3676_);
v___x_3828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_3827_);
v___x_3829_ = l_Lean_Syntax_isOfKind(v___x_3827_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; 
lean_dec(v___x_3827_);
lean_dec(v___x_3823_);
lean_dec(v_unfold_3821_);
lean_dec(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec(v_tk_3677_);
v___x_3830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3830_;
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v___x_3831_ = l_Lean_Syntax_getArg(v___x_3823_, v___x_3678_);
v___x_3832_ = l_Lean_Syntax_getArg(v___x_3823_, v___y_3818_);
v___x_3833_ = l_Lean_Syntax_isNone(v___x_3832_);
if (v___x_3833_ == 0)
{
uint8_t v___x_3834_; 
lean_inc(v___x_3832_);
v___x_3834_ = l_Lean_Syntax_matchesNull(v___x_3832_, v___x_3678_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; 
lean_dec(v___x_3832_);
lean_dec(v___x_3831_);
lean_dec(v___x_3827_);
lean_dec(v___x_3823_);
lean_dec(v_unfold_3821_);
lean_dec(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec(v_tk_3677_);
v___x_3835_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3835_;
}
else
{
lean_object* v_only_3836_; lean_object* v___x_3837_; 
v_only_3836_ = l_Lean_Syntax_getArg(v___x_3832_, v___x_3676_);
lean_dec(v___x_3832_);
v___x_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3837_, 0, v_only_3836_);
lean_inc(v___y_3818_);
v___y_3777_ = v___x_3827_;
v___y_3778_ = v___x_3828_;
v___y_3779_ = v___x_3825_;
v___y_3780_ = v___x_3824_;
v___y_3781_ = v___x_3822_;
v___y_3782_ = v___y_3817_;
v___y_3783_ = v_unfold_3821_;
v___y_3784_ = v___y_3818_;
v___y_3785_ = v___x_3823_;
v___y_3786_ = v___x_3822_;
v___y_3787_ = v___y_3818_;
v___y_3788_ = v___x_3831_;
v_only_3789_ = v___x_3837_;
v___y_3790_ = v___y_3815_;
v___y_3791_ = v___y_3811_;
v___y_3792_ = v___y_3814_;
v___y_3793_ = v___y_3816_;
v___y_3794_ = v___y_3813_;
v___y_3795_ = v___y_3812_;
v___y_3796_ = v___y_3820_;
v___y_3797_ = v___y_3819_;
goto v___jp_3776_;
}
}
else
{
lean_object* v___x_3838_; 
lean_dec(v___x_3832_);
v___x_3838_ = lean_box(0);
lean_inc(v___y_3818_);
v___y_3777_ = v___x_3827_;
v___y_3778_ = v___x_3828_;
v___y_3779_ = v___x_3825_;
v___y_3780_ = v___x_3824_;
v___y_3781_ = v___x_3822_;
v___y_3782_ = v___y_3817_;
v___y_3783_ = v_unfold_3821_;
v___y_3784_ = v___y_3818_;
v___y_3785_ = v___x_3823_;
v___y_3786_ = v___x_3822_;
v___y_3787_ = v___y_3818_;
v___y_3788_ = v___x_3831_;
v_only_3789_ = v___x_3838_;
v___y_3790_ = v___y_3815_;
v___y_3791_ = v___y_3811_;
v___y_3792_ = v___y_3814_;
v___y_3793_ = v___y_3816_;
v___y_3794_ = v___y_3813_;
v___y_3795_ = v___y_3812_;
v___y_3796_ = v___y_3820_;
v___y_3797_ = v___y_3819_;
goto v___jp_3776_;
}
}
}
}
v___jp_3839_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3849_ = lean_unsigned_to_nat(2u);
v___x_3850_ = l_Lean_Syntax_getArg(v_stx_3658_, v___x_3849_);
v___x_3851_ = l_Lean_Syntax_isNone(v___x_3850_);
if (v___x_3851_ == 0)
{
uint8_t v___x_3852_; 
lean_inc(v___x_3850_);
v___x_3852_ = l_Lean_Syntax_matchesNull(v___x_3850_, v___x_3678_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; 
lean_dec(v___x_3850_);
lean_dec(v_squeeze_3840_);
lean_dec(v_tk_3677_);
lean_dec(v_stx_3658_);
v___x_3853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_3853_;
}
else
{
lean_object* v_unfold_3854_; lean_object* v___x_3855_; 
v_unfold_3854_ = l_Lean_Syntax_getArg(v___x_3850_, v___x_3676_);
lean_dec(v___x_3850_);
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v_unfold_3854_);
v___y_3811_ = v___y_3842_;
v___y_3812_ = v___y_3846_;
v___y_3813_ = v___y_3845_;
v___y_3814_ = v___y_3843_;
v___y_3815_ = v___y_3841_;
v___y_3816_ = v___y_3844_;
v___y_3817_ = v_squeeze_3840_;
v___y_3818_ = v___x_3849_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3847_;
v_unfold_3821_ = v___x_3855_;
goto v___jp_3810_;
}
}
else
{
lean_object* v___x_3856_; 
lean_dec(v___x_3850_);
v___x_3856_ = lean_box(0);
v___y_3811_ = v___y_3842_;
v___y_3812_ = v___y_3846_;
v___y_3813_ = v___y_3845_;
v___y_3814_ = v___y_3843_;
v___y_3815_ = v___y_3841_;
v___y_3816_ = v___y_3844_;
v___y_3817_ = v_squeeze_3840_;
v___y_3818_ = v___x_3849_;
v___y_3819_ = v___y_3848_;
v___y_3820_ = v___y_3847_;
v_unfold_3821_ = v___x_3856_;
goto v___jp_3810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(lean_object* v_useReducible_3864_, lean_object* v_stx_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
uint8_t v_useReducible_boxed_3875_; lean_object* v_res_3876_; 
v_useReducible_boxed_3875_ = lean_unbox(v_useReducible_3864_);
v_res_3876_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v_useReducible_boxed_3875_, v_stx_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(lean_object* v_mvarId_3877_, lean_object* v_val_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_3877_, v_val_3878_, v___y_3884_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(lean_object* v_mvarId_3889_, lean_object* v_val_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_3889_, v_val_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(lean_object* v_o_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_3901_, v___y_3909_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(lean_object* v_o_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(lean_object* v_00_u03b1_3923_, lean_object* v_msg_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_msg_3924_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(lean_object* v_00_u03b1_3935_, lean_object* v_msg_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_3935_, v_msg_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(lean_object* v_00_u03b1_3947_, lean_object* v_x_3948_, lean_object* v_mkInfoTree_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v_x_3948_, v_mkInfoTree_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(lean_object* v_00_u03b1_3960_, lean_object* v_x_3961_, lean_object* v_mkInfoTree_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v_00_u03b1_3960_, v_x_3961_, v_mkInfoTree_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(lean_object* v_00_u03b2_3973_, lean_object* v_x_3974_, lean_object* v_x_3975_, lean_object* v_x_3976_){
_start:
{
lean_object* v___x_3977_; 
v___x_3977_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_3974_, v_x_3975_, v_x_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(lean_object* v_00_u03b2_3978_, lean_object* v_m_3979_, lean_object* v_a_3980_){
_start:
{
uint8_t v___x_3981_; 
v___x_3981_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___redArg(v_m_3979_, v_a_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b2_3982_, lean_object* v_m_3983_, lean_object* v_a_3984_){
_start:
{
uint8_t v_res_3985_; lean_object* v_r_3986_; 
v_res_3985_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5(v_00_u03b2_3982_, v_m_3983_, v_a_3984_);
lean_dec_ref(v_a_3984_);
lean_dec_ref(v_m_3983_);
v_r_3986_ = lean_box(v_res_3985_);
return v_r_3986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_3987_, lean_object* v_m_3988_, lean_object* v_a_3989_, lean_object* v_b_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_3988_, v_a_3989_, v_b_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15(lean_object* v_mvarId_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___redArg(v_mvarId_3992_, v___y_3993_, v___y_3999_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15___boxed(lean_object* v_mvarId_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__15(v_mvarId_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v_mvarId_4004_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(lean_object* v_mvarId_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_mvarId_4016_, v___y_4017_, v___y_4023_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___boxed(lean_object* v_mvarId_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(v_mvarId_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v_mvarId_4028_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10(lean_object* v_00_u03b2_4040_, lean_object* v_x_4041_, size_t v_x_4042_, size_t v_x_4043_, lean_object* v_x_4044_, lean_object* v_x_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___redArg(v_x_4041_, v_x_4042_, v_x_4043_, v_x_4044_, v_x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10___boxed(lean_object* v_00_u03b2_4047_, lean_object* v_x_4048_, lean_object* v_x_4049_, lean_object* v_x_4050_, lean_object* v_x_4051_, lean_object* v_x_4052_){
_start:
{
size_t v_x_96399__boxed_4053_; size_t v_x_96400__boxed_4054_; lean_object* v_res_4055_; 
v_x_96399__boxed_4053_ = lean_unbox_usize(v_x_4049_);
lean_dec(v_x_4049_);
v_x_96400__boxed_4054_ = lean_unbox_usize(v_x_4050_);
lean_dec(v_x_4050_);
v_res_4055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10(v_00_u03b2_4047_, v_x_4048_, v_x_96399__boxed_4053_, v_x_96400__boxed_4054_, v_x_4051_, v_x_4052_);
return v_res_4055_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_4056_, lean_object* v_a_4057_, lean_object* v_x_4058_){
_start:
{
uint8_t v___x_4059_; 
v___x_4059_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___redArg(v_a_4057_, v_x_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11___boxed(lean_object* v_00_u03b2_4060_, lean_object* v_a_4061_, lean_object* v_x_4062_){
_start:
{
uint8_t v_res_4063_; lean_object* v_r_4064_; 
v_res_4063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__5_spec__11(v_00_u03b2_4060_, v_a_4061_, v_x_4062_);
lean_dec(v_x_4062_);
lean_dec_ref(v_a_4061_);
v_r_4064_ = lean_box(v_res_4063_);
return v_r_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13(lean_object* v_00_u03b2_4065_, lean_object* v_data_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13___redArg(v_data_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19(lean_object* v_00_u03b2_4068_, lean_object* v_n_4069_, lean_object* v_k_4070_, lean_object* v_v_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19___redArg(v_n_4069_, v_k_4070_, v_v_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20(lean_object* v_00_u03b2_4073_, size_t v_depth_4074_, lean_object* v_keys_4075_, lean_object* v_vals_4076_, lean_object* v_heq_4077_, lean_object* v_i_4078_, lean_object* v_entries_4079_){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___redArg(v_depth_4074_, v_keys_4075_, v_vals_4076_, v_i_4078_, v_entries_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20___boxed(lean_object* v_00_u03b2_4081_, lean_object* v_depth_4082_, lean_object* v_keys_4083_, lean_object* v_vals_4084_, lean_object* v_heq_4085_, lean_object* v_i_4086_, lean_object* v_entries_4087_){
_start:
{
size_t v_depth_boxed_4088_; lean_object* v_res_4089_; 
v_depth_boxed_4088_ = lean_unbox_usize(v_depth_4082_);
lean_dec(v_depth_4082_);
v_res_4089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__20(v_00_u03b2_4081_, v_depth_boxed_4088_, v_keys_4083_, v_vals_4084_, v_heq_4085_, v_i_4086_, v_entries_4087_);
lean_dec_ref(v_vals_4084_);
lean_dec_ref(v_keys_4083_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_4090_, lean_object* v_i_4091_, lean_object* v_source_4092_, lean_object* v_target_4093_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15___redArg(v_i_4091_, v_source_4092_, v_target_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21(lean_object* v_00_u03b2_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_, lean_object* v_x_4098_, lean_object* v_x_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__10_spec__19_spec__21___redArg(v_x_4096_, v_x_4097_, v_x_4098_, v_x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20(lean_object* v_00_u03b2_4101_, lean_object* v_x_4102_, lean_object* v_x_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__13_spec__15_spec__20___redArg(v_x_4102_, v_x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_){
_start:
{
uint8_t v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = 1;
v___x_4116_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___x_4115_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_);
lean_dec(v_a_4125_);
lean_dec_ref(v_a_4124_);
lean_dec(v_a_4123_);
lean_dec_ref(v_a_4122_);
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4137_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed), 10, 0);
v___x_4141_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4137_, v___x_4138_, v___x_4139_, v___x_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(lean_object* v_a_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2));
v___x_4171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6));
v___x_4172_ = l_Lean_addBuiltinDeclarationRanges(v___x_4170_, v___x_4171_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(lean_object* v_x_4177_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(lean_object* v_x_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_4179_);
lean_dec(v_x_4179_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(lean_object* v_stx_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; uint8_t v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___x_4233_; uint8_t v___x_4234_; 
v___x_4233_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
lean_inc(v_stx_4192_);
v___x_4234_ = l_Lean_Syntax_isOfKind(v_stx_4192_, v___x_4233_);
if (v___x_4234_ == 0)
{
lean_object* v___x_4235_; 
lean_dec(v_stx_4192_);
v___x_4235_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4235_;
}
else
{
lean_object* v___x_4236_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; uint8_t v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; uint8_t v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; uint8_t v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; uint8_t v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v_tk_4363_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v_args_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___x_4423_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v_only_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v_unfold_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v_squeeze_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v___x_4236_ = lean_unsigned_to_nat(0u);
v_tk_4363_ = l_Lean_Syntax_getArg(v_stx_4192_, v___x_4236_);
v___x_4423_ = lean_unsigned_to_nat(1u);
v___x_4499_ = l_Lean_Syntax_getArg(v_stx_4192_, v___x_4423_);
v___x_4500_ = l_Lean_Syntax_isNone(v___x_4499_);
if (v___x_4500_ == 0)
{
uint8_t v___x_4501_; 
lean_inc(v___x_4499_);
v___x_4501_ = l_Lean_Syntax_matchesNull(v___x_4499_, v___x_4423_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; 
lean_dec(v___x_4499_);
lean_dec(v_tk_4363_);
lean_dec(v_stx_4192_);
v___x_4502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4502_;
}
else
{
lean_object* v_squeeze_4503_; lean_object* v___x_4504_; 
v_squeeze_4503_ = l_Lean_Syntax_getArg(v___x_4499_, v___x_4236_);
lean_dec(v___x_4499_);
v___x_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4504_, 0, v_squeeze_4503_);
v_squeeze_4482_ = v___x_4504_;
v___y_4483_ = v_a_4193_;
v___y_4484_ = v_a_4194_;
v___y_4485_ = v_a_4195_;
v___y_4486_ = v_a_4196_;
v___y_4487_ = v_a_4197_;
v___y_4488_ = v_a_4198_;
v___y_4489_ = v_a_4199_;
v___y_4490_ = v_a_4200_;
goto v___jp_4481_;
}
}
else
{
lean_object* v___x_4505_; 
lean_dec(v___x_4499_);
v___x_4505_ = lean_box(0);
v_squeeze_4482_ = v___x_4505_;
v___y_4483_ = v_a_4193_;
v___y_4484_ = v_a_4194_;
v___y_4485_ = v_a_4195_;
v___y_4486_ = v_a_4196_;
v___y_4487_ = v_a_4197_;
v___y_4488_ = v_a_4198_;
v___y_4489_ = v_a_4199_;
v___y_4490_ = v_a_4200_;
goto v___jp_4481_;
}
v___jp_4237_:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_inc_ref(v___y_4256_);
v___x_4260_ = l_Array_append___redArg(v___y_4256_, v___y_4259_);
lean_dec_ref(v___y_4259_);
lean_inc(v___y_4254_);
lean_inc(v___y_4248_);
v___x_4261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4261_, 0, v___y_4248_);
lean_ctor_set(v___x_4261_, 1, v___y_4254_);
lean_ctor_set(v___x_4261_, 2, v___x_4260_);
if (lean_obj_tag(v___y_4245_) == 1)
{
lean_object* v_val_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v_val_4262_ = lean_ctor_get(v___y_4245_, 0);
lean_inc(v_val_4262_);
lean_dec_ref_known(v___y_4245_, 1);
v___x_4263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
v___x_4264_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__0));
lean_inc_n(v___y_4248_, 4);
v___x_4265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___y_4248_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
lean_inc_ref(v___y_4256_);
v___x_4266_ = l_Array_append___redArg(v___y_4256_, v_val_4262_);
lean_dec(v_val_4262_);
lean_inc(v___y_4254_);
v___x_4267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4267_, 0, v___y_4248_);
lean_ctor_set(v___x_4267_, 1, v___y_4254_);
lean_ctor_set(v___x_4267_, 2, v___x_4266_);
v___x_4268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__1));
v___x_4269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___y_4248_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = l_Lean_Syntax_node3(v___y_4248_, v___x_4263_, v___x_4265_, v___x_4267_, v___x_4269_);
v___x_4271_ = l_Array_mkArray1___redArg(v___x_4270_);
v___y_4203_ = v___y_4238_;
v___y_4204_ = v___y_4239_;
v___y_4205_ = v___y_4240_;
v___y_4206_ = v___y_4241_;
v___y_4207_ = v___y_4242_;
v___y_4208_ = v___y_4243_;
v___y_4209_ = v___y_4244_;
v___y_4210_ = v___y_4246_;
v___y_4211_ = v___y_4247_;
v___y_4212_ = v___y_4248_;
v___y_4213_ = v___y_4249_;
v___y_4214_ = v___y_4250_;
v___y_4215_ = v___y_4251_;
v___y_4216_ = v___y_4252_;
v___y_4217_ = v___x_4261_;
v___y_4218_ = v___y_4253_;
v___y_4219_ = v___y_4254_;
v___y_4220_ = v___y_4255_;
v___y_4221_ = v___y_4256_;
v___y_4222_ = v___y_4257_;
v___y_4223_ = v___y_4258_;
v___y_4224_ = v___x_4271_;
goto v___jp_4202_;
}
else
{
lean_object* v___x_4272_; 
lean_dec(v___y_4245_);
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4203_ = v___y_4238_;
v___y_4204_ = v___y_4239_;
v___y_4205_ = v___y_4240_;
v___y_4206_ = v___y_4241_;
v___y_4207_ = v___y_4242_;
v___y_4208_ = v___y_4243_;
v___y_4209_ = v___y_4244_;
v___y_4210_ = v___y_4246_;
v___y_4211_ = v___y_4247_;
v___y_4212_ = v___y_4248_;
v___y_4213_ = v___y_4249_;
v___y_4214_ = v___y_4250_;
v___y_4215_ = v___y_4251_;
v___y_4216_ = v___y_4252_;
v___y_4217_ = v___x_4261_;
v___y_4218_ = v___y_4253_;
v___y_4219_ = v___y_4254_;
v___y_4220_ = v___y_4255_;
v___y_4221_ = v___y_4256_;
v___y_4222_ = v___y_4257_;
v___y_4223_ = v___y_4258_;
v___y_4224_ = v___x_4272_;
goto v___jp_4202_;
}
}
v___jp_4273_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
lean_inc_ref(v___y_4292_);
v___x_4296_ = l_Array_append___redArg(v___y_4292_, v___y_4295_);
lean_dec_ref(v___y_4295_);
lean_inc(v___y_4290_);
lean_inc(v___y_4284_);
v___x_4297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4297_, 0, v___y_4284_);
lean_ctor_set(v___x_4297_, 1, v___y_4290_);
lean_ctor_set(v___x_4297_, 2, v___x_4296_);
if (lean_obj_tag(v___y_4276_) == 1)
{
lean_object* v_val_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_val_4298_ = lean_ctor_get(v___y_4276_, 0);
lean_inc(v_val_4298_);
lean_dec_ref_known(v___y_4276_, 1);
v___x_4299_ = l_Lean_SourceInfo_fromRef(v_val_4298_, v___x_4234_);
lean_dec(v_val_4298_);
v___x_4300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__2));
v___x_4301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Array_mkArray1___redArg(v___x_4301_);
v___y_4238_ = v___y_4274_;
v___y_4239_ = v___y_4275_;
v___y_4240_ = v___y_4277_;
v___y_4241_ = v___x_4297_;
v___y_4242_ = v___y_4278_;
v___y_4243_ = v___y_4279_;
v___y_4244_ = v___y_4280_;
v___y_4245_ = v___y_4281_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___y_4284_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4288_;
v___y_4253_ = v___y_4289_;
v___y_4254_ = v___y_4290_;
v___y_4255_ = v___y_4291_;
v___y_4256_ = v___y_4292_;
v___y_4257_ = v___y_4293_;
v___y_4258_ = v___y_4294_;
v___y_4259_ = v___x_4302_;
goto v___jp_4237_;
}
else
{
lean_object* v___x_4303_; 
v___x_4303_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4276_);
lean_dec(v___y_4276_);
v___y_4238_ = v___y_4274_;
v___y_4239_ = v___y_4275_;
v___y_4240_ = v___y_4277_;
v___y_4241_ = v___x_4297_;
v___y_4242_ = v___y_4278_;
v___y_4243_ = v___y_4279_;
v___y_4244_ = v___y_4280_;
v___y_4245_ = v___y_4281_;
v___y_4246_ = v___y_4282_;
v___y_4247_ = v___y_4283_;
v___y_4248_ = v___y_4284_;
v___y_4249_ = v___y_4285_;
v___y_4250_ = v___y_4286_;
v___y_4251_ = v___y_4287_;
v___y_4252_ = v___y_4288_;
v___y_4253_ = v___y_4289_;
v___y_4254_ = v___y_4290_;
v___y_4255_ = v___y_4291_;
v___y_4256_ = v___y_4292_;
v___y_4257_ = v___y_4293_;
v___y_4258_ = v___y_4294_;
v___y_4259_ = v___x_4303_;
goto v___jp_4237_;
}
}
v___jp_4304_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
lean_inc_ref(v___y_4323_);
v___x_4326_ = l_Array_append___redArg(v___y_4323_, v___y_4325_);
lean_dec_ref(v___y_4325_);
lean_inc(v___y_4320_);
lean_inc(v___y_4314_);
v___x_4327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4327_, 0, v___y_4314_);
lean_ctor_set(v___x_4327_, 1, v___y_4320_);
lean_ctor_set(v___x_4327_, 2, v___x_4326_);
v___x_4328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6));
if (lean_obj_tag(v___y_4321_) == 0)
{
lean_object* v___x_4329_; 
v___x_4329_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___y_4274_ = v___y_4305_;
v___y_4275_ = v___y_4306_;
v___y_4276_ = v___y_4307_;
v___y_4277_ = v___y_4308_;
v___y_4278_ = v___y_4309_;
v___y_4279_ = v___y_4310_;
v___y_4280_ = v___x_4327_;
v___y_4281_ = v___y_4311_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___y_4313_;
v___y_4284_ = v___y_4314_;
v___y_4285_ = v___y_4315_;
v___y_4286_ = v___y_4316_;
v___y_4287_ = v___y_4317_;
v___y_4288_ = v___y_4318_;
v___y_4289_ = v___y_4319_;
v___y_4290_ = v___y_4320_;
v___y_4291_ = v___y_4322_;
v___y_4292_ = v___y_4323_;
v___y_4293_ = v___y_4324_;
v___y_4294_ = v___x_4328_;
v___y_4295_ = v___x_4329_;
goto v___jp_4273_;
}
else
{
lean_object* v_val_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v_val_4330_ = lean_ctor_get(v___y_4321_, 0);
lean_inc(v_val_4330_);
lean_dec_ref_known(v___y_4321_, 1);
v___x_4331_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0));
v___x_4332_ = lean_array_push(v___x_4331_, v_val_4330_);
v___y_4274_ = v___y_4305_;
v___y_4275_ = v___y_4306_;
v___y_4276_ = v___y_4307_;
v___y_4277_ = v___y_4308_;
v___y_4278_ = v___y_4309_;
v___y_4279_ = v___y_4310_;
v___y_4280_ = v___x_4327_;
v___y_4281_ = v___y_4311_;
v___y_4282_ = v___y_4312_;
v___y_4283_ = v___y_4313_;
v___y_4284_ = v___y_4314_;
v___y_4285_ = v___y_4315_;
v___y_4286_ = v___y_4316_;
v___y_4287_ = v___y_4317_;
v___y_4288_ = v___y_4318_;
v___y_4289_ = v___y_4319_;
v___y_4290_ = v___y_4320_;
v___y_4291_ = v___y_4322_;
v___y_4292_ = v___y_4323_;
v___y_4293_ = v___y_4324_;
v___y_4294_ = v___x_4328_;
v___y_4295_ = v___x_4332_;
goto v___jp_4273_;
}
}
v___jp_4333_:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
lean_inc_ref(v___y_4353_);
v___x_4355_ = l_Array_append___redArg(v___y_4353_, v___y_4354_);
lean_dec_ref(v___y_4354_);
lean_inc(v___y_4350_);
lean_inc(v___y_4343_);
v___x_4356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4356_, 0, v___y_4343_);
lean_ctor_set(v___x_4356_, 1, v___y_4350_);
lean_ctor_set(v___x_4356_, 2, v___x_4355_);
if (lean_obj_tag(v___y_4348_) == 1)
{
lean_object* v_val_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v_val_4357_ = lean_ctor_get(v___y_4348_, 0);
lean_inc(v_val_4357_);
lean_dec_ref_known(v___y_4348_, 1);
v___x_4358_ = l_Lean_SourceInfo_fromRef(v_val_4357_, v___x_4234_);
lean_dec(v_val_4357_);
v___x_4359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__9));
v___x_4360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set(v___x_4360_, 1, v___x_4359_);
v___x_4361_ = l_Array_mkArray1___redArg(v___x_4360_);
v___y_4305_ = v___y_4334_;
v___y_4306_ = v___y_4335_;
v___y_4307_ = v___y_4336_;
v___y_4308_ = v___y_4337_;
v___y_4309_ = v___y_4338_;
v___y_4310_ = v___y_4339_;
v___y_4311_ = v___y_4340_;
v___y_4312_ = v___y_4341_;
v___y_4313_ = v___y_4342_;
v___y_4314_ = v___y_4343_;
v___y_4315_ = v___y_4344_;
v___y_4316_ = v___y_4345_;
v___y_4317_ = v___y_4346_;
v___y_4318_ = v___y_4347_;
v___y_4319_ = v___y_4349_;
v___y_4320_ = v___y_4350_;
v___y_4321_ = v___y_4351_;
v___y_4322_ = v___y_4352_;
v___y_4323_ = v___y_4353_;
v___y_4324_ = v___x_4356_;
v___y_4325_ = v___x_4361_;
goto v___jp_4304_;
}
else
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4348_);
lean_dec(v___y_4348_);
v___y_4305_ = v___y_4334_;
v___y_4306_ = v___y_4335_;
v___y_4307_ = v___y_4336_;
v___y_4308_ = v___y_4337_;
v___y_4309_ = v___y_4338_;
v___y_4310_ = v___y_4339_;
v___y_4311_ = v___y_4340_;
v___y_4312_ = v___y_4341_;
v___y_4313_ = v___y_4342_;
v___y_4314_ = v___y_4343_;
v___y_4315_ = v___y_4344_;
v___y_4316_ = v___y_4345_;
v___y_4317_ = v___y_4346_;
v___y_4318_ = v___y_4347_;
v___y_4319_ = v___y_4349_;
v___y_4320_ = v___y_4350_;
v___y_4321_ = v___y_4351_;
v___y_4322_ = v___y_4352_;
v___y_4323_ = v___y_4353_;
v___y_4324_ = v___x_4356_;
v___y_4325_ = v___x_4362_;
goto v___jp_4304_;
}
}
v___jp_4364_:
{
lean_object* v_ref_4380_; uint8_t v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v_ref_4380_ = lean_ctor_get(v___y_4374_, 5);
v___x_4381_ = 0;
v___x_4382_ = l_Lean_SourceInfo_fromRef(v_ref_4380_, v___x_4381_);
v___x_4383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1));
v___x_4384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2));
v___x_4385_ = l_Lean_SourceInfo_fromRef(v_tk_4363_, v___x_4234_);
lean_dec(v_tk_4363_);
v___x_4386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
lean_ctor_set(v___x_4386_, 1, v___x_4383_);
v___x_4387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__5));
v___x_4388_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6, &l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6_once, _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___closed__6);
if (lean_obj_tag(v___y_4375_) == 1)
{
lean_object* v_val_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_val_4389_ = lean_ctor_get(v___y_4375_, 0);
lean_inc(v_val_4389_);
lean_dec_ref_known(v___y_4375_, 1);
v___x_4390_ = l_Lean_SourceInfo_fromRef(v_val_4389_, v___x_4234_);
lean_dec(v_val_4389_);
v___x_4391_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1));
v___x_4392_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4390_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = l_Array_mkArray1___redArg(v___x_4392_);
v___y_4334_ = v___y_4365_;
v___y_4335_ = v___y_4366_;
v___y_4336_ = v___y_4367_;
v___y_4337_ = v___y_4368_;
v___y_4338_ = v___y_4369_;
v___y_4339_ = v___x_4384_;
v___y_4340_ = v___y_4370_;
v___y_4341_ = v___y_4371_;
v___y_4342_ = v___x_4386_;
v___y_4343_ = v___x_4382_;
v___y_4344_ = v___y_4372_;
v___y_4345_ = v___y_4373_;
v___y_4346_ = v___x_4381_;
v___y_4347_ = v___y_4374_;
v___y_4348_ = v___y_4376_;
v___y_4349_ = v___y_4377_;
v___y_4350_ = v___x_4387_;
v___y_4351_ = v___y_4379_;
v___y_4352_ = v___y_4378_;
v___y_4353_ = v___x_4388_;
v___y_4354_ = v___x_4393_;
goto v___jp_4333_;
}
else
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_4375_);
lean_dec(v___y_4375_);
v___y_4334_ = v___y_4365_;
v___y_4335_ = v___y_4366_;
v___y_4336_ = v___y_4367_;
v___y_4337_ = v___y_4368_;
v___y_4338_ = v___y_4369_;
v___y_4339_ = v___x_4384_;
v___y_4340_ = v___y_4370_;
v___y_4341_ = v___y_4371_;
v___y_4342_ = v___x_4386_;
v___y_4343_ = v___x_4382_;
v___y_4344_ = v___y_4372_;
v___y_4345_ = v___y_4373_;
v___y_4346_ = v___x_4381_;
v___y_4347_ = v___y_4374_;
v___y_4348_ = v___y_4376_;
v___y_4349_ = v___y_4377_;
v___y_4350_ = v___x_4387_;
v___y_4351_ = v___y_4379_;
v___y_4352_ = v___y_4378_;
v___y_4353_ = v___x_4388_;
v___y_4354_ = v___x_4394_;
goto v___jp_4333_;
}
}
v___jp_4395_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4411_ = lean_unsigned_to_nat(5u);
v___x_4412_ = l_Lean_Syntax_getArg(v___y_4400_, v___x_4411_);
lean_dec(v___y_4400_);
v___x_4413_ = l_Lean_Syntax_getOptional_x3f(v___y_4401_);
lean_dec(v___y_4401_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v___x_4414_; 
v___x_4414_ = lean_box(0);
v___y_4365_ = v___y_4405_;
v___y_4366_ = v___x_4412_;
v___y_4367_ = v___y_4396_;
v___y_4368_ = v___y_4408_;
v___y_4369_ = v___y_4404_;
v___y_4370_ = v_args_4402_;
v___y_4371_ = v___y_4399_;
v___y_4372_ = v___y_4403_;
v___y_4373_ = v___y_4410_;
v___y_4374_ = v___y_4409_;
v___y_4375_ = v___y_4398_;
v___y_4376_ = v___y_4397_;
v___y_4377_ = v___y_4407_;
v___y_4378_ = v___y_4406_;
v___y_4379_ = v___x_4414_;
goto v___jp_4364_;
}
else
{
lean_object* v_val_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
v_val_4415_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4413_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_val_4415_);
lean_dec(v___x_4413_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_val_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
v___y_4365_ = v___y_4405_;
v___y_4366_ = v___x_4412_;
v___y_4367_ = v___y_4396_;
v___y_4368_ = v___y_4408_;
v___y_4369_ = v___y_4404_;
v___y_4370_ = v_args_4402_;
v___y_4371_ = v___y_4399_;
v___y_4372_ = v___y_4403_;
v___y_4373_ = v___y_4410_;
v___y_4374_ = v___y_4409_;
v___y_4375_ = v___y_4398_;
v___y_4376_ = v___y_4397_;
v___y_4377_ = v___y_4407_;
v___y_4378_ = v___y_4406_;
v___y_4379_ = v___x_4420_;
goto v___jp_4364_;
}
}
}
}
v___jp_4424_:
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4440_ = l_Lean_Syntax_getArg(v___y_4427_, v___y_4429_);
v___x_4441_ = l_Lean_Syntax_isNone(v___x_4440_);
if (v___x_4441_ == 0)
{
uint8_t v___x_4442_; 
lean_inc(v___x_4440_);
v___x_4442_ = l_Lean_Syntax_matchesNull(v___x_4440_, v___x_4423_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; 
lean_dec(v___x_4440_);
lean_dec(v_only_4431_);
lean_dec(v___y_4430_);
lean_dec(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec(v_tk_4363_);
v___x_4443_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4443_;
}
else
{
lean_object* v___x_4444_; lean_object* v___x_4445_; uint8_t v___x_4446_; 
v___x_4444_ = l_Lean_Syntax_getArg(v___x_4440_, v___x_4236_);
lean_dec(v___x_4440_);
v___x_4445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4));
lean_inc(v___x_4444_);
v___x_4446_ = l_Lean_Syntax_isOfKind(v___x_4444_, v___x_4445_);
if (v___x_4446_ == 0)
{
lean_object* v___x_4447_; 
lean_dec(v___x_4444_);
lean_dec(v_only_4431_);
lean_dec(v___y_4430_);
lean_dec(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec(v_tk_4363_);
v___x_4447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4447_;
}
else
{
lean_object* v___x_4448_; lean_object* v_args_4449_; lean_object* v___x_4450_; 
v___x_4448_ = l_Lean_Syntax_getArg(v___x_4444_, v___x_4423_);
lean_dec(v___x_4444_);
v_args_4449_ = l_Lean_Syntax_getArgs(v___x_4448_);
lean_dec(v___x_4448_);
v___x_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4450_, 0, v_args_4449_);
v___y_4396_ = v_only_4431_;
v___y_4397_ = v___y_4426_;
v___y_4398_ = v___y_4425_;
v___y_4399_ = v___y_4428_;
v___y_4400_ = v___y_4427_;
v___y_4401_ = v___y_4430_;
v_args_4402_ = v___x_4450_;
v___y_4403_ = v___y_4432_;
v___y_4404_ = v___y_4433_;
v___y_4405_ = v___y_4434_;
v___y_4406_ = v___y_4435_;
v___y_4407_ = v___y_4436_;
v___y_4408_ = v___y_4437_;
v___y_4409_ = v___y_4438_;
v___y_4410_ = v___y_4439_;
goto v___jp_4395_;
}
}
}
else
{
lean_object* v___x_4451_; 
lean_dec(v___x_4440_);
v___x_4451_ = lean_box(0);
v___y_4396_ = v_only_4431_;
v___y_4397_ = v___y_4426_;
v___y_4398_ = v___y_4425_;
v___y_4399_ = v___y_4428_;
v___y_4400_ = v___y_4427_;
v___y_4401_ = v___y_4430_;
v_args_4402_ = v___x_4451_;
v___y_4403_ = v___y_4432_;
v___y_4404_ = v___y_4433_;
v___y_4405_ = v___y_4434_;
v___y_4406_ = v___y_4435_;
v___y_4407_ = v___y_4436_;
v___y_4408_ = v___y_4437_;
v___y_4409_ = v___y_4438_;
v___y_4410_ = v___y_4439_;
goto v___jp_4395_;
}
}
v___jp_4452_:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; uint8_t v___x_4467_; 
v___x_4464_ = lean_unsigned_to_nat(3u);
v___x_4465_ = l_Lean_Syntax_getArg(v_stx_4192_, v___x_4464_);
lean_dec(v_stx_4192_);
v___x_4466_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2));
lean_inc(v___x_4465_);
v___x_4467_ = l_Lean_Syntax_isOfKind(v___x_4465_, v___x_4466_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; 
lean_dec(v___x_4465_);
lean_dec(v_unfold_4455_);
lean_dec(v___y_4453_);
lean_dec(v_tk_4363_);
v___x_4468_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4468_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4469_ = l_Lean_Syntax_getArg(v___x_4465_, v___x_4236_);
v___x_4470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8));
lean_inc(v___x_4469_);
v___x_4471_ = l_Lean_Syntax_isOfKind(v___x_4469_, v___x_4470_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; 
lean_dec(v___x_4469_);
lean_dec(v___x_4465_);
lean_dec(v_unfold_4455_);
lean_dec(v___y_4453_);
lean_dec(v_tk_4363_);
v___x_4472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4472_;
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; uint8_t v___x_4475_; 
v___x_4473_ = l_Lean_Syntax_getArg(v___x_4465_, v___x_4423_);
v___x_4474_ = l_Lean_Syntax_getArg(v___x_4465_, v___y_4454_);
v___x_4475_ = l_Lean_Syntax_isNone(v___x_4474_);
if (v___x_4475_ == 0)
{
uint8_t v___x_4476_; 
lean_inc(v___x_4474_);
v___x_4476_ = l_Lean_Syntax_matchesNull(v___x_4474_, v___x_4423_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; 
lean_dec(v___x_4474_);
lean_dec(v___x_4473_);
lean_dec(v___x_4469_);
lean_dec(v___x_4465_);
lean_dec(v_unfold_4455_);
lean_dec(v___y_4453_);
lean_dec(v_tk_4363_);
v___x_4477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4477_;
}
else
{
lean_object* v_only_4478_; lean_object* v___x_4479_; 
v_only_4478_ = l_Lean_Syntax_getArg(v___x_4474_, v___x_4236_);
lean_dec(v___x_4474_);
v___x_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4479_, 0, v_only_4478_);
v___y_4425_ = v___y_4453_;
v___y_4426_ = v_unfold_4455_;
v___y_4427_ = v___x_4465_;
v___y_4428_ = v___x_4469_;
v___y_4429_ = v___x_4464_;
v___y_4430_ = v___x_4473_;
v_only_4431_ = v___x_4479_;
v___y_4432_ = v___y_4456_;
v___y_4433_ = v___y_4457_;
v___y_4434_ = v___y_4458_;
v___y_4435_ = v___y_4459_;
v___y_4436_ = v___y_4460_;
v___y_4437_ = v___y_4461_;
v___y_4438_ = v___y_4462_;
v___y_4439_ = v___y_4463_;
goto v___jp_4424_;
}
}
else
{
lean_object* v___x_4480_; 
lean_dec(v___x_4474_);
v___x_4480_ = lean_box(0);
v___y_4425_ = v___y_4453_;
v___y_4426_ = v_unfold_4455_;
v___y_4427_ = v___x_4465_;
v___y_4428_ = v___x_4469_;
v___y_4429_ = v___x_4464_;
v___y_4430_ = v___x_4473_;
v_only_4431_ = v___x_4480_;
v___y_4432_ = v___y_4456_;
v___y_4433_ = v___y_4457_;
v___y_4434_ = v___y_4458_;
v___y_4435_ = v___y_4459_;
v___y_4436_ = v___y_4460_;
v___y_4437_ = v___y_4461_;
v___y_4438_ = v___y_4462_;
v___y_4439_ = v___y_4463_;
goto v___jp_4424_;
}
}
}
}
v___jp_4481_:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v___x_4491_ = lean_unsigned_to_nat(2u);
v___x_4492_ = l_Lean_Syntax_getArg(v_stx_4192_, v___x_4491_);
v___x_4493_ = l_Lean_Syntax_isNone(v___x_4492_);
if (v___x_4493_ == 0)
{
uint8_t v___x_4494_; 
lean_inc(v___x_4492_);
v___x_4494_ = l_Lean_Syntax_matchesNull(v___x_4492_, v___x_4423_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; 
lean_dec(v___x_4492_);
lean_dec(v_squeeze_4482_);
lean_dec(v_tk_4363_);
lean_dec(v_stx_4192_);
v___x_4495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
return v___x_4495_;
}
else
{
lean_object* v_unfold_4496_; lean_object* v___x_4497_; 
v_unfold_4496_ = l_Lean_Syntax_getArg(v___x_4492_, v___x_4236_);
lean_dec(v___x_4492_);
v___x_4497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4497_, 0, v_unfold_4496_);
v___y_4453_ = v_squeeze_4482_;
v___y_4454_ = v___x_4491_;
v_unfold_4455_ = v___x_4497_;
v___y_4456_ = v___y_4483_;
v___y_4457_ = v___y_4484_;
v___y_4458_ = v___y_4485_;
v___y_4459_ = v___y_4486_;
v___y_4460_ = v___y_4487_;
v___y_4461_ = v___y_4488_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
goto v___jp_4452_;
}
}
else
{
lean_object* v___x_4498_; 
lean_dec(v___x_4492_);
v___x_4498_ = lean_box(0);
v___y_4453_ = v_squeeze_4482_;
v___y_4454_ = v___x_4491_;
v_unfold_4455_ = v___x_4498_;
v___y_4456_ = v___y_4483_;
v___y_4457_ = v___y_4484_;
v___y_4458_ = v___y_4485_;
v___y_4459_ = v___y_4486_;
v___y_4460_ = v___y_4487_;
v___y_4461_ = v___y_4488_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
goto v___jp_4452_;
}
}
}
v___jp_4202_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
lean_inc_ref(v___y_4221_);
v___x_4225_ = l_Array_append___redArg(v___y_4221_, v___y_4224_);
lean_dec_ref(v___y_4224_);
lean_inc_n(v___y_4219_, 2);
lean_inc_n(v___y_4212_, 4);
v___x_4226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4226_, 0, v___y_4212_);
lean_ctor_set(v___x_4226_, 1, v___y_4219_);
lean_ctor_set(v___x_4226_, 2, v___x_4225_);
v___x_4227_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__7___closed__5));
v___x_4228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___y_4212_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = l_Lean_Syntax_node2(v___y_4212_, v___y_4219_, v___x_4228_, v___y_4204_);
lean_inc(v___y_4223_);
v___x_4230_ = l_Lean_Syntax_node5(v___y_4212_, v___y_4223_, v___y_4210_, v___y_4206_, v___y_4217_, v___x_4226_, v___x_4229_);
lean_inc(v___y_4208_);
v___x_4231_ = l_Lean_Syntax_node4(v___y_4212_, v___y_4208_, v___y_4211_, v___y_4222_, v___y_4209_, v___x_4230_);
v___x_4232_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(v___y_4215_, v___x_4231_, v___y_4213_, v___y_4207_, v___y_4203_, v___y_4220_, v___y_4218_, v___y_4205_, v___y_4216_, v___y_4214_);
return v___x_4232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(lean_object* v_stx_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(v_stx_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1(){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4525_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4526_ = ((lean_object*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0));
v___x_4527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1));
v___x_4528_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed), 10, 0);
v___x_4529_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4525_, v___x_4526_, v___x_4527_, v___x_4528_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(lean_object* v_a_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
return v_res_4531_;
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
